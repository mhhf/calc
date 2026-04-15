/**
 * Bytecode Loader — hex string → grade-0 arr_get facts for compile-time specialization.
 *
 * Phase C of TODO_0160: converts contract bytecode into persistent grade-0 facts
 * that feed into multi-stage composition (Stage 3: arr_get specialization).
 *
 * Input: hex bytecode string (e.g., "6040600052...")
 * Output: { arrayHash, facts, entryPoints }
 *   - arrayHash: content-addressed raw arrlit hash of semantic bytecode
 *   - facts: Map<predHead, [{name, hash}]> compatible with compose0's grade0Facts
 *   - entryPoints: Set<number> of reachable PC positions (PC=0 + JUMPDESTs)
 */

'use strict';

const Store = require('../../kernel/store');
const { intToBin } = require('./ffi/convert');

/**
 * Load bytecode hex string into grade-0 arr_get facts.
 *
 * @param {string} hex - Hex bytecode string (no 0x prefix)
 * @param {string} [arrayName='contract'] - Label for fact naming (cosmetic)
 * @returns {{ arrayHash: number, facts: Map, entryPoints: Set<number> }}
 */
function loadBytecode(hex, arrayName = 'contract') {
  if (hex.startsWith('0x') || hex.startsWith('0X')) hex = hex.slice(2);
  if (hex.length % 2 !== 0) throw new Error('Odd-length hex string');

  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }

  // ── Semantic bytecode: group PUSH data bytes into single values ──
  // Pre-scan for required array length
  let requiredLen = bytes.length;
  {
    let pc = 0;
    while (pc < bytes.length) {
      const op = bytes[pc];
      if (op >= 0x60 && op <= 0x7f) {
        const n = op - 0x5f;
        const nextPc = pc + 1 + n;
        if (nextPc >= bytes.length) {
          const needed = nextPc + 1;
          if (needed > requiredLen) requiredLen = needed;
        }
        pc = nextPc;
      } else {
        pc++;
      }
    }
  }

  // Build semantic array + track PUSH data filler positions to skip
  const semantic = new Uint32Array(requiredLen);
  const zeroBinlit = intToBin(0n);
  const isFillerPosition = new Uint8Array(requiredLen); // 1 = unreachable PUSH data filler

  // Fill with zeroBinlit (for trailing positions)
  for (let i = 0; i < requiredLen; i++) semantic[i] = zeroBinlit;

  let pc = 0;
  while (pc < bytes.length) {
    const op = bytes[pc];
    semantic[pc] = intToBin(BigInt(op));

    if (op >= 0x60 && op <= 0x7f) {
      const n = op - 0x5f;
      // Combine next n bytes into big-endian value
      let combined = 0n;
      const available = Math.min(n, bytes.length - (pc + 1));
      for (let j = 0; j < available; j++) {
        combined = (combined << 8n) | BigInt(bytes[pc + 1 + j]);
      }
      combined <<= BigInt((n - available) * 8); // pad missing bytes with 0
      semantic[pc + 1] = intToBin(combined);
      // ALL PUSH data positions are fillers — unreachable as instruction starts.
      // Generating arr_get facts for these creates phantom specialized rules
      // (e.g., data byte 0x01 → phantom ADD rule) that pollute fusion's
      // producer/consumer map. PUSH data access is resolved by residual resolution.
      for (let j = 1; j <= n && pc + j < requiredLen; j++) {
        isFillerPosition[pc + j] = 1;
      }
      pc += 1 + n;
    } else {
      pc++;
    }
  }

  const arrayHash = Store.putArray(semantic);

  // ── Generate arr_get facts: arr_get(arrlit, PC, Value) ──
  // Uses raw arrlit hash (not wrapped) so remaining arr_get goals
  // at runtime can be resolved by FFI's O(1) arrlit path.
  // Skip PUSH data filler positions — they'd create unreachable phantom rules.
  const facts = [];
  for (let i = 0; i < semantic.length; i++) {
    if (isFillerPosition[i]) continue;
    const pcHash = intToBin(BigInt(i));
    const factHash = Store.put('arr_get', [arrayHash, pcHash, semantic[i]]);
    facts.push({
      name: `arr_get/${arrayName}:${i}`,
      hash: factHash,
    });
  }

  const factsMap = new Map();
  factsMap.set('arr_get', facts);

  // ── Entry point detection: PC=0 + JUMPDESTs (0x5B) ──
  const entryPoints = new Set();
  entryPoints.add(0); // PC=0 always reachable
  pc = 0;
  while (pc < bytes.length) {
    const op = bytes[pc];
    if (op === 0x5b) { // JUMPDEST
      entryPoints.add(pc);
    }
    // Skip PUSH data bytes
    if (op >= 0x60 && op <= 0x7f) {
      pc += 1 + (op - 0x5f);
    } else {
      pc++;
    }
  }

  return { arrayHash, facts: factsMap, entryPoints };
}

/**
 * Scoping guard for arr_get specialization.
 * Only allows specialization when the arr_get goal's arg₁ (array identifier)
 * matches arg₀ of a `bytecode` linear resource in the same rule.
 * Prevents stack/memory arr_get goals from being specialized with bytecode facts.
 *
 * @param {Object} _rule - The rule being specialized (unused, kept for API)
 * @param {string} pred - Predicate being specialized
 * @param {number} goalHash - The persistent goal hash
 * @param {Object} ante - Flattened antecedent { linear, persistent, grade0 }
 * @returns {boolean} true if specialization should proceed
 */
function bytecodeArrGetGuard(_rule, pred, goalHash, ante) {
  if (pred !== 'arr_get') return true;
  const arg1 = Store.child(goalHash, 0);
  for (const pat of ante.linear) {
    if (Store.tag(pat) === 'bytecode' && Store.child(pat, 0) === arg1) {
      return true;
    }
  }
  return false;
}

module.exports = { loadBytecode, bytecodeArrGetGuard };
