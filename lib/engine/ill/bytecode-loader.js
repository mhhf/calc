/**
 * Bytecode Loader — hex string → grade-0 arr_get facts for compile-time specialization.
 *
 * Phase C of TODO_0160: converts contract bytecode into persistent grade-0 facts
 * that feed into multi-stage composition (Stage 3: arr_get specialization).
 *
 * Input: hex bytecode string (e.g., "6040600052...")
 * Output: { arrayHash, facts, entryPoints }
 *   - arrayHash: content-addressed arrlit hash of semantic bytecode
 *   - facts: Map<predHead, [{name, hash}]> compatible with composeGrade0's grade0Facts
 *   - entryPoints: Set<number> of reachable PC positions (PC=0 + JUMPDESTs)
 */

'use strict';

const Store = require('../../kernel/store');
const { intToBin } = require('./ffi/convert');

/**
 * Load bytecode hex string into grade-0 arr_get facts.
 *
 * @param {string} hex - Hex bytecode string (no 0x prefix)
 * @param {string} [arrayName='contract'] - Name for the bytecode array
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

  // Build semantic array
  const semantic = new Uint32Array(requiredLen);
  const zeroBinlit = intToBin(0n);

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
      // Fill remaining positions in this PUSH range with zero
      for (let j = 2; j <= n && pc + j < requiredLen; j++) {
        semantic[pc + j] = zeroBinlit;
      }
      pc += 1 + n;
    } else {
      pc++;
    }
  }

  const arrayHash = Store.putArray(semantic);
  const arrayTermHash = Store.put(arrayName, [arrayHash]);

  // ── Generate arr_get facts: arr_get(arrayName, PC, Value) ──
  const facts = [];
  for (let i = 0; i < semantic.length; i++) {
    const pcHash = intToBin(BigInt(i));
    const factHash = Store.put('arr_get', [arrayTermHash, pcHash, semantic[i]]);
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

  return { arrayHash: arrayTermHash, facts: factsMap, entryPoints };
}

module.exports = { loadBytecode };
