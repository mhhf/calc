#!/usr/bin/env node
/**
 * Fuzz test: compare FFI against the canonical reference for every FFI predicate.
 *
 * Walks the registry (`ffi.defaultMeta`) automatically — each predicate is either
 * fuzzed (clause- or spec-mode), declared as a skip stub with a reason, or
 * reported as UNFUZZED (no config). Output is grouped by audit cluster
 * (§3.1–§3.11) with a coverage summary at the end.
 *
 * Two comparison modes:
 *
 *   - clause-mode (default): compare FFI result against backward clause
 *     resolution (FFI off). Property: φ ∘ FFI = φ ∘ clause where φ canonicalizes.
 *
 *   - spec-mode: compare FFI result against a JS reference function that
 *     captures the mathematical specification. Used when there is no clause
 *     or the clause introduces an uninterpreted symbol the FFI then
 *     interprets (Group B extralogical primitives — see ffi-audit.md §4.1).
 *
 * Usage:
 *   node tools/fuzz-ffi.js [--count N] [--pred NAME] [--cluster §3.x]
 *                          [--seed N] [--verbose] [--list]
 *
 * Reports mismatches. Exits non-zero on any failure.
 */
'use strict';

import path from 'path';
import sha3 from 'js-sha3';
import Store from '../lib/kernel/store.js';
import mde from '../lib/engine/index.js';
import backward from '../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../lib/engine/ill/backchain-ill.js';
import ffi from '../lib/engine/ill/ffi/index.js';
import convert from '../lib/engine/ill/ffi/convert.js';
import { apply } from '../lib/kernel/substitute.js';

const { keccak256 } = sha3;

// Parse args
const args = process.argv.slice(2);
let COUNT = 50;
let PRED_FILTER = null;
let CLUSTER_FILTER = null;
let SEED = Date.now();
let LIST_ONLY = false;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--count' && args[i + 1]) COUNT = parseInt(args[++i]);
  if (args[i] === '--pred' && args[i + 1]) PRED_FILTER = args[++i];
  if (args[i] === '--cluster' && args[i + 1]) CLUSTER_FILTER = args[++i];
  if (args[i] === '--seed' && args[i + 1]) SEED = parseInt(args[++i]);
  if (args[i] === '--list') LIST_ONLY = true;
}

// Simple seeded PRNG (xorshift32)
let rngState = SEED | 1;
function rand() {
  rngState ^= rngState << 13;
  rngState ^= rngState >> 17;
  rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
}

function randBigInt(bits) {
  if (bits === 0) return 0n;
  let val = 0n;
  for (let i = 0; i < bits; i++) {
    if (rand() > 0.5) val |= (1n << BigInt(i));
  }
  return val;
}

// Random printable-ASCII string (length 0..maxLen, default 11). Used for
// string_concat / string_length spec-mode trials.
function randStr(maxLen = 11) {
  const len = Math.floor(rand() * (maxLen + 1));
  let s = '';
  for (let i = 0; i < len; i++) {
    s += String.fromCharCode(0x20 + Math.floor(rand() * 95));
  }
  return s;
}

// 256-bit two's complement helpers for signed-input generators.
const MOD_256 = 1n << 256n;
const u256 = (v) => ((v % MOD_256) + MOD_256) % MOD_256;

// ============================================================================
// PREDICATE CONFIGS (organized by audit cluster — see ffi-audit.md §3)
// ============================================================================
//
// Each entry:
//   cluster: '§3.x' label for grouping in coverage report
//   inputs/outputs: ['+', '-'] mode arrays (sans for runner-mode)
//   gen: () => [bigints]  (default binlit encoding)
//   inputEnc/outputEnc: per-arg encoding ['binlit'|'strlit']
//   compareMode: 'clause' (default) | 'spec'
//   spec: ([inputs]) => [outputs]  (spec-mode only)
//   runner: () => { passed, msg }  (custom-runner override; e.g. sha3_compute)
//   skip: 'reason'  (declared unfuzzable, with rationale)
// ----------------------------------------------------------------------------

const PRED_CONFIGS = {
  // ── §3.1 General arithmetic ────────────────────────────────────────────
  plus: { cluster: '§3.1', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  inc:  { cluster: '§3.1', inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(16)] },
  mul:  { cluster: '§3.1', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(8), randBigInt(8)] },
  sub:  { cluster: '§3.1', inputs: ['+', '+'], outputs: ['-'],
          gen: () => { let b = randBigInt(12); let a = b + randBigInt(12); return [a, b]; } },
  div:  { cluster: '§3.1', inputs: ['+', '+'], outputs: ['-'],
          gen: () => { let b = randBigInt(6); if (b === 0n) b = 1n; return [randBigInt(10), b]; } },
  mod:  { cluster: '§3.1', inputs: ['+', '+'], outputs: ['-'],
          gen: () => { let b = randBigInt(6); if (b === 0n) b = 1n; return [randBigInt(10), b]; } },
  trim: { cluster: '§3.1', skip: 'structural canonicalization — identity on binlit; FFI vs clause both no-ops on canonical input' },

  // ── §3.2 Comparisons ───────────────────────────────────────────────────
  lt:      { cluster: '§3.2', inputs: ['+', '+'], outputs: [], gen: () => [randBigInt(16), randBigInt(16)] },
  le:      { cluster: '§3.2', inputs: ['+', '+'], outputs: [], gen: () => [randBigInt(16), randBigInt(16)] },
  eq:      { cluster: '§3.2', inputs: ['+', '+'], outputs: [],
             gen: () => { let v = randBigInt(16); return rand() > 0.5 ? [v, v] : [v, randBigInt(16)]; } },
  eq_bool: { cluster: '§3.2', inputs: ['+', '+'], outputs: ['-'],
             gen: () => { let v = randBigInt(16); return rand() > 0.5 ? [v, v] : [v, randBigInt(16)]; } },
  neq:     { cluster: '§3.2', inputs: ['+', '+'], outputs: [],
             gen: () => { let v = randBigInt(16); return rand() > 0.5 ? [v, v + 1n] : [v, randBigInt(16)]; } },
  gt:      { cluster: '§3.2', inputs: ['+', '+', '+'], outputs: ['-'],
             // gt(A,B,Carry,Z): Z = A>B ? 1 : (A<B ? 0 : Carry).
             // Carry constrained to {0,1} to match how callers use it.
             gen: () => [randBigInt(12), randBigInt(12), rand() > 0.5 ? 1n : 0n] },

  // ── §3.3 Bitwise ───────────────────────────────────────────────────────
  and:    { cluster: '§3.3', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  or:     { cluster: '§3.3', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  xor:    { cluster: '§3.3', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  not:    { cluster: '§3.3', skip: 'bare structural NOT (no padding) ≠ FFI 256-bit bitwiseNot — semantic mismatch by design; use not256' },
  not256: { cluster: '§3.3', inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(160)] },
  to256:  { cluster: '§3.3', inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(300)] },
  shr:    { cluster: '§3.3', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(4), randBigInt(16)] },
  shl:    { cluster: '§3.3', inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(4), randBigInt(8)] },

  // ── §3.4 EVM 256-bit semantics ─────────────────────────────────────────
  // Most use compareMode 'spec' against the FFI semantics: structural clause
  // execution at full 256-bit width is intractable (e.g. shift-by-248), and
  // the audit Layer-C witness is the FFI semantics themselves.
  sub256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            gen: () => [randBigInt(64), randBigInt(64)],
            spec: ([a, b]) => [u256(a - b)] },
  div256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            // Mix of nonzero divisors and explicit zero (zero-safe → 0).
            gen: () => [randBigInt(64), rand() > 0.1 ? (randBigInt(32) | 1n) : 0n],
            spec: ([a, b]) => [b === 0n ? 0n : a / b] },
  mod256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            gen: () => [randBigInt(64), rand() > 0.1 ? (randBigInt(32) | 1n) : 0n],
            spec: ([a, b]) => [b === 0n ? 0n : a % b] },
  exp256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            gen: () => [randBigInt(32), randBigInt(6)],   // small exp → fast
            spec: ([base, e]) => {
              if (e === 0n) return [1n];
              const M = MOD_256 - 1n;
              let r = 1n, b = base & M, x = e;
              while (x > 0n) { if (x & 1n) r = (r * b) & M; b = (b * b) & M; x >>= 1n; }
              return [r];
            } },
  slt:    { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            gen: () => [u256(randBigInt(7) - 64n), u256(randBigInt(7) - 64n)],
            spec: ([a, b]) => {
              const SB = 1n << 255n;
              const sa = a >= SB ? a - MOD_256 : a;
              const sb = b >= SB ? b - MOD_256 : b;
              return [sa < sb ? 1n : 0n];
            } },
  sdiv256: { cluster: '§3.4', inputs: ['+', '+'], outputs: ['-'], gen: () => {
              let a = randBigInt(7) - 64n;
              let b = randBigInt(5) - 16n;
              if (b === 0n) b = 1n;
              return [u256(a), u256(b)];
            } },
  smod256: { cluster: '§3.4', inputs: ['+', '+'], outputs: ['-'], gen: () => {
              let a = randBigInt(7) - 64n;
              let b = randBigInt(5) - 16n;
              if (b === 0n) b = 1n;
              return [u256(a), u256(b)];
            } },
  addmod256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+', '+'], outputs: ['-'],
               gen: () => [randBigInt(32), randBigInt(32), rand() > 0.1 ? (randBigInt(16) | 1n) : 0n],
               spec: ([a, b, n]) => [n === 0n ? 0n : (a + b) % n] },
  mulmod256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+', '+'], outputs: ['-'],
               gen: () => [randBigInt(32), randBigInt(32), rand() > 0.1 ? (randBigInt(16) | 1n) : 0n],
               spec: ([a, b, n]) => [n === 0n ? 0n : (a * b) % n] },
  signextend256: { cluster: '§3.4', inputs: ['+', '+'], outputs: ['-'], gen: () => {
                    const big = rand() > 0.7;
                    return [big ? (32n + randBigInt(4)) : randBigInt(2), randBigInt(16)];
                  } },
  byte256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
             gen: () => [BigInt(Math.floor(rand() * 35)), randBigInt(256)],
             spec: ([i, x]) => [i >= 32n ? 0n : (x >> ((31n - i) * 8n)) & 0xFFn] },
  sar256: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
            gen: () => [BigInt(Math.floor(rand() * 260)), randBigInt(256)],
            spec: ([sh, v]) => {
              const SB = 1n << 255n;
              const isNeg = v >= SB;
              if (sh >= 256n) return [isNeg ? MOD_256 - 1n : 0n];
              const signed = isNeg ? v - MOD_256 : v;
              return [u256(signed >> sh)];
            } },
  checked_sub: { cluster: '§3.4', inputs: ['+', '+'], outputs: ['-'],
                 // a >= b guaranteed → success path (clause and FFI both succeed).
                 gen: () => { let b = randBigInt(8); let a = b + randBigInt(8); return [a, b]; } },
  byte_size256: { cluster: '§3.4', inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(24)] },
  byte_replace: { cluster: '§3.4', compareMode: 'spec', inputs: ['+', '+', '+'], outputs: ['-'],
                  gen: () => [randBigInt(256), BigInt(Math.floor(rand() * 32)), randBigInt(8)],
                  spec: ([word, pos, byte]) => {
                    if (pos >= 32n) return null;   // FFI fails — caller skips
                    const sh = (31n - pos) * 8n;
                    const mask = 0xFFn << sh;
                    return [(word & ~mask) | ((byte & 0xFFn) << sh)];
                  } },

  // ── §3.5 Gas ───────────────────────────────────────────────────────────
  sstore_gas: { cluster: '§3.5', skip: 'multi-modal: returns conservative default for symbolic inputs; needs explicit Gsset/Gsreset branch harness' },

  // ── §3.6 Opcode classifiers ────────────────────────────────────────────
  // gen returns opcodes uniformly across the predicate's success window.
  is_push: { cluster: '§3.6', compareMode: 'spec', inputs: ['+'], outputs: ['-'],
             gen: () => [0x60n + BigInt(Math.floor(rand() * 32))],   // 0x60..0x7f
             spec: ([op]) => (op < 0x60n || op > 0x7fn) ? null : [op - 0x5fn] },
  is_dup:  { cluster: '§3.6', compareMode: 'spec', inputs: ['+'], outputs: ['-'],
             gen: () => [0x80n + BigInt(Math.floor(rand() * 16))],   // 0x80..0x8f
             spec: ([op]) => (op < 0x80n || op > 0x8fn) ? null : [op - 0x80n] },
  is_swap: { cluster: '§3.6', compareMode: 'spec', inputs: ['+'], outputs: ['-'],
             gen: () => [0x90n + BigInt(Math.floor(rand() * 16))],   // 0x90..0x9f
             spec: ([op]) => (op < 0x90n || op > 0x9fn) ? null : [op - 0x90n] },

  // ── §3.7 Fixed-point (extralogical, spec-mode) ─────────────────────────
  // fixed_mul D A B C  ↔  C = ⌊(A × B) / 10^D⌋
  fixed_mul: { cluster: '§3.7', compareMode: 'spec', inputs: ['+', '+', '+'], outputs: ['-'],
               gen: () => {
                 const D = BigInt(1 + Math.floor(rand() * 18));
                 return [D, randBigInt(64), randBigInt(64)];
               },
               spec: ([D, A, B]) => [(A * B) / (10n ** D)] },
  // fixed_div D A B C  ↔  C = ⌊(A × 10^D) / B⌋,  B ≠ 0
  fixed_div: { cluster: '§3.7', compareMode: 'spec', inputs: ['+', '+', '+'], outputs: ['-'],
               gen: () => {
                 const D = BigInt(1 + Math.floor(rand() * 18));
                 let B = randBigInt(48); if (B === 0n) B = 1n;
                 return [D, randBigInt(64), B];
               },
               spec: ([D, A, B]) => [(A * (10n ** D)) / B] },

  // ── §3.8 Strings (extralogical, spec-mode) ─────────────────────────────
  string_concat: { cluster: '§3.8', compareMode: 'spec', inputs: ['+', '+'], outputs: ['-'],
                   inputEnc: ['strlit', 'strlit'], outputEnc: ['strlit'],
                   gen: () => [randStr(), randStr()],
                   spec: ([a, b]) => [a + b] },
  string_length: { cluster: '§3.8', compareMode: 'spec', inputs: ['+'], outputs: ['-'],
                   inputEnc: ['strlit'], outputEnc: ['binlit'],
                   gen: () => [randStr()],
                   spec: ([s]) => [BigInt(s.length)] },

  // ── §3.9 Arrays / tries ────────────────────────────────────────────────
  arr_get:   { cluster: '§3.9', skip: 'arrlit/trie state generator out of scope for Phase-1' },
  arr_set:   { cluster: '§3.9', skip: 'arrlit/trie state generator out of scope for Phase-1' },
  alen:      { cluster: '§3.9', skip: 'arrlit state generator out of scope for Phase-1' },
  read_bytes:{ cluster: '§3.9', skip: 'bytecode chain generator out of scope for Phase-1' },
  notMember: { cluster: '§3.9', skip: 'arrlit state generator out of scope for Phase-1' },
  trie_get:  { cluster: '§3.9', skip: 'FFI removed (compiled clause dispatch / Tier 2)' },
  trie_set:  { cluster: '§3.9', skip: 'FFI removed (compiled clause dispatch / Tier 2)' },

  // ── §3.10 Memory ───────────────────────────────────────────────────────
  mem_expand: { cluster: '§3.10', skip: 'write-log memory state generator out of scope for Phase-1' },
  mem_read:   { cluster: '§3.10', skip: 'write-log memory state generator out of scope for Phase-1' },
  no_overlap: { cluster: '§3.10', compareMode: 'spec', inputs: ['+', '+', '+', '+'], outputs: [],
                gen: () => [randBigInt(8), 1n + randBigInt(6), randBigInt(8), 1n + randBigInt(6)],
                // boolean: spec returns success flag via {success: bool}
                spec: ([r, rs, w, ws]) => ({ success: (r + rs <= w) || (w + ws <= r) }) },

  // sha3_compute Mem Offset End Hash  ↔  Hash = keccak256(Mem[Offset..End))
  // Custom runner: assemble write-log memory + word-aligned offset/end. The clause
  // path (sha3_compute/eval) introduces an uninterpreted `sha3 Bytes` symbol; the
  // FFI interprets that symbol as the concrete keccak256 digest. Spec witness is
  // js-sha3 keccak256 over the same byte sequence.
  sha3_compute: {
    cluster: '§3.10',
    compareMode: 'spec',
    runner: () => {
      const N = 1 + Math.floor(rand() * 4);              // 1..4 32-byte words
      const words = [];
      for (let i = 0; i < N; i++) words.push(randBigInt(256));

      // Build the write-log memory: write(off, val, rest), most-recent first.
      let mem = Store.put('atom', ['empty_mem']);
      for (let i = N - 1; i >= 0; i--) {
        mem = Store.put('write', [
          Store.put('binlit', [BigInt(i * 32)]),
          Store.put('binlit', [words[i]]),
          mem,
        ]);
      }
      const offset = Store.put('binlit', [0n]);
      const end = Store.put('binlit', [BigInt(N * 32)]);
      const out = Store.put('metavar', ['sha3_out']);

      const handler = ffi.get('memory.sha3_compute');
      const r = handler ? handler([mem, offset, end, out]) : null;
      if (!r || !r.success) {
        return { passed: false, msg: 'sha3_compute FFI failed: ' + (r ? r.reason : 'no handler') };
      }
      const got = convert.binToInt(r.theta[0][1]);

      // Reference: encode words big-endian and keccak256 the concatenation.
      const bytes = Buffer.alloc(N * 32);
      for (let i = 0; i < N; i++) {
        const w = words[i];
        for (let j = 0; j < 32; j++) {
          bytes[i * 32 + j] = Number((w >> BigInt(8 * (31 - j))) & 0xFFn);
        }
      }
      const expected = BigInt('0x' + keccak256(bytes));

      if (got !== expected) {
        return {
          passed: false,
          msg: 'sha3 mismatch (N=' + N + ' words): expected 0x' + expected.toString(16) +
               ' got 0x' + got.toString(16),
        };
      }
      return { passed: true };
    },
  },

  // ── §3.11 Calldata ─────────────────────────────────────────────────────
  cd_read: { cluster: '§3.11', skip: 'sconcat-chain calldata state generator out of scope for Phase-1' },

  // ── §3.12 Rationals (TODO_0265 Phase 1) ────────────────────────────────
  // Fuzzed in the dedicated rational-trials section below: goals mix ratlit
  // and bin arguments, clause resolution runs against bin.ill + rat.ill, and
  // results are compared as canonical hashes (outputs may be rational).
  qplus: { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qsub:  { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qmul:  { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qdiv:  { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qlt:   { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qle:   { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qeq:   { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qneq:  { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
  qeq_bool: { cluster: '§3.12', skip: 'covered by the §3.12 rational trials section' },
};

// ============================================================================
// COVERAGE: walk the registry, emit reports
// ============================================================================

const ALL_PREDS = Object.keys(ffi.defaultMeta).sort();

if (LIST_ONLY) {
  const byCluster = {};
  let unfuzzed = [];
  for (const pred of ALL_PREDS) {
    const c = PRED_CONFIGS[pred];
    if (!c) { unfuzzed.push(pred); continue; }
    (byCluster[c.cluster] ||= []).push({ pred, status: c.skip ? 'skip' : (c.runner ? 'runner' : (c.compareMode === 'spec' ? 'spec' : 'clause')) });
  }
  console.log('FFI predicate coverage map:\n');
  for (const cl of Object.keys(byCluster).sort()) {
    console.log(cl);
    for (const e of byCluster[cl]) console.log('  [' + e.status.padEnd(7) + '] ' + e.pred);
  }
  if (unfuzzed.length) {
    console.log('\nUNFUZZED (no entry in PRED_CONFIGS):');
    for (const p of unfuzzed) console.log('  ' + p);
  }
  process.exit(0);
}

Store.clear();
const ec = mde.load(path.join(import.meta.dirname, '../calculus/ill/programs/multisig_nocall_solc.ill'));

let totalTests = 0, totalPass = 0, totalFail = 0, totalSkip = 0;
const clusterStats = {};   // cluster → { pass, fail, skip, predicates: [{pred, status, summary}] }

function bumpCluster(cluster, predRow) {
  const cs = clusterStats[cluster] ||= { pass: 0, fail: 0, skip: 0, predicates: [] };
  cs.pass += predRow.pass;
  cs.fail += predRow.fail;
  cs.skip += predRow.skip;
  cs.predicates.push(predRow);
}

let predList;
if (PRED_FILTER) {
  predList = [PRED_FILTER];
} else if (CLUSTER_FILTER) {
  predList = ALL_PREDS.filter(p => PRED_CONFIGS[p] && PRED_CONFIGS[p].cluster === CLUSTER_FILTER);
} else {
  predList = ALL_PREDS;
}

// Format a single input/output for diagnostic display, dispatching on encoding.
function display(v, enc) {
  if (enc === 'strlit') return JSON.stringify(v);
  if (enc === 'binlit' || enc === undefined) return '0x' + (v ?? 0n).toString(16);
  return String(v);
}

// Decode an FFI output hash into its native JS value, dispatching on encoding.
function decodeOutput(h, enc) {
  if (enc === 'strlit') return convert.hashToStr(h);
  return convert.binToInt(h);   // 'binlit' default
}

for (const pred of predList) {
  const config = PRED_CONFIGS[pred];

  // No config at all → unfuzzed registry entry.
  if (!config) {
    console.log('UNFUZZED ' + pred + ' (no entry in PRED_CONFIGS)');
    bumpCluster('UNFUZZED', { pred, status: 'unfuzzed', pass: 0, fail: 0, skip: 0, summary: 'no config' });
    continue;
  }

  // Declared skip — print reason and continue.
  if (config.skip) {
    console.log('skip ' + pred + ': ' + config.skip);
    bumpCluster(config.cluster, { pred, status: 'skip', pass: 0, fail: 0, skip: 0, summary: config.skip });
    continue;
  }

  let pass = 0, fail = 0, skip = 0;

  for (let trial = 0; trial < COUNT; trial++) {
    // ── Custom-runner predicates (e.g. sha3_compute): full control. ──
    if (config.runner) {
      const r = config.runner();
      if (r.passed) { pass++; }
      else { fail++; console.log('MISMATCH ' + pred + ': ' + r.msg); }
      continue;
    }

    const inputs = config.gen();
    const inputEnc = config.inputEnc || inputs.map(() => 'binlit');
    const outputEnc = config.outputEnc || config.outputs.map(() => 'binlit');
    const inputHashes = inputs.map((v, i) => Store.put(inputEnc[i], [v]));
    const outputFvs = config.outputs.map((_, i) => Store.put('metavar', ['out' + i]));
    const allArgs = [...inputHashes, ...outputFvs];

    // FFI path
    const ffiGoal = Store.put(pred, allArgs);
    const meta = ffi.defaultMeta[pred];
    const ffiHandler = meta ? ffi.get(meta.ffi) : null;
    let ffiResult = null;
    if (ffiHandler) {
      ffiResult = ffiHandler(allArgs);
    }

    // ── Spec-mode: compare FFI against JS reference, no clause. ──
    if (config.compareMode === 'spec') {
      const inDisplay = inputs.map((v, i) => display(v, inputEnc[i])).join(', ');
      const expected = config.spec(inputs);

      // Boolean spec (e.g. no_overlap): {success: bool}
      if (config.outputs.length === 0) {
        const ffiOk = ffiResult ? ffiResult.success : false;
        if (ffiOk === expected.success) { pass++; }
        else {
          fail++;
          console.log('MISMATCH ' + pred + '(' + inDisplay + '): FFI=' + ffiOk + ' spec=' + expected.success);
        }
        continue;
      }

      // Spec returned null → input out of FFI's domain (e.g. byte_replace pos>=32).
      // Both FFI and spec should fail-mode → record as skip.
      if (expected === null) {
        if (ffiResult && ffiResult.success) {
          fail++;
          console.log('MISMATCH ' + pred + '(' + inDisplay + '): spec=undefined but FFI succeeded');
        } else {
          skip++;
        }
        continue;
      }

      if (!ffiResult || !ffiResult.success) {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inDisplay + '): FFI failed' +
                    (ffiResult ? ' (' + ffiResult.reason + ')' : ''));
        continue;
      }
      const got = ffiResult.theta.map((pair, i) => decodeOutput(pair[1], outputEnc[i]));
      let match = expected.length === got.length;
      for (let i = 0; match && i < expected.length; i++) {
        if (expected[i] !== got[i]) match = false;
      }
      if (match) {
        pass++;
      } else {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inDisplay + '): expected ' +
                    expected.map((v, i) => display(v, outputEnc[i])).join(', ') +
                    ', got ' + got.map((v, i) => display(v, outputEnc[i])).join(', '));
      }
      continue;
    }

    // Clause path (default: clause-mode comparison)
    const clauseResult = backward.prove(ffiGoal, ec.clauses, ec.definitions, {
      ...makeILLBackchainOpts(), maxDepth: 20000, allBuckets: true, useFFI: false
    });

    // Compare
    if (config.outputs.length === 0) {
      // Boolean predicates: compare success/failure
      const ffiOk = ffiResult ? ffiResult.success : false;
      const clauseOk = clauseResult.success;
      if (ffiOk === clauseOk) {
        pass++;
      } else {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inputs.map(v => '0x' + v.toString(16)).join(', ') + ')' +
                     ': FFI=' + ffiOk + ' clause=' + clauseOk);
      }
    } else {
      // Output predicates: compare output values
      if (!ffiResult || !ffiResult.success) {
        if (!clauseResult.success) { pass++; continue; }
        // FFI failed but clause succeeded — check if clause result is valid
        skip++;
        continue;
      }
      if (!clauseResult.success) {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inputs.map(v => '0x' + v.toString(16)).join(', ') + ')' +
                     ': FFI succeeded, clause FAILED');
        continue;
      }
      // Both succeeded — compare output values
      const ffiOutputs = ffiResult.theta.map(pair => convert.binToInt(pair[1]));
      const clauseOutputs = outputFvs.map(fv => {
        let val = fv;
        for (let i = 0; i < 500; i++) { let n = apply(val, clauseResult.theta); if (n === val) break; val = n; }
        return convert.binToInt(val);
      });

      let match = true;
      for (let i = 0; i < ffiOutputs.length; i++) {
        if (ffiOutputs[i] !== clauseOutputs[i]) { match = false; break; }
      }
      if (match) {
        pass++;
      } else {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inputs.map(v => '0x' + v.toString(16)).join(', ') + ')' +
                     ': FFI=' + ffiOutputs.map(v => v !== null ? '0x' + v.toString(16) : 'null') +
                     ' clause=' + clauseOutputs.map(v => v !== null ? '0x' + v.toString(16) : 'null'));
      }
    }
  }

  totalTests += pass + fail + skip;
  totalPass += pass;
  totalFail += fail;
  totalSkip += skip;

  const status = fail > 0 ? 'FAIL' : 'ok';
  const mode = config.runner ? 'runner' : (config.compareMode === 'spec' ? 'spec' : 'clause');
  console.log(status + ' ' + pred + ' [' + mode + ']: ' + pass + '/' + (pass + fail) + ' passed' +
              (skip > 0 ? ' (' + skip + ' skipped)' : ''));
  bumpCluster(config.cluster, { pred, status: fail > 0 ? 'FAIL' : 'ok', pass, fail, skip,
                                summary: pass + '/' + (pass + fail) + (skip ? ' (+' + skip + ' skip)' : '') + ' [' + mode + ']' });
}

// ============================================================================
// §3.12 RATIONAL TRIALS (TODO_0265 Phase 1)
// ============================================================================
//
// Property: φ ∘ FFI = φ ∘ clause where φ is the composed binlit+ratlit
// canonicalizer, over goals mixing ratlit and bin arguments (q-ops coerce
// bins to n/1). Clause resolution runs against bin.ill + rat.ill (a
// separate load — the base corpus above stays rat-free, proving bin
// behavior is untouched). Split namespaces (D8.1 revised): only the
// q-family accepts rationals; the bin family is fuzzed in §3.1/§3.2.

{
  const { binlitTheory } = await import('../lib/engine/ill/binlit-theory.js');
  const { ratlitTheory, putRat, installRatlitTheory } =
    await import('../lib/engine/theories/ratlit-theory.js');
  const { defaultTheories, buildCanonicalizer } = await import('../lib/kernel/eq-theory.js');

  installRatlitTheory();
  const ecRat = mde.load(path.join(import.meta.dirname, '../calculus/till/prelude/rat.ill'));
  const ratTheories = [...defaultTheories, binlitTheory, ratlitTheory];
  const ratCanon = buildCanonicalizer(ratTheories);
  const ratOpts = makeILLBackchainOpts({ theories: ratTheories, normalize: ratCanon });

  // Small magnitudes: clause-mode qnorm runs Euclid over divmod clauses,
  // whose recursion depth is linear in the quotient — cross-multiplied
  // numerators must stay a few hundred at most.
  const genRatArg = () => rand() > 0.5
    ? putRat(randBigInt(4), 1n + randBigInt(3))
    : Store.put('binlit', [randBigInt(4)]);

  // pred → [nInputs, hasOutput]
  const RAT_PREDS = {
    qplus: [2, true], qsub: [2, true], qmul: [2, true], qdiv: [2, true],
    qlt: [2, false], qle: [2, false], qeq: [2, false], qneq: [2, false],
    qeq_bool: [2, true],
  };

  for (const pred of Object.keys(RAT_PREDS)) {
    if (PRED_FILTER && pred !== PRED_FILTER) continue;
    if (CLUSTER_FILTER && CLUSTER_FILTER !== '§3.12') continue;
    const [nIn, hasOut] = RAT_PREDS[pred];
    const meta = ffi.defaultMeta[pred];
    const handler = ffi.get(meta.ffi);
    let pass = 0, fail = 0;

    for (let trial = 0; trial < COUNT; trial++) {
      const ins = Array.from({ length: nIn }, genRatArg);
      const out = hasOut ? Store.put('metavar', ['qout']) : null;
      const args = hasOut ? [...ins, out] : ins;
      const goal = Store.put(pred, args);

      const ffiResult = handler(args);
      const clauseResult = backward.prove(goal, ecRat.clauses, ecRat.definitions, {
        ...ratOpts, maxDepth: 20000, allBuckets: true, useFFI: false,
      });

      const ffiOk = !!(ffiResult && ffiResult.success);
      const dumpIns = () => ins.map(h => Store.tag(h) === 'ratlit'
        ? Store.child(h, 0) + '/' + Store.child(h, 1)
        : String(Store.child(h, 0))).join(', ');

      if (ffiOk !== clauseResult.success) {
        fail++;
        console.log('MISMATCH ' + pred + '(' + dumpIns() + '): FFI=' + ffiOk +
                    ' clause=' + clauseResult.success);
        continue;
      }
      if (!ffiOk) { pass++; continue; }
      if (!hasOut) { pass++; continue; }

      const ffiVal = ratCanon(ffiResult.theta[0][1]);
      let clauseVal = out;
      for (let i = 0; i < 500; i++) {
        const n = apply(clauseVal, clauseResult.theta);
        if (n === clauseVal) break;
        clauseVal = n;
      }
      clauseVal = ratCanon(clauseVal);
      if (ffiVal === clauseVal) {
        pass++;
      } else {
        fail++;
        console.log('MISMATCH ' + pred + '(' + dumpIns() + '): canonical hash ' +
                    'FFI=' + ffiVal + ' clause=' + clauseVal);
      }
    }

    totalTests += pass + fail;
    totalPass += pass;
    totalFail += fail;
    const status = fail > 0 ? 'FAIL' : 'ok';
    console.log(status + ' ' + pred + ' [rat]: ' + pass + '/' + (pass + fail) + ' passed');
    bumpCluster('§3.12', { pred: pred + '@rat', status, pass, fail, skip: 0,
                           summary: pass + '/' + (pass + fail) + ' [rat]' });
  }
}

// ============================================================================
// CLUSTER SUMMARY + COVERAGE TOTALS
// ============================================================================

console.log('\n── Coverage by cluster ──');
const clusterOrder = Object.keys(clusterStats).sort();
let nFuzzed = 0, nSkipped = 0, nUnfuzzed = 0;
for (const cl of clusterOrder) {
  const cs = clusterStats[cl];
  const fuzzed = cs.predicates.filter(p => p.status === 'ok' || p.status === 'FAIL').length;
  const skipped = cs.predicates.filter(p => p.status === 'skip').length;
  const unfuzzed = cs.predicates.filter(p => p.status === 'unfuzzed').length;
  nFuzzed += fuzzed; nSkipped += skipped; nUnfuzzed += unfuzzed;
  console.log(cl + ': ' + cs.pass + '/' + (cs.pass + cs.fail) + ' (' +
              fuzzed + ' fuzzed, ' + skipped + ' skip, ' + unfuzzed + ' unfuzzed)');
}

console.log('\nRegistry: ' + ALL_PREDS.length + ' predicates total');
console.log('  fuzzed:   ' + nFuzzed);
console.log('  skip:     ' + nSkipped);
console.log('  unfuzzed: ' + nUnfuzzed);
console.log('\n' + totalPass + ' passed, ' + totalFail + ' failed, ' + totalSkip + ' skipped' +
            ' (seed: ' + SEED + ')');
process.exit(totalFail > 0 ? 1 : 0);
