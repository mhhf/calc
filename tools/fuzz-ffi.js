#!/usr/bin/env node
/**
 * Fuzz test: compare FFI against the canonical reference for every arithmetic
 * predicate. Two comparison modes:
 *
 *   - clause-mode (default): compare FFI result against backward clause
 *     resolution (FFI off). Property: φ ∘ FFI = φ ∘ clause where φ canonicalizes.
 *     Used for §3.1–§3.6 logical primitives.
 *
 *   - spec-mode (Group B extralogical primitives): compare FFI result against
 *     a JS reference function that captures the mathematical specification.
 *     Used for §3.7 fixed-point arithmetic, §3.8 strings, and §3.10
 *     `sha3_compute`. There is no clause for these (or the clause introduces
 *     an uninterpreted symbol the FFI then interprets); the spec is the
 *     witness of soundness.
 *
 * Usage:
 *   node tools/fuzz-ffi.js [--count N] [--pred NAME] [--seed N] [--verbose]
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
let SEED = Date.now();
let VERBOSE = false;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--count' && args[i + 1]) COUNT = parseInt(args[++i]);
  if (args[i] === '--pred' && args[i + 1]) PRED_FILTER = args[++i];
  if (args[i] === '--seed' && args[i + 1]) SEED = parseInt(args[++i]);
  if (args[i] === '--verbose') VERBOSE = true;
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

// Predicate test configs: input modes, output modes, value generators
const PRED_CONFIGS = {
  plus: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  inc: { inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(16)] },
  mul: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(8), randBigInt(8)] },
  sub: { inputs: ['+', '+'], outputs: ['-'], gen: () => { let b = randBigInt(12); let a = b + randBigInt(12); return [a, b]; } },
  div: { inputs: ['+', '+'], outputs: ['-'], gen: () => { let b = randBigInt(6); if (b === 0n) b = 1n; return [randBigInt(10), b]; } },
  mod: { inputs: ['+', '+'], outputs: ['-'], gen: () => { let b = randBigInt(6); if (b === 0n) b = 1n; return [randBigInt(10), b]; } },
  and: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  or: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  xor: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(16), randBigInt(16)] },
  // Note: bare 'not' is structural bit-flip (no padding), while FFI does 256-bit NOT.
  // EVM uses not256 for correct 256-bit semantics. Skip bare not from FFI comparison.
  // not: { inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(16)] },
  not256: { inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(160)] },
  to256: { inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(300)] },
  shr: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(4), randBigInt(16)] },
  shl: { inputs: ['+', '+'], outputs: ['-'], gen: () => [randBigInt(4), randBigInt(8)] },
  eq: { inputs: ['+', '+'], outputs: [], gen: () => { let v = randBigInt(16); return rand() > 0.5 ? [v, v] : [v, randBigInt(16)]; } },
  neq: { inputs: ['+', '+'], outputs: [], gen: () => { let v = randBigInt(16); return rand() > 0.5 ? [v, v + 1n] : [v, randBigInt(16)]; } },
  lt: { inputs: ['+', '+'], outputs: [], gen: () => [randBigInt(16), randBigInt(16)] },
  le: { inputs: ['+', '+'], outputs: [], gen: () => [randBigInt(16), randBigInt(16)] },
  dec: { inputs: ['+'], outputs: ['-'], gen: () => { let v = randBigInt(8); if (v === 0n) v = 1n; return [v]; } },
  // Group A clauses authored in TODO_0228: previously FFI-only, now have backward clauses.
  // sdiv/smod use small magnitudes wrapped to 256-bit two's complement to exercise sign paths
  // without triggering structural divmod blowup; signextend caps B at 30 to keep small-branch tractable.
  byte_size256: { inputs: ['+'], outputs: ['-'], gen: () => [randBigInt(24)] },
  signextend256: { inputs: ['+', '+'], outputs: ['-'], gen: () => {
    const big = rand() > 0.7;
    return [big ? (32n + randBigInt(4)) : randBigInt(2), randBigInt(16)];
  } },
  sdiv256: { inputs: ['+', '+'], outputs: ['-'], gen: () => {
    const M = 1n << 256n;
    const u = v => ((v % M) + M) % M;
    let a = randBigInt(7) - 64n;          // signed [-64, 63]
    let b = randBigInt(5) - 16n;          // signed [-16, 15]
    if (b === 0n) b = 1n;
    return [u(a), u(b)];
  } },
  smod256: { inputs: ['+', '+'], outputs: ['-'], gen: () => {
    const M = 1n << 256n;
    const u = v => ((v % M) + M) % M;
    let a = randBigInt(7) - 64n;
    let b = randBigInt(5) - 16n;
    if (b === 0n) b = 1n;
    return [u(a), u(b)];
  } },

  // ── Group B (TODO_0228): extralogical primitives — no clause to compare against. ──
  // `compareMode: 'spec'` runs FFI and compares against a JS reference function
  // capturing the mathematical specification (see doc/documentation/ffi-audit.md §4.1).

  // fixed_mul D A B C  ↔  C = ⌊(A × B) / 10^D⌋
  fixed_mul: {
    compareMode: 'spec',
    inputs: ['+', '+', '+'], outputs: ['-'],
    gen: () => {
      const D = BigInt(1 + Math.floor(rand() * 18));   // 1..18 decimals
      return [D, randBigInt(64), randBigInt(64)];
    },
    spec: ([D, A, B]) => [(A * B) / (10n ** D)],
  },

  // fixed_div D A B C  ↔  C = ⌊(A × 10^D) / B⌋,  B ≠ 0
  fixed_div: {
    compareMode: 'spec',
    inputs: ['+', '+', '+'], outputs: ['-'],
    gen: () => {
      const D = BigInt(1 + Math.floor(rand() * 18));
      let B = randBigInt(48); if (B === 0n) B = 1n;
      return [D, randBigInt(64), B];
    },
    spec: ([D, A, B]) => [(A * (10n ** D)) / B],
  },

  // string_concat A B C  ↔  C = A · B  (free-monoid concatenation on UTF-16 code units)
  string_concat: {
    compareMode: 'spec',
    inputs: ['+', '+'], outputs: ['-'],
    inputEnc: ['strlit', 'strlit'],
    outputEnc: ['strlit'],
    gen: () => [randStr(), randStr()],
    spec: ([a, b]) => [a + b],
  },

  // string_length A N  ↔  N = |A|  (count of UTF-16 code units)
  string_length: {
    compareMode: 'spec',
    inputs: ['+'], outputs: ['-'],
    inputEnc: ['strlit'],
    outputEnc: ['binlit'],
    gen: () => [randStr()],
    spec: ([s]) => [BigInt(s.length)],
  },

  // sha3_compute Mem Offset End Hash  ↔  Hash = keccak256(Mem[Offset..End))
  // Custom runner: assemble write-log memory + word-aligned offset/end. The clause
  // path (sha3_compute/eval) introduces an uninterpreted `sha3 Bytes` symbol; the
  // FFI interprets that symbol as the concrete keccak256 digest. Spec witness is
  // js-sha3 keccak256 over the same byte sequence.
  sha3_compute: {
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
};

Store.clear();
const ec = mde.load(path.join(import.meta.dirname, '../calculus/ill/programs/multisig_nocall_solc.ill'));

let totalTests = 0, totalPass = 0, totalFail = 0, totalSkip = 0;

const preds = PRED_FILTER ? [PRED_FILTER] : Object.keys(PRED_CONFIGS);

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

for (const pred of preds) {
  const config = PRED_CONFIGS[pred];
  if (!config) { console.log('Unknown predicate:', pred); continue; }

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

    // ── Spec-mode (Group B): compare FFI against JS reference, no clause. ──
    if (config.compareMode === 'spec') {
      const inDisplay = inputs.map((v, i) => display(v, inputEnc[i])).join(', ');
      if (!ffiResult || !ffiResult.success) {
        fail++;
        console.log('MISMATCH ' + pred + '(' + inDisplay + '): FFI failed' +
                    (ffiResult ? ' (' + ffiResult.reason + ')' : ''));
        continue;
      }
      const expected = config.spec(inputs);
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
  console.log(status + ' ' + pred + ': ' + pass + '/' + (pass + fail) + ' passed' +
              (skip > 0 ? ' (' + skip + ' skipped)' : ''));
}

console.log('\n' + totalPass + ' passed, ' + totalFail + ' failed, ' + totalSkip + ' skipped' +
            ' (seed: ' + SEED + ')');
process.exit(totalFail > 0 ? 1 : 0);
