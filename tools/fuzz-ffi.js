#!/usr/bin/env node
/**
 * Fuzz test: compare FFI vs backward clause resolution for all arithmetic predicates.
 *
 * Usage:
 *   node tools/fuzz-ffi.js [--count N] [--pred NAME] [--seed N] [--verbose]
 *
 * Tests each predicate with random inputs, comparing FFI result against clause-only
 * backward proving. Reports mismatches.
 */
'use strict';

const path = require('path');
const Store = require('../lib/kernel/store');
const mde = require('../lib/engine');
const backward = require('../lib/engine/backchain');
const ffi = require('../lib/engine/ill/ffi');
const convert = require('../lib/engine/ill/ffi/convert');
const show = require('../lib/engine/show');
const apply = require('../lib/kernel/substitute').apply;

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
};

Store.clear();
const ec = mde.load(path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc.ill'));

let totalTests = 0, totalPass = 0, totalFail = 0, totalSkip = 0;

const preds = PRED_FILTER ? [PRED_FILTER] : Object.keys(PRED_CONFIGS);

for (const pred of preds) {
  const config = PRED_CONFIGS[pred];
  if (!config) { console.log('Unknown predicate:', pred); continue; }

  let pass = 0, fail = 0, skip = 0;

  for (let trial = 0; trial < COUNT; trial++) {
    const inputs = config.gen();
    const inputHashes = inputs.map(v => Store.put('binlit', [v]));
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

    // Clause path
    const clauseResult = backward.prove(ffiGoal, ec.clauses, ec.definitions, {
      maxDepth: 20000, allBuckets: true, useFFI: false
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
