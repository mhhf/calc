/**
 * Compile-time residual resolver for persistent goals.
 *
 * After grade-0 specialization, rules may still have persistent goals like
 * !inc(0x5, ?Y) where inputs are ground but outputs are metavars. This
 * resolver computes those outputs at compile time, grounding consequent
 * variables and enabling basic block fusion.
 *
 * Arithmetic predicates delegate to arith-core.js (shared with FFI).
 * Array access (arr_get, arr_set) stays here (Store-dependent, trie-divergent).
 */

'use strict';

const Store = require('../../kernel/store');
const { predHead } = require('../../kernel/ast');
const { binToInt, intToBin } = require('./ffi/convert');
const { computeArith } = require('./ffi/arith-core');

// Predicate → { arity, inputs } for arith-core delegation.
// inputs = number of leading children that are input positions.
const _ARITH_PREDS = {
  inc:         { arity: 2, inputs: 1 },
  plus:        { arity: 3, inputs: 2 },
  checked_sub: { arity: 3, inputs: 2 },
  gt:          { arity: 4, inputs: 3 },
  add_mod:     { arity: 4, inputs: 3 },
  mul_mod:     { arity: 4, inputs: 3 },
  div:         { arity: 3, inputs: 2 },
  mod:         { arity: 3, inputs: 2 },
  cd_read:     { arity: 3, inputs: 2 },
};

/**
 * Attempt to resolve a persistent goal at compile time.
 * @param {number} goalHash - persistent goal hash (e.g., inc(0x5, ?Y))
 * @returns {number|null} resolved fact hash with all positions ground, or null
 */
function residualResolver(goalHash) {
  const pred = predHead(goalHash);
  if (!pred) return null;
  const arity = Store.arity(goalHash);

  // Arithmetic predicates → delegate to arith-core
  const config = _ARITH_PREDS[pred];
  if (config) {
    if (arity !== config.arity) return null;
    const hashes = [];
    const bigints = [];
    for (let i = 0; i < config.inputs; i++) {
      const h = Store.child(goalHash, i);
      if (!_isGroundArg(h)) return null;
      const v = binToInt(h);
      if (v === null) return null;
      hashes.push(h);
      bigints.push(v);
    }
    const result = computeArith(pred, bigints);
    if (result === null) return null;
    hashes.push(intToBin(result));
    return Store.put(pred, hashes);
  }

  switch (pred) {
    // arr_get(+, +, -): V = Array[Index] — arrlit only at compile time
    case 'arr_get': {
      if (arity !== 3) return null;
      const arr = Store.child(goalHash, 0);
      const idx = Store.child(goalHash, 1);
      if (!_isGroundArg(arr) || !_isGroundArg(idx)) return null;
      const idxInt = binToInt(idx);
      if (idxInt === null || idxInt < 0n) return null;
      const elems = Store.getArrayElements(arr);
      if (!elems) return null;
      if (idxInt >= BigInt(elems.length)) return null;
      return Store.put('arr_get', [arr, idx, elems[Number(idxInt)]]);
    }

    // arr_set(+, +, +, -): Result = Array[Index := Value] — arrlit only
    case 'arr_set': {
      if (arity !== 4) return null;
      const arr = Store.child(goalHash, 0);
      const idx = Store.child(goalHash, 1);
      const val = Store.child(goalHash, 2);
      if (!_isGroundArg(arr) || !_isGroundArg(idx) || !_isGroundArg(val)) return null;
      const idxInt = binToInt(idx);
      if (idxInt === null || idxInt < 0n) return null;
      const elems = Store.getArrayElements(arr);
      if (!elems) return null;
      if (idxInt >= BigInt(elems.length)) return null;
      const newData = new Uint32Array(elems.length);
      newData.set(elems);
      newData[Number(idxInt)] = val;
      const newArr = Store.put('arrlit', [newData]);
      return Store.put('arr_set', [arr, idx, val, newArr]);
    }

    default:
      return null;
  }
}

/** Check if an argument is ground (not a metavar) */
function _isGroundArg(h) {
  return typeof h === 'number' && Store.tag(h) !== 'metavar';
}

module.exports = { residualResolver };
