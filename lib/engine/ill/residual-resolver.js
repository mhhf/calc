/**
 * Compile-time residual resolver for persistent goals.
 *
 * After grade-0 specialization, rules may still have persistent goals like
 * !inc(0x5, ?Y) where inputs are ground but outputs are metavars. This
 * resolver computes those outputs at compile time, grounding consequent
 * variables and enabling basic block fusion.
 *
 * Covers two categories:
 *   1. Arithmetic: inc, plus, checked_sub, gt, add_mod, mul_mod, div, mod
 *   2. Array access: arr_get, arr_set (on arrlit or trie-backed arrays)
 *
 * Each predicate mirrors its FFI implementation but returns a complete fact
 * hash (all positions filled) instead of a substitution.
 */

'use strict';

const Store = require('../../kernel/store');
const { getPredicateHead } = require('../../kernel/ast');
const { binToInt, intToBin } = require('./ffi/convert');

/**
 * Attempt to resolve a persistent goal at compile time.
 * @param {number} goalHash - persistent goal hash (e.g., inc(0x5, ?Y))
 * @returns {number|null} resolved fact hash with all positions ground, or null
 */
function residualResolver(goalHash) {
  const pred = getPredicateHead(goalHash);
  if (!pred) return null;
  const arity = Store.arity(goalHash);

  switch (pred) {
    // inc(+, -): Y = X + 1
    case 'inc': {
      if (arity !== 2) return null;
      const a = Store.child(goalHash, 0);
      if (!_isGroundArg(a)) return null;
      const aInt = binToInt(a);
      if (aInt === null) return null;
      return Store.put('inc', [a, intToBin(aInt + 1n)]);
    }

    // plus(+, +, -): C = A + B
    case 'plus': {
      if (arity !== 3) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      if (!_isGroundArg(a) || !_isGroundArg(b)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      if (aInt === null || bInt === null) return null;
      return Store.put('plus', [a, b, intToBin(aInt + bInt)]);
    }

    // checked_sub(+, +, -): C = A - B (only if A >= B)
    case 'checked_sub': {
      if (arity !== 3) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      if (!_isGroundArg(a) || !_isGroundArg(b)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      if (aInt === null || bInt === null) return null;
      if (aInt < bInt) return null; // Underflow → cannot resolve (execution would fail)
      return Store.put('checked_sub', [a, b, intToBin(aInt - bInt)]);
    }

    // gt(+, +, +, -): Z = A > B ? 1 : (A < B ? 0 : Carry)
    case 'gt': {
      if (arity !== 4) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      const carry = Store.child(goalHash, 2);
      if (!_isGroundArg(a) || !_isGroundArg(b) || !_isGroundArg(carry)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      const cInt = binToInt(carry);
      if (aInt === null || bInt === null || cInt === null) return null;
      const z = aInt > bInt ? 1n : (aInt < bInt ? 0n : cInt);
      return Store.put('gt', [a, b, carry, intToBin(z)]);
    }

    // add_mod(+, +, +, -): R = (A + B) mod N
    case 'add_mod': {
      if (arity !== 4) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      const n = Store.child(goalHash, 2);
      if (!_isGroundArg(a) || !_isGroundArg(b) || !_isGroundArg(n)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      const nInt = binToInt(n);
      if (aInt === null || bInt === null || nInt === null) return null;
      if (nInt === 0n) return null; // Division by zero
      return Store.put('add_mod', [a, b, n, intToBin((aInt + bInt) % nInt)]);
    }

    // mul_mod(+, +, +, -): R = (A * B) mod N
    case 'mul_mod': {
      if (arity !== 4) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      const n = Store.child(goalHash, 2);
      if (!_isGroundArg(a) || !_isGroundArg(b) || !_isGroundArg(n)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      const nInt = binToInt(n);
      if (aInt === null || bInt === null || nInt === null) return null;
      if (nInt === 0n) return null;
      return Store.put('mul_mod', [a, b, n, intToBin((aInt * bInt) % nInt)]);
    }

    // div(+, +, -): Q = A / B
    case 'div': {
      if (arity !== 3) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      if (!_isGroundArg(a) || !_isGroundArg(b)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      if (aInt === null || bInt === null || bInt === 0n) return null;
      return Store.put('div', [a, b, intToBin(aInt / bInt)]);
    }

    // mod(+, +, -): R = A % B
    case 'mod': {
      if (arity !== 3) return null;
      const a = Store.child(goalHash, 0);
      const b = Store.child(goalHash, 1);
      if (!_isGroundArg(a) || !_isGroundArg(b)) return null;
      const aInt = binToInt(a);
      const bInt = binToInt(b);
      if (aInt === null || bInt === null || bInt === 0n) return null;
      return Store.put('mod', [a, b, intToBin(aInt % bInt)]);
    }

    // arr_get(+, +, -): V = Array[Index]  — mirrors ffi/array.js arr_get
    case 'arr_get': {
      if (arity !== 3) return null;
      const arr = Store.child(goalHash, 0);
      const idx = Store.child(goalHash, 1);
      if (!_isGroundArg(arr) || !_isGroundArg(idx)) return null;
      const idxInt = binToInt(idx);
      if (idxInt === null || idxInt < 0n) return null;
      const elems = Store.getArrayElements(arr);
      if (!elems) return null; // trie not supported at compile time
      if (idxInt >= BigInt(elems.length)) return null;
      return Store.put('arr_get', [arr, idx, elems[Number(idxInt)]]);
    }

    // arr_set(+, +, +, -): Result = Array[Index := Value]  — mirrors ffi/array.js arr_set
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
