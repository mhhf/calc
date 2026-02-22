/**
 * Fresh variable generation for quantifier instantiation.
 *
 * Two kinds:
 *   freshEvar()    → evar(N) — runtime eigenvariable (symbolic witness)
 *   freshMetavar() → freevar('_mN') — compile/search-time metavar (unification slot)
 */

const Store = require('./store');

// Eigenvariable counter (BigInt, monotonic, forkable for parallel symexec)
let _evarNext = 0n;

function freshEvar() {
  const h = Store.put('evar', [_evarNext]);
  _evarNext += 1n;
  return h;
}

function resetFresh(val = 0n) { _evarNext = val; }

function getFreshCounter() { return _evarNext; }

// Metavar counter (compile-time binder opening + backward prover witness search)
let _metavarNext = 0;

function freshMetavar() {
  return Store.put('freevar', ['_m' + _metavarNext++]);
}

function resetMetavar(val = 0) { _metavarNext = val; }

module.exports = { freshEvar, resetFresh, getFreshCounter, freshMetavar, resetMetavar };
