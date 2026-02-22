/**
 * Fresh eigenvariable generation for quantifier instantiation.
 * Uses content-addressed evar(N) nodes with monotonic BigInt counter.
 */

const Store = require('./store');

let _next = 0n;

function freshEvar() {
  const h = Store.put('evar', [_next]);
  _next += 1n;
  return h;
}

function resetFresh(val = 0n) { _next = val; }

function getFreshCounter() { return _next; }

module.exports = { freshEvar, resetFresh, getFreshCounter };
