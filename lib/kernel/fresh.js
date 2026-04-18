/**
 * Fresh variable generation for quantifier instantiation.
 *
 * Two kinds:
 *   freshEvar()    → evar(N) — runtime eigenvariable (symbolic witness)
 *   freshMetavar() → freevar('_mN') — compile/search-time metavar (unification slot)
 */

import Store from './store.js';
// Eigenvariable counter (BigInt, monotonic, forkable for parallel explore)
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
  return Store.put('metavar', ['m' + _metavarNext++]);
}

function resetMetavar(val = 0) { _metavarNext = val; }

// TODO_0218: reset metavar counter on Store.clear() so fresh metavar IDs are
// a deterministic function of parse order. Without this, two back-to-back
// loads of the same fixture produce different Store arenas (metavar IDs drift
// upward), breaking snapshot byte-equality invariants and cross-run cache
// hits. Uses onClear (not onReplace): after a restore() the counter is set
// explicitly by the cache loader from the snapshot's metadata so post-restore
// freshMetavar() allocations continue from the stored boundary.
Store.onClear(() => { _metavarNext = 0; });

export { freshEvar, resetFresh, getFreshCounter, freshMetavar, resetMetavar };
export default { freshEvar, resetFresh, getFreshCounter, freshMetavar, resetMetavar };
