/**
 * Pattern utilities — tree walkers for content-addressed rule patterns.
 *
 * Shared by compile.js (rule compilation) and rule-analysis.js (delta analysis).
 */

import Store from '../kernel/store.js';
/** Check if term is ground (no metavars). Freevars and evars are ground. */
function isGround(h) {
  // Fast path: Store.isGround checks groundBits — strict "no metavars AND no freevars".
  // If true, pattern-utils semantics (metavar-free) is also satisfied.
  if (Store.isGround(h)) return true;
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'metavar') return false;
  // arrlit is an opaque container: walk its (possibly non-ground) elements.
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++) {
      if (!isGround(elems[i])) return false;
    }
    return true;
  }
  // `tn` is opaque ONLY as a ground runtime trie (handled by the groundBits
  // fast-path above). A non-ground `tn` is a clause PATTERN (`tn L V R`) whose
  // metavar children must be walked — fall through to generic recursion.
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && !isGround(c)) return false;
  }
  return true;
}

// Memoization cache: content-addressed hash → frozen metavar array.
// Invalidated on Store.clear() or Store.restore() (both fire onReplace) —
// restore swaps in a different snapshot, so same IDs may refer to different content.
const _EMPTY_MV = Object.freeze([]);
const _mvCache = new Map();
Store.onReplace(() => { _mvCache.clear(); });

function _walkCollectMV(h, out) {
  const t = Store.tag(h);
  if (!t) return;
  if (t === 'metavar') { out.add(h); return; }
  if (t === 'freevar') return;
  // Ground runtime trie: opaque (no metavars). A non-ground `tn` is a clause
  // PATTERN (`tn L V R`) — recurse into its children to collect L, V, R.
  if (t === 'tn' && Store.isGround(h)) return;
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++) _walkCollectMV(elems[i], out);
    return;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) _walkCollectMV(c, out);
  }
}

/**
 * Internal: get cached metavar array for hash h (populates cache on miss).
 * Returns the shared empty array for ground terms.
 */
function _getMetavarArray(h) {
  if (Store.isGround(h)) return _EMPTY_MV;
  let cached = _mvCache.get(h);
  if (cached === undefined) {
    const s = new Set();
    _walkCollectMV(h, s);
    cached = s.size === 0 ? _EMPTY_MV : Object.freeze([...s]);
    _mvCache.set(h, cached);
  }
  return cached;
}

/** Collect metavar hashes into a Set. */
function collectMetavars(h, out) {
  const cached = _getMetavarArray(h);
  for (let i = 0; i < cached.length; i++) out.add(cached[i]);
}

/** True iff h contains any metavar (memoized; O(1) for ground terms). */
function hasMetavars(h) {
  return _getMetavarArray(h).length > 0;
}

/**
 * Check if h contains any metavar in `domain`.
 * Allocation-free path when h's metavar set is cached or the term is ground.
 */
function hasMetavarInDomain(h, domain) {
  const cached = _getMetavarArray(h);
  for (let i = 0; i < cached.length; i++) {
    if (domain.has(cached[i])) return true;
  }
  return false;
}

/** Collect all freevars in a pattern. */
function collectFreevars(h) {
  const vars = new Set();
  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === 'freevar' || t === 'metavar') { vars.add(hash); return; }
    // Ground runtime trie: opaque. A non-ground `tn` is a clause pattern whose
    // variable children must be walked.
    if (t === 'tn' && Store.isGround(hash)) return;
    if (t === 'arrlit') {
      const elems = Store.getArrayElements(hash);
      if (elems) for (let i = 0; i < elems.length; i++) walk(elems[i]);
      return;
    }
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) walk(c);
    }
  }
  walk(h);
  return vars;
}

export { isGround, collectMetavars, hasMetavars, hasMetavarInDomain, collectFreevars };
export default { isGround, collectMetavars, hasMetavars, hasMetavarInDomain, collectFreevars };
