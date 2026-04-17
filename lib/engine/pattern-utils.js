/**
 * Pattern utilities — tree walkers for content-addressed rule patterns.
 *
 * Shared by compile.js (rule compilation) and rule-analysis.js (delta analysis).
 */

const Store = require('../kernel/store');

/** Check if term is ground (no metavars). Freevars and evars are ground. */
function isGround(h) {
  // Fast path: Store.isGround checks groundBits — strict "no metavars AND no freevars".
  // If true, pattern-utils semantics (metavar-free) is also satisfied.
  if (Store.isGround(h)) return true;
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'metavar') return false;
  // Opaque containers: no metavars possible inside
  if (t === 'arrlit' || t === 'tn') {
    if (t === 'arrlit') {
      const elems = Store.getArrayElements(h);
      if (elems) for (let i = 0; i < elems.length; i++) {
        if (!isGround(elems[i])) return false;
      }
    }
    return true;
  }
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
  if (t === 'freevar' || t === 'tn') return;
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
    if (t === 'tn') return; // opaque container (runtime trie, no freevars)
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

module.exports = { isGround, collectMetavars, hasMetavarInDomain, collectFreevars };
