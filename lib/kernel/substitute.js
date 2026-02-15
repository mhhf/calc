/**
 * Substitution for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Equality is O(1) hash comparison.
 * Substitution returns a new hash (interned).
 */

const Store = require('./store');

/**
 * Equality: O(1) hash comparison
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {boolean}
 */
const eq = (a, b) => a === b;

/**
 * Copy is identity for content-addressed terms (immutable)
 * @param {number} h - Term hash
 * @returns {number} Same hash
 */
const copy = h => h;

/**
 * Substitute v with val in term h
 * @param {number} h - Term hash
 * @param {number} v - Variable hash to replace
 * @param {number} val - Replacement term hash
 * @returns {number} New term hash (or same if unchanged)
 */
const sub = (h, v, val) => {
  if (h === v) return val;

  const t = Store.tag(h);
  if (!t) return h;

  const a = Store.arity(h);
  let changed = false;
  const newChildren = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const newC = sub(c, v, val);
      if (newC !== c) changed = true;
      newChildren.push(newC);
    } else {
      newChildren.push(c);
    }
  }

  if (!changed) return h;
  return Store.put(t, newChildren);
};

/**
 * Apply a substitution (list of [var, val] pairs) - single traversal
 * Complexity: O(N + M) where N = |theta|, M = term size
 * REQUIRES: theta is idempotent (variables don't reference other bound vars)
 * @param {number} h - Term hash
 * @param {Array<[number, number]>} theta - Substitution
 * @returns {number} New term hash
 */
const apply = (h, theta) => {
  if (theta.length === 0) return h;

  function go(hash) {
    for (let i = 0; i < theta.length; i++) {
      if (theta[i][0] === hash) return theta[i][1];
    }

    const t = Store.tag(hash);
    if (!t) return hash;

    // Atoms and freevars (not in varMap) are leaves
    if (t === 'atom' || t === 'freevar') return hash;

    const a = Store.arity(hash);
    let changed = false;
    const newChildren = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) {
        const nc = go(c);
        if (nc !== c) changed = true;
        newChildren.push(nc);
      } else {
        newChildren.push(c);
      }
    }

    return changed ? Store.put(t, newChildren) : hash;
  }

  return go(h);
};

/**
 * Apply a flat interleaved substitution [v0, t0, v1, t1, ...] - single traversal
 * Hot-path version: avoids pair array allocations.
 * @param {number} h - Term hash
 * @param {number[]} theta - Flat interleaved substitution
 * @returns {number} New term hash
 */
const applyFlat = (h, theta) => {
  if (theta.length === 0) return h;

  function go(hash) {
    // Flat theta lookup
    for (let i = 0; i < theta.length; i += 2) {
      if (theta[i] === hash) return theta[i + 1];
    }

    const t = Store.tag(hash);
    if (!t || t === 'atom' || t === 'freevar') return hash;

    const a = Store.arity(hash);

    // Arity-specialized paths: avoid newChildren[] allocation
    if (a === 2) {
      const c0 = Store.child(hash, 0), c1 = Store.child(hash, 1);
      const n0 = Store.isTermChild(c0) ? go(c0) : c0;
      const n1 = Store.isTermChild(c1) ? go(c1) : c1;
      return (n0 !== c0 || n1 !== c1) ? Store.put(t, [n0, n1]) : hash;
    }
    if (a === 1) {
      const c0 = Store.child(hash, 0);
      const n0 = Store.isTermChild(c0) ? go(c0) : c0;
      return n0 !== c0 ? Store.put(t, [n0]) : hash;
    }
    if (a === 0) return hash;

    // Fallback for arity >= 3 (rare)
    let changed = false;
    const nc = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) {
        const r = go(c);
        if (r !== c) changed = true;
        nc.push(r);
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(t, nc) : hash;
  }

  return go(h);
};

/**
 * Check if variable v occurs in term h
 * @param {number} v - Variable hash
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const occurs = (v, h) => {
  if (v === h) return true;

  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && occurs(v, c)) return true;
  }
  return false;
};

module.exports = {
  sub,
  apply,
  applyFlat,
  eq,
  copy,
  occurs
};
