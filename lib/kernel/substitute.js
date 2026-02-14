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

  const varMap = new Map(theta);

  function go(hash) {
    if (varMap.has(hash)) return varMap.get(hash);

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
  eq,
  copy,
  occurs
};
