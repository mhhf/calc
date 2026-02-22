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

/**
 * De Bruijn substitution: replace bound(index) with replacement in body.
 * Increments depth under nested exists/forall binders.
 * @param {number} bodyHash - Term hash containing bound variables
 * @param {bigint} index - De Bruijn index to replace (0n = innermost binder)
 * @param {number} replacement - Term hash to substitute in
 * @returns {number} New term hash
 */
const debruijnSubst = (bodyHash, index, replacement) => {
  const TAG_BOUND = Store.TAG.bound;
  const TAG_EXISTS = Store.TAG.exists;
  const TAG_FORALL = Store.TAG.forall;
  function go(h, depth) {
    const tid = Store.tagId(h);
    if (!tid) return h;
    if (tid === TAG_BOUND) {
      const k = Store.child(h, 0); // BigInt
      return k === BigInt(depth) ? replacement : h;
    }
    if (tid === TAG_EXISTS || tid === TAG_FORALL) {
      const body = Store.child(h, 0);
      const newBody = go(body, depth + 1);
      return newBody !== body ? Store.put(Store.TAG_NAMES[tid], [newBody]) : h;
    }
    const a = Store.arity(h);
    if (a === 0) return h;
    let changed = false;
    const nc = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (Store.isTermChild(c)) {
        const r = go(c, depth);
        if (r !== c) changed = true;
        nc.push(r);
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(Store.TAG_NAMES[tid], nc) : h;
  }
  return go(bodyHash, Number(index));
};

/**
 * Apply an indexed substitution (Stage 6 de Bruijn theta).
 *
 * theta[slot] = value, slots[hash] = slotIndex.
 * O(1) metavar lookup instead of O(n) linear scan.
 *
 * See doc/research/de-bruijn-indexed-matching.md.
 *
 * @param {number} h - Term hash
 * @param {Array} theta - Indexed theta (theta[slot] = value)
 * @param {Object} slots - { [metavarHash]: slotIndex }
 * @returns {number} New term hash
 */
const applyIndexed = (h, theta, slots) => {
  function go(hash) {
    // O(1) slot lookup (undefined if hash not a metavar in this rule)
    const slot = slots[hash];
    if (slot !== undefined) {
      const val = theta[slot];
      if (val !== undefined) return val;
    }

    const t = Store.tag(hash);
    if (!t || t === 'atom' || t === 'freevar') return hash;

    const a = Store.arity(hash);

    // Arity-specialized paths
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
 * Compiled substitution — direct Store.put from precomputed recipe.
 * Bypasses recursive applyIndexed traversal for flat patterns.
 *
 * recipe: { tag, sources: [{type:'slot',slot}|{type:'literal',value}], compiled, isSlot }
 *
 * @param {Object} recipe - Compiled substitution recipe
 * @param {Array} theta - Indexed theta (theta[slot] = value)
 * @returns {number} New term hash
 */
const subCompiled = (recipe, theta) => {
  if (recipe.isSlot) return theta[recipe.slot];
  const sources = recipe.sources;
  const n = sources.length;
  if (n === 1) {
    const s = sources[0];
    return Store.put(recipe.tag, [s.type === 'slot' ? theta[s.slot] : s.value]);
  }
  if (n === 2) {
    const s0 = sources[0], s1 = sources[1];
    return Store.put(recipe.tag, [
      s0.type === 'slot' ? theta[s0.slot] : s0.value,
      s1.type === 'slot' ? theta[s1.slot] : s1.value
    ]);
  }
  const children = [];
  for (let i = 0; i < n; i++) {
    const s = sources[i];
    children.push(s.type === 'slot' ? theta[s.slot] : s.value);
  }
  return Store.put(recipe.tag, children);
};

module.exports = {
  sub,
  apply,
  applyIndexed,
  subCompiled,
  debruijnSubst,
  eq,
  copy,
  occurs
};
