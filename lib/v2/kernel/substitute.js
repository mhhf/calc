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
  // If h equals v, return val
  if (h === v) return val;

  // Get the node
  const node = Store.get(h);
  if (!node) return h;  // Shouldn't happen, but be safe

  const { tag, children } = node;

  // Recursively substitute in children
  let changed = false;
  const newChildren = children.map(c => {
    if (Store.isTermChild(c)) {
      // Child is a hash - recurse
      const newC = sub(c, v, val);
      if (newC !== c) changed = true;
      return newC;
    } else {
      // Child is a primitive (string) - keep as is
      return c;
    }
  });

  // If nothing changed, return original hash
  if (!changed) return h;

  // Intern and return new hash
  return Store.intern(tag, newChildren);
};

/**
 * Apply a substitution (list of [var, val] pairs)
 * @param {number} h - Term hash
 * @param {Array<[number, number]>} theta - Substitution
 * @returns {number} New term hash
 */
const apply = (h, theta) => theta.reduce((acc, [v, val]) => sub(acc, v, val), h);

/**
 * Check if variable v occurs in term h
 * @param {number} v - Variable hash
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const occurs = (v, h) => {
  if (v === h) return true;

  const node = Store.get(h);
  if (!node) return false;

  return node.children.some(c =>
    Store.isTermChild(c) ? occurs(v, c) : false
  );
};

module.exports = { sub, apply, eq, copy, occurs };
