/**
 * AST Utilities for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 */

const Store = require('./store');
const { copy, eq } = require('./substitute');

/**
 * Get free variable names from term
 * @param {number} h - Term hash
 * @returns {string[]} - Unique variable names
 */
function freeVars(h) {
  const vars = new Set();

  function walk(hash) {
    const node = Store.get(hash);
    if (!node) return;

    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string') vars.add(name);
      return;
    }

    for (const child of node.children) {
      if (Store.isTermChild(child)) walk(child);
    }
  }

  walk(h);
  return [...vars];
}

/**
 * Check if formula is atomic (atom or freevar)
 * @param {number} h - Term hash
 * @returns {boolean}
 */
function isAtomic(h) {
  const tag = Store.tag(h);
  return tag === 'atom' || tag === 'freevar';
}

/**
 * Get the principal connective (tag) of formula
 * @param {number} h - Term hash
 * @returns {string|null}
 */
function connective(h) {
  return Store.tag(h) || null;
}

/**
 * Get content-addressed hash (identity for content-addressed terms)
 * @param {number} h - Term hash
 * @returns {number} Same hash
 */
function hash(h) {
  return h;
}

/**
 * Map over term children (returns new term hash if any child changed)
 * @param {number} h - Term hash
 * @param {Function} fn - Function to apply to each term child
 * @returns {number} - New term hash or same if unchanged
 */
function mapChildren(h, fn) {
  const node = Store.get(h);
  if (!node) return h;

  let changed = false;
  const newChildren = node.children.map(c => {
    if (Store.isTermChild(c)) {
      const newC = fn(c);
      if (newC !== c) changed = true;
      return newC;
    }
    return c;
  });

  if (!changed) return h;
  return Store.intern(node.tag, newChildren);
}

/**
 * Fold over term (depth-first)
 * @param {number} h - Term hash
 * @param {Function} fn - Function(acc, hash) -> acc
 * @param {*} initial - Initial accumulator value
 * @returns {*} - Final accumulator value
 */
function fold(h, fn, initial) {
  let acc = fn(initial, h);

  const node = Store.get(h);
  if (node) {
    for (const child of node.children) {
      if (Store.isTermChild(child)) {
        acc = fold(child, fn, acc);
      }
    }
  }

  return acc;
}

/**
 * Get tag of term
 * @param {number} h - Term hash
 * @returns {string|undefined}
 */
function tag(h) {
  return Store.tag(h);
}

/**
 * Get children of term
 * @param {number} h - Term hash
 * @returns {(number|string)[]}
 */
function children(h) {
  return Store.children(h);
}

module.exports = {
  copy,
  eq,
  freeVars,
  isAtomic,
  connective,
  hash,
  tag,
  children,
  mapChildren,
  fold
};
