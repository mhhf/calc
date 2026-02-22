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

/**
 * Check if a tag string is a user-defined predicate (not a built-in/connective/structural tag).
 * Uses the Store's tag ID boundary: pre-registered tags (ID < PRED_BOUNDARY) are built-in,
 * dynamically registered tags (ID >= PRED_BOUNDARY) are user-defined predicates.
 * @param {string} tagName - Tag string
 * @returns {boolean}
 */
function isPredTag(tagName) {
  const id = Store.TAG[tagName];
  return id !== undefined && id >= Store.PRED_BOUNDARY;
}

/**
 * Get the predicate head of a term.
 * For atoms: returns the atom name (string child 0).
 * For flat predicates (tag >= PRED_BOUNDARY): returns the tag string.
 * Otherwise: null.
 * @param {number} h - Term hash
 * @returns {string|null}
 */
function getPredicateHead(h) {
  if (!Store.isTerm(h)) return null;
  const tid = Store.tagId(h);
  if (tid === Store.TAG.atom) return Store.child(h, 0);
  if (tid >= Store.PRED_BOUNDARY) return Store.TAG_NAMES[tid];
  return null;
}

module.exports = {
  copy,
  eq,
  freeVars,
  isAtomic,
  connective,
  tag,
  children,
  getPredicateHead,
  isPredTag
};
