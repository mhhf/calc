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

// Tags that are NOT flat predicates (built-in or connective tags)
const NON_PRED_TAGS = new Set([
  'atom', 'freevar', 'app', 'binlit', 'strlit', 'charlit',
  'tensor', 'loli', 'with', 'bang', 'one',
  'type', 'arrow', 'monad',
  'var', 'any', 'hyp', 'comma', 'empty', 'seq', 'deriv'
]);

/**
 * Get the predicate head of a term.
 * For atoms: returns the atom name (string child 0).
 * For flat predicates (non-NON_PRED_TAGS): returns the tag string.
 * Otherwise: null.
 * @param {number} h - Term hash
 * @returns {string|null}
 */
function getPredicateHead(h) {
  const t = Store.tag(h);
  if (!t) return null;
  if (!NON_PRED_TAGS.has(t)) return t;
  if (t === 'atom') return Store.child(h, 0);
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
  NON_PRED_TAGS
};
