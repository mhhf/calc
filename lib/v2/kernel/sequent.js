/**
 * Generic Sequent for content-addressed terms
 *
 * Structure: { contexts: { [name]: [hash, ...] }, succedent: hash }
 * All formulas are stored as hashes (numbers).
 * No assumptions about context semantics (set/multiset/list).
 */

const { hashCombine } = require('../../hash');
const { hashAST } = require('./ast-hash');
const Store = require('./store');
const { apply: subApply } = require('./substitute');
const { freeVars: astFreeVars } = require('./ast');

// =============================================================================
// Sequent Construction
// =============================================================================

/**
 * Create sequent with array contexts
 * @param {{ [name]: number[] }} contexts - Context name -> formula hashes
 * @param {number} succedent - Succedent formula hash
 */
const seq = (contexts, succedent) => ({ contexts, succedent, _hash: null });

/**
 * Create empty sequent with named contexts
 */
const empty = (ctxNames = ['linear', 'cartesian']) => seq(
  Object.fromEntries(ctxNames.map(n => [n, []])),
  null
);

/**
 * Create sequent from formula arrays (convenience for ILL)
 * @param {number[]} linear - Linear context formula hashes
 * @param {number[]} cartesian - Cartesian context formula hashes
 * @param {number} succedent - Succedent formula hash
 */
const fromArrays = (linear, cartesian, succedent) => seq({
  linear: linear || [],
  cartesian: cartesian || []
}, succedent);

// =============================================================================
// Sequent Operations
// =============================================================================

/**
 * Copy sequent (shallow - hashes are immutable)
 */
const copy = (s) => seq(
  Object.fromEntries(
    Object.entries(s.contexts).map(([name, ctx]) => [name, [...ctx]])
  ),
  s.succedent
);

/**
 * Apply substitution to sequent
 * @param {Object} s - Sequent
 * @param {Array<[number, number]>} theta - Substitution
 */
const substitute = (s, theta) => seq(
  Object.fromEntries(
    Object.entries(s.contexts).map(([name, ctx]) => [
      name,
      ctx.map(h => subApply(h, theta))
    ])
  ),
  subApply(s.succedent, theta)
);

/**
 * Get all free variable names in sequent
 */
const freeVars = (s) => {
  const vars = new Set();

  for (const ctx of Object.values(s.contexts)) {
    for (const h of ctx) {
      for (const v of astFreeVars(h)) vars.add(v);
    }
  }
  if (s.succedent) {
    for (const v of astFreeVars(s.succedent)) vars.add(v);
  }

  return [...vars];
};

/**
 * Rename free variables to unique names
 */
let varIndex = 0;
const renameVars = (s) => {
  const vars = freeVars(s);
  const theta = vars.map(v => [
    Store.intern('freevar', [v]),
    Store.intern('freevar', [`_V${varIndex++}`])
  ]);
  return { seq: substitute(s, theta), theta };
};

// =============================================================================
// Hashing and Equality
// =============================================================================

/**
 * Compute sequent hash (order-independent within each context)
 */
const hash = (s) => {
  if (s._hash) return s._hash;

  // Sort context hashes for order-independence
  const ctxHashes = Object.entries(s.contexts)
    .sort(([a], [b]) => a.localeCompare(b))
    .flatMap(([_, ctx]) => [...ctx].sort((a, b) => a - b));

  return s._hash = hashCombine(...ctxHashes, s.succedent || 0);
};

/**
 * Check sequent equality via hash
 */
const eq = (a, b) => hash(a) === hash(b);

// =============================================================================
// Simple Context Operations (generic)
// =============================================================================

/**
 * Get context by name
 * @returns {number[]} Array of formula hashes
 */
const getContext = (s, ctxName) => s.contexts[ctxName] || [];

/**
 * Add formula to context (returns new sequent)
 * @param {number} formula - Formula hash
 */
const addToContext = (s, ctxName, formula) => seq(
  { ...s.contexts, [ctxName]: [...(s.contexts[ctxName] || []), formula] },
  s.succedent
);

/**
 * Remove formula at index from context (returns new sequent)
 */
const removeAtIndex = (s, ctxName, index) => {
  const ctx = s.contexts[ctxName] || [];
  if (index < 0 || index >= ctx.length) return null;
  return seq(
    { ...s.contexts, [ctxName]: [...ctx.slice(0, index), ...ctx.slice(index + 1)] },
    s.succedent
  );
};

/**
 * Set succedent (returns new sequent)
 * @param {number} succedent - Formula hash
 */
const setSuccedent = (s, succedent) => seq(s.contexts, succedent);

module.exports = {
  // Core
  hashAST,  // Re-export for convenience (now identity)
  seq,
  empty,
  fromArrays,
  hash,
  eq,

  // Operations
  copy,
  substitute,
  freeVars,
  renameVars,

  // Context access
  getContext,
  addToContext,
  removeAtIndex,
  setSuccedent
};
