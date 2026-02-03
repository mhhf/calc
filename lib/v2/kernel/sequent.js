/**
 * Generic Sequent
 *
 * Simple structure: { contexts: { [name]: [formula, ...] }, succedent }
 * No assumptions about context semantics (set/multiset/list).
 * Prover-specific modules handle resource tracking.
 */

const { hashCombine } = require('../../hash');
const { hashAST } = require('./ast-hash');

// =============================================================================
// Sequent Construction
// =============================================================================

/**
 * Create sequent with array contexts
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
 */
const fromArrays = (linear, cartesian, succedent) => seq({
  linear: linear || [],
  cartesian: cartesian || []
}, succedent);

// =============================================================================
// Sequent Operations
// =============================================================================

/**
 * Deep copy sequent
 */
const copy = (s) => {
  const { copy: copyAST } = require('./substitute');
  return seq(
    Object.fromEntries(
      Object.entries(s.contexts).map(([name, ctx]) => [
        name,
        ctx.map(f => copyAST(f))
      ])
    ),
    copyAST(s.succedent)
  );
};

/**
 * Apply substitution to sequent
 */
const substitute = (s, theta) => {
  const { apply } = require('./substitute');
  return seq(
    Object.fromEntries(
      Object.entries(s.contexts).map(([name, ctx]) => [
        name,
        ctx.map(f => apply(f, theta))
      ])
    ),
    apply(s.succedent, theta)
  );
};

/**
 * Get all free variable names in sequent
 */
const freeVars = (s) => {
  const { freeVars: astFreeVars } = require('./ast');
  const vars = new Set();

  for (const ctx of Object.values(s.contexts)) {
    for (const f of ctx) {
      for (const v of astFreeVars(f)) vars.add(v);
    }
  }
  for (const v of astFreeVars(s.succedent)) vars.add(v);

  return [...vars];
};

/**
 * Rename free variables to unique names
 */
let varIndex = 0;
const renameVars = (s) => {
  const vars = freeVars(s);
  const mkVar = (n) => ({ tag: 'freevar', children: [n] });

  const theta = vars.map(v => [mkVar(v), mkVar(`_V${varIndex++}`)]);
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

  const ctxHashes = Object.entries(s.contexts)
    .sort(([a], [b]) => a.localeCompare(b))
    .flatMap(([_, ctx]) => ctx.map(hashAST).sort((a, b) => a < b ? -1 : 1));

  return s._hash = hashCombine(...ctxHashes, hashAST(s.succedent));
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
 */
const getContext = (s, ctxName) => s.contexts[ctxName] || [];

/**
 * Add formula to context (returns new sequent)
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
 */
const setSuccedent = (s, succedent) => seq(s.contexts, succedent);

module.exports = {
  // Core
  hashAST,
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
