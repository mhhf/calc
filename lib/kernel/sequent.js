/**
 * Generic Sequent for content-addressed terms
 *
 * Structure: { contexts: { [name]: [hash, ...] }, succedent: hash }
 * All formulas are stored as hashes (numbers).
 * No assumptions about context semantics (set/multiset/list).
 */

import { hashCombine } from '../hash.js';
import Store from './store.js';
import { apply as subApply } from './substitute.js';
import { freeVars as astFreeVars } from './ast.js';
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
 * Default two-zone context structure (the LNL shape). The CONVENIENCE
 * default for calculi without family zone declarations — same status as
 * `empty()`'s default zone names. Calculi that declare `@position_modes`
 * + `@structural` rules in their family file get a DERIVED structure
 * instead (lib/calculus/index.js deriveContextStructure, TODO_0086).
 * Single source of truth: the prover kernel and buildCalculus both
 * import this rather than keeping private copies.
 */
const DEFAULT_CONTEXT_STRUCTURE = Object.freeze({
  zones: Object.freeze(['linear', 'cartesian']),
  properties: Object.freeze({
    linear: Object.freeze({ exchange: true, contraction: false, weakening: false }),
    cartesian: Object.freeze({ exchange: true, contraction: true, weakening: true }),
  }),
  consumableZone: 'linear',
  consumableZones: Object.freeze(['linear']),
  copySource: 'cartesian',
  copyTarget: 'linear',
});

// =============================================================================
// Consumable-zone routing (TODO_0285)
// =============================================================================
//
// A calculus may declare AUX consumable zones beyond the primary one
// (deriveContextStructure). Membership is decided by the zone's WRAPPER
// connective tag (a constructor whose @category names the zone), so a
// formula is self-describing: zone columns are the router-materialized
// view of one threaded pool, and the search's Context deltas stay
// zone-blind (hash-disjointness — a wrapper-tagged formula never legally
// sits in the primary zone).

/** Zone name a formula routes to among the consumable zones. */
const routeZone = (cs, h) => {
  const byTag = cs.wrapperZoneByTag;
  if (!byTag) return cs.consumableZone;
  return byTag[Store.tag(h)] || cs.consumableZone;
};

/**
 * Union pool of a sequent's consumable zones, primary zone first.
 * Fast path: with a single consumable zone the CZ array is returned
 * as-is — two-zone calculi see zero allocation. The result may ALIAS a
 * zone column (single-zone path, and the one-non-empty-zone case below)
 * — callers must treat it as read-only; only genuine unions allocate.
 */
const consumablePool = (s, cs) => {
  const zones = cs.consumableZones;
  if (!zones || zones.length === 1) return s.contexts[cs.consumableZone] || [];
  let out = null;
  for (const z of zones) {
    const ctx = s.contexts[z];
    if (ctx && ctx.length) out = out ? out.concat(ctx) : ctx;
  }
  if (out === null) return [];
  // A single non-empty zone returns its array unchanged; only genuine
  // unions allocate.
  return out;
};

/**
 * Build consumable-zone columns for an array of formulas by routing.
 * Every consumable zone is present (empty arrays included) so premise
 * sequents have a deterministic column set.
 */
const routeContexts = (cs, formulas) => {
  const zones = cs.consumableZones || [cs.consumableZone];
  if (zones.length === 1) return { [cs.consumableZone]: formulas };
  const out = {};
  for (const z of zones) out[z] = [];
  for (const h of formulas) out[routeZone(cs, h)].push(h);
  return out;
};

/**
 * Create empty sequent with named contexts
 */
const empty = (ctxNames = DEFAULT_CONTEXT_STRUCTURE.zones) => seq(
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
    Store.put('freevar', [v]),
    Store.put('metavar', [`V${varIndex++}`])
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

export { seq, empty, fromArrays, DEFAULT_CONTEXT_STRUCTURE, hash, eq, copy, substitute, freeVars, renameVars, getContext, addToContext, removeAtIndex, routeZone, consumablePool, routeContexts };
export default { seq, empty, fromArrays, DEFAULT_CONTEXT_STRUCTURE, hash, eq, copy, substitute, freeVars, renameVars, getContext, addToContext, removeAtIndex, routeZone, consumablePool, routeContexts };
