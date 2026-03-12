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

/**
 * Peel bang/forall wrappers from a rule formula to get the loli node.
 *
 * Program rules in .ill files are stored as: !∀X₁.∀X₂...∀Xₙ.(A ⊸ {B})
 * The outermost bang makes them persistent (in gamma). Universals bind
 * metavars instantiated at match time. The loli is the actual rule body.
 */
function getLoliFromRule(hash) {
  let h = hash;
  for (let i = 0; i < 20; i++) {
    const t = Store.tag(h);
    if (t === 'loli') return h;
    if (t === 'bang' || t === 'forall') { h = Store.child(h, 0); continue; }
    return null;
  }
  return null;
}

/**
 * Build a right-associated tensor tree from ground fact hashes.
 * [f1, f2, f3] → tensor(f1, tensor(f2, f3))
 * [f1] → f1
 * [] → one
 */
function buildRightTensor(hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

/**
 * Collect external freevars from a term — freevars not in the rule's slot map.
 * These come from the forward engine state (symbolic values like _Sender)
 * and must NOT be unified by the backward prover.
 *
 * @param {number} hash - Term hash to inspect
 * @param {Object} slots - Rule's metavarSlots (freevar hash → theta index)
 * @returns {Set<number>|null} Set of external freevar hashes, or null if none
 */
function collectExternalFreevars(hash, slots) {
  let externals = null;
  function walk(h) {
    if (!Store.isTerm(h)) return;
    const node = Store.get(h);
    if (!node) return;
    if (node.tag === 'freevar') {
      if (slots[h] === undefined) {
        if (!externals) externals = new Set();
        externals.add(h);
      }
      return;
    }
    if (node.tag === 'atom' || node.tag === 'binlit' ||
        node.tag === 'strlit' || node.tag === 'charlit') return;
    for (const child of node.children) {
      if (Store.isTermChild(child)) walk(child);
    }
  }
  walk(hash);
  return externals;
}

/**
 * Check if a backward prover's theta bound any external freevars.
 * If so, the result is unsound — the prover assumed specific values
 * for symbolic constants (e.g. and(_Sender, mask, Z) → binds _Sender=0).
 *
 * @param {Array} theta - Prover's returned theta: [[freevarHash, value], ...]
 * @param {Set<number>} externals - External freevar hashes from collectExternalFreevars
 * @returns {boolean} true if any external freevar was bound (result is unsound)
 */
function proverBoundExternals(theta, externals) {
  for (let i = 0; i < theta.length; i++) {
    if (externals.has(theta[i][0])) return true;
  }
  return false;
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
  isPredTag,
  getLoliFromRule,
  buildRightTensor,
  collectExternalFreevars,
  proverBoundExternals
};
