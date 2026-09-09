/**
 * Equational Theory API
 *
 * An equational theory describes one class of representational equivalence.
 * The kernel provides theories for Store's compact literal types; calculus
 * layers register additional theories (e.g., ILL registers binlit).
 *
 * Interface — EquationalTheory:
 *   name:          string
 *   sourceTagIds:  number[]  — tag IDs this theory can rewrite FROM (for O(1) lookup)
 *   canRewrite:    (srcTagId, dstTagId) => boolean
 *   rewrite:       (srcTid, srcHash, dstTid, dstArity) => number | null
 *   canonicalize:  (hash) => number
 *
 * Dispatch: matchers use a precomputed _rewriteFromTag[tagId] → theory lookup
 * for O(1) dispatch. No loop overhead in the hot path when tags don't match
 * any theory (just a single property lookup returning undefined).
 *
 * STATE-CANONICITY INVARIANT (doc/def/0046): hash identity is
 * representation equality, not value equality — the engine keeps the two
 * interchangeable inside live states by canonicalizing at every
 * fact-entry boundary (production via the compile-time canonPatterns
 * gate, plain-object entry, loli materialization, clause outputs).
 * A theory that declares a canonical form MUST make canonicalize() a
 * fixpoint-reaching fold to it; a theory whose canonicalize is the
 * identity (strlit) opts out — its value class may split state rows by
 * representation, and only matching (rewrite) sees through it.
 *
 * Store-level structural concern: arrlit ↔ acons/ae is NOT expressible via
 * the rewrite API because Store.put('acons', [h, arrlit(t)]) normalizes to
 * arrlit([h, ...t]). Array decomposition stays inline in each matcher.
 * See backchain-ill.js header comment for the rationale.
 */

import Store from './store.js';
const { TAG } = Store;

// ── Strlit theory: strlit ↔ cons/nil ─────────────────────────────────

const _TAG_STRLIT = TAG.strlit;

const strlitTheory = {
  name: 'strlit',
  sourceTagIds: [_TAG_STRLIT],

  canRewrite(srcTid, dstTid) {
    if (srcTid !== _TAG_STRLIT) return false;
    return dstTid === TAG.cons || dstTid === TAG.atom;
  },

  rewrite(srcTid, srcHash, dstTid, dstArity) {
    if (srcTid !== _TAG_STRLIT) return null;
    const str = Store.child(srcHash, 0);

    // strlit("") → atom('nil')
    if (dstTid === TAG.atom && str === '') return Store.put('atom', ['nil']);

    // strlit("abc") → cons(charlit('a'), strlit("bc"))
    if (dstTid === TAG.cons && dstArity === 2 && str !== '') {
      return Store.put('cons', [
        Store.put1('charlit', str.charCodeAt(0)),
        Store.put1('strlit', str.slice(1))
      ]);
    }

    return null;
  },

  canonicalize(h) { return h; }
};

// ── Default theories (Store built-ins) ───────────────────────────────

// Only strlit — arrlit uses inline decomposition (Store normalization).
const defaultTheories = [strlitTheory];

// ── Theory lookup table ──────────────────────────────────────────────

/**
 * Build O(1) lookup table: tagId → theory for cross-tag dispatch.
 * Called once at theory registration time. Matchers use:
 *   const th = _rewriteFromTag[tagId];
 *   if (th) { const r = th.rewrite(...); ... }
 */
function buildTheoryLookup(theories) {
  const lookup = {};
  for (const th of theories) {
    if (th.sourceTagIds) {
      for (const tid of th.sourceTagIds) lookup[tid] = th;
    }
  }
  return lookup;
}

// ── First-argument classification for compact literals ───────────────
//
// Clause indexing buckets goals by the outermost constructor of their first
// argument. Compact literal tags must classify as the structural head their
// theory rewrites them to (binlit → 'e'/'i'/'o', ratlit → 'rat'), or goals
// with compact first args never find the structurally-headed clauses.
//
// All classification goes through this registry (TODO_0265 Phase 2b):
// binlit registers via installBinlitClassifier() (called from initILL),
// ratlit via installRatlitTheory(). The three call sites (backchain.js,
// compile.js, opt/compiled-clauses.js) have no inline special cases.
// Contract for direct backchain callers: install the owning theory's
// classifier BEFORE chaining with compact-literal first args — an
// unregistered tag classifies as null → the default bucket → structurally-
// headed clauses are missed unless allBuckets is on.
const _firstArgClassifiers = new Map(); // tagId → (hash) => string

/** Register a classifier for a compact-literal tag. Idempotent by tagId. */
function registerFirstArgClassifier(tagId, fn) {
  _firstArgClassifiers.set(tagId, fn);
}

/** Classify a first-arg hash by its compact tag; null when unregistered. */
function classifyFirstArg(tagId, hash) {
  const fn = _firstArgClassifiers.get(tagId);
  return fn ? fn(hash) : null;
}

/**
 * Build a composed canonicalize function from all registered theories.
 * Returns null if no theory has canonicalize, a single function if one does,
 * or a composed function that applies each in sequence.
 */
function buildCanonicalizer(theories) {
  const fns = [];
  for (const t of theories) {
    if (t.canonicalize && t.canonicalize !== _identity) fns.push(t.canonicalize);
  }
  if (fns.length === 0) return null;
  if (fns.length === 1) return fns[0];
  return (h) => { for (let i = 0; i < fns.length; i++) h = fns[i](h); return h; };
}
function _identity(h) { return h; }

export { defaultTheories, buildTheoryLookup, buildCanonicalizer, registerFirstArgClassifier, classifyFirstArg };
export default { defaultTheories, buildTheoryLookup, buildCanonicalizer, registerFirstArgClassifier, classifyFirstArg };
