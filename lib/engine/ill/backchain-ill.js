/**
 * ILL-specific defaults for the backward prover.
 *
 * Extracted from prove.js to keep the core prover calculus-agnostic.
 * Provides: normalization (via binlitTheory), proof term construction,
 * and FFI dispatch.
 *
 * Note: arrlit ↔ acons/ae expansion is handled inline in prove.js because
 * the Store normalizes acons(H, arrlit(T)) → arrlit([H, ...T]), making it
 * impossible to create acons nodes via Store.put. Array expansion is a
 * Store-level structural concern, not ILL-specific.
 */

const Store = require('../../kernel/store');
const { isPredTag, getPredicateHead: getHead, buildRightTensor } = require('../../kernel/ast');
const { defaultTheories } = require('../../kernel/eq-theory');
const { binlitTheory } = require('./binlit-theory');
const { setTheories } = require('../../kernel/unify');

// ── Tag registration ────────────────────────────────────────────────
// o, i are dynamic (>= PRED_BOUNDARY) — may change after Store.restore().
const _ATOM_E = Store.put('atom', ['e']);
Store.put('atom', ['ae']); // ensure ae atom exists for prove.js
Store.put('o', [_ATOM_E]); // ensure o tag is registered
Store.put('i', [_ATOM_E]); // ensure i tag is registered

// Register ILL equational theories (binlit ↔ i/o/e) for all matchers.
// Must happen after o/i tag registration above.
setTheories([...defaultTheories, binlitTheory]);

// Lazy FFI import — never loaded for non-ILL callers
let _ffi = null;
function _getFfi() { if (!_ffi) _ffi = require('./ffi'); return _ffi; }

/** Get default FFI metadata (lazy). */
function getFFIMeta() { return _getFfi().defaultMeta; }

// ── Normalization ───────────────────────────────────────────────────

/**
 * Normalize binary constructor chains (i/o/e) to compact binlit form.
 * Delegates to binlitTheory.canonicalize — single source of truth.
 */
const normalize = binlitTheory.canonicalize;

// ── Proof Term Construction ─────────────────────────────────────────

function _tensorRSpine(terms) {
  if (terms.length === 0) return { rule: 'one_r', principal: null, subterms: [] };
  if (terms.length === 1) return terms[0];
  let acc = terms[terms.length - 1];
  for (let i = terms.length - 2; i >= 0; i--) {
    acc = { rule: 'tensor_r', principal: null, subterms: [terms[i], acc] };
  }
  return acc;
}

/**
 * Build an ILL clause proof term from ground components.
 * Reconstructs: copy(loli(tensor(!P₁,...), monad(Q)), loli_l(antProof, monad_l(id(Q))))
 */
function buildClauseTerm(groundPrems, premTerms, groundHead) {
  const bangPrems = groundPrems.map(p => Store.put('bang', [p]));
  const groundAnt = buildRightTensor(bangPrems);
  const groundMonad = Store.put('monad', [groundHead]);
  const groundLoli = Store.put('loli', [groundAnt, groundMonad]);

  const wrappedPrems = premTerms.map(pt =>
    ({ rule: 'promotion', principal: null, subterms: [pt] }));
  const antProof = _tensorRSpine(wrappedPrems);

  const monadBody = { rule: 'monad_l', principal: groundMonad, subterms: [
    { rule: 'id', principal: groundHead, subterms: [] }
  ]};
  const loliApp = { rule: 'loli_l', principal: groundLoli,
                    subterms: [antProof, monadBody] };
  return { rule: 'copy', principal: groundLoli, subterms: [loliApp] };
}

// ── FFI Dispatch ────────────────────────────────────────────────────

/** Default FFI dispatch for ILL predicates. */
function tryFFI(goal, ffiMeta) {
  const head = getHead(goal);
  if (!head) return null;
  const meta = ffiMeta[head];
  if (!meta || !meta.ffi) return null;
  if (!Store.isTerm(goal) || !isPredTag(Store.tag(goal))) return null;
  const a = Store.arity(goal);
  const args = new Array(a);
  for (let i = 0; i < a; i++) args[i] = Store.child(goal, i);
  const ffiMod = _getFfi();
  if (!ffiMod.mode.checkMode(args, meta.mode)) return null;
  const fn = ffiMod.get(meta.ffi);
  if (!fn) return null;
  return fn(args);
}

/**
 * Build proof term for an FFI-resolved goal.
 */
function buildFFITerm() {
  return { rule: 'ffi', principal: null, subterms: [] };
}

/**
 * Build proof term for a type/axiom match (copy + identity).
 */
function buildTypeTerm(groundGoal) {
  return { rule: 'copy', principal: groundGoal,
           subterms: [{ rule: 'id', principal: groundGoal, subterms: [] }] };
}

module.exports = { normalize, buildClauseTerm, buildFFITerm, buildTypeTerm, tryFFI, getFFIMeta };
