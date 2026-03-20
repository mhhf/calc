/**
 * ILL-specific defaults for the backward prover.
 *
 * Extracted from prove.js to keep the core prover calculus-agnostic.
 * Provides: normalization, proof term construction, FFI dispatch,
 * and equational normalization (binlit ↔ o/i/e).
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
const _TAG_BINLIT = Store.TAG.binlit;

const _ATOM_E = Store.put('atom', ['e']);
Store.put('atom', ['ae']); // ensure ae atom exists for prove.js
Store.put('o', [_ATOM_E]); // ensure o tag is registered
Store.put('i', [_ATOM_E]); // ensure i tag is registered

// Register ILL equational theories (binlit ↔ i/o/e) for all matchers.
// Must happen after o/i tag registration above.
setTheories([...defaultTheories, binlitTheory]);

function _tagO() { return Store.TAG.o; }
function _tagI() { return Store.TAG.i; }

// Lazy FFI import — never loaded for non-ILL callers
let _ffi = null;
function _getFfi() { if (!_ffi) _ffi = require('../ffi'); return _ffi; }

/** Get default FFI metadata (lazy). */
function getFFIMeta() { return _getFfi().defaultMeta; }

// ── Normalization ───────────────────────────────────────────────────

/**
 * Normalize binary constructor chains (i/o/e) to compact binlit form.
 * Prevents hash divergence between forward engine and clause resolution.
 */
function normalize(h) {
  if (!Store.isTerm(h)) return h;
  const tag = Store.tag(h);
  if (!tag) return h;
  const ffiMod = _getFfi();
  if (tag === 'i' || tag === 'o') {
    const v = ffiMod.convert.binToInt(h);
    if (v !== null) return ffiMod.convert.intToBin(v);
  }
  if (tag === 'atom') {
    const v = ffiMod.convert.binToInt(h);
    if (v !== null) return ffiMod.convert.intToBin(v);
    return h;
  }
  if (tag === 'binlit' || tag === 'strlit' || tag === 'charlit' ||
      tag === 'freevar' || tag === 'metavar') return h;
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) {
      const rc = normalize(c);
      nc.push(rc);
      if (rc !== c) changed = true;
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(tag, nc) : h;
}

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

// ── Equational Normalization ─────────────────────────────────────────────

/**
 * Rewrite a term between compact and structural binary number representations.
 *
 * Handles ILL binary arithmetic equivalences:
 *   binlit(0n)          ↔  atom('e')           (binary zero)
 *   binlit(n) even n>0  →  o(binlit(n>>1))     (zero-bit / even)
 *   binlit(n) odd       →  i(binlit(n>>1))     (one-bit / odd)
 *   atom('e')           →  binlit(0n)           (reverse of zero)
 *
 * The compact→structural direction always produces fully concrete results.
 * The structural→compact direction only handles atom('e') since compound
 * forms (o(X), i(X)) may contain metavars — _groundMatch's bidirectional
 * calls handle the reverse by rewriting the compact side instead.
 *
 * Note: arrlit ↔ acons/ae is NOT handled here because the Store normalizes
 * acons(H, arrlit(T)) → arrlit([H, ...T]). Array expansion is handled
 * inline in prove.js via direct child decomposition.
 *
 * @param {number} srcTid - Source term's tag ID
 * @param {number} srcHash - Source term's Store hash
 * @param {number} dstTid - Target tag ID to rewrite towards
 * @param {number} dstArity - Target expected arity
 * @returns {number|null} Rewritten Store hash, or null if not applicable
 */
function eqRewrite(srcTid, srcHash, dstTid, dstArity) {
  // binlit → structural (e / o / i)
  if (srcTid === _TAG_BINLIT) {
    const val = Store.child(srcHash, 0);
    if (typeof val !== 'bigint') return null;
    if (val === 0n && dstTid === Store.TAG.atom) return _ATOM_E;
    if (dstTid === _tagO() && dstArity === 1 && val > 0n && (val & 1n) === 0n)
      return Store.put('o', [Store.put1('binlit', val >> 1n)]);
    if (dstTid === _tagI() && dstArity === 1 && (val & 1n) === 1n)
      return Store.put('i', [Store.put1('binlit', val >> 1n)]);
    return null;
  }

  // atom('e') → binlit(0n)
  if (srcTid === Store.TAG.atom) {
    if (Store.child(srcHash, 0) === 'e' && dstTid === _TAG_BINLIT)
      return Store.put1('binlit', 0n);
    return null;
  }

  return null;
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

module.exports = { normalize, buildClauseTerm, buildFFITerm, buildTypeTerm, tryFFI, eqRewrite, getFFIMeta };
