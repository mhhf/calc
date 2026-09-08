/**
 * Ratlit Equational Theory — the ℚ theory of the till numeric tower,
 * shared by the calculi that import rat.ill (till, gill, sill, will).
 *
 * Two representations of one object, the rationals ℚ (TODO_0265 Phase 1, D14):
 *
 *   rat(N, D)  — constructor term over bin; what backward clauses match
 *                (semantics: calculus/till/prelude/rat.ill)
 *   ratlit     — compact kernel leaf, 2 bigint children (num, den);
 *                storage + FFI fast path
 *
 * Exact analogy to i/o/e ↔ binlit via binlitTheory — and since RES_0143
 * L10 the same LAYERING: binlit's theory lives in calculus/ill/lib/,
 * this one lives here. Registered per-calculus via
 * calculusConfig.theories; representation READING (putRat/ratParts/
 * isRatTerm) is kernel infrastructure (lib/kernel/rat-term.js) because
 * the certificate checkers consume it.
 *
 * Canonical form (the only form putRat produces, so equal rationals are
 * hash-equal): gcd-reduced, den > 0, zero = (0, 1), den = 1 collapses
 * to binlit (ℚ ⊇ ℕ: an integer rational IS the integer — one hash per
 * value, which is what keeps timed cohorts from splitting on
 * representation).
 */

import Store from '../../../lib/kernel/store.js';
import { putRat, ratParts, isRatTerm, binVal as _binVal } from '../../../lib/kernel/rat-term.js';
import { registerFirstArgClassifier } from '../../../lib/kernel/eq-theory.js';
import { registerLeafTag } from '../../../lib/engine/backchain.js';

const _TAG_RATLIT = Store.TAG.ratlit;
const _TAG_BINLIT = Store.TAG.binlit;
const _TAG_STRLIT = Store.TAG.strlit;
const _TAG_CHARLIT = Store.TAG.charlit;
const _TAG_FREEVAR = Store.TAG.freevar;
const _TAG_METAVAR = Store.TAG.metavar;
const _TAG_ARRLIT = Store.TAG.arrlit;

// 'rat' is a dynamic predicate tag (registered by rat.ill) — resolve lazily.
function _tagRat() { return Store.TAG.rat; }

const ratlitTheory = {
  name: 'ratlit',
  sourceTagIds: [_TAG_RATLIT],
  // Value class (tag names): the ℚ forms — compact ratlit, structural
  // rat(N,D), and the q-tower's frac constructor. Consumed by
  // over-approximation clients via kernel theoryClassTags() (RES_0143 L4).
  classTags: ['ratlit', 'rat', 'frac'],

  canRewrite(srcTid, dstTid) {
    if (srcTid !== _TAG_RATLIT) return false;
    const tr = _tagRat();
    return tr !== undefined && dstTid === tr;
  },

  /**
   * Rewrite compact to structural: ratlit(n, d) → rat(binlit(n), binlit(d)).
   * Only for non-negative rationals — rat(N, D) ranges over bin = ℕ
   * (negative grades are deferred, TODO_0265 Deferred: debt/dual).
   */
  rewrite(srcTid, srcHash, dstTid, dstArity) {
    if (srcTid !== _TAG_RATLIT) return null;
    const tr = _tagRat();
    if (tr === undefined || dstTid !== tr || dstArity !== 2) return null;
    const n = Store.child(srcHash, 0);
    const d = Store.child(srcHash, 1);
    if (n < 0n) return null;
    return Store.put('rat', [Store.put1('binlit', n), Store.put1('binlit', d)]);
  },

  /**
   * Canonicalize: structural rat(N, D) with ground bin children → canonical
   * compact form via putRat (which collapses den = 1 to binlit). Recurses
   * into compound terms; leaves everything else unchanged. rat nodes with
   * unresolvable or zero-denominator children stay as-is (clauses guard).
   *
   * Also folds the numeral constructors over rational leaves: o(x) ≡ 2x
   * and i(x) ≡ 2x + 1 are true equations of the numeric sort over ℚ, not
   * just ℕ. With split namespaces (D8.1 revised) no in-contract derivation
   * produces o/i-wrapped rationals, but bin clauses with unconstrained
   * variables (mul/s1's Y) can still derive them from ill-sorted goals —
   * the digit algorithms are semiring-generic, so the wrapped forms are
   * value-correct and folding them is the theory's honest completion
   * (defense-in-depth, not load-bearing).
   */
  canonicalize(h) {
    if (!Store.isTerm(h)) return h;
    const tid = Store.tagId(h);

    const tr = _tagRat();
    if (tr !== undefined && tid === tr && Store.arity(h) === 2) {
      const n = _binVal(Store.child(h, 0));
      const d = _binVal(Store.child(h, 1));
      if (n !== null && d !== null && d !== 0n) return putRat(n, d);
      return h;
    }

    // o/i over a rational leaf: fold by value (binlitTheory, which runs
    // first in the composed canonicalizer, has already folded pure-ℕ chains).
    const ti = Store.TAG.i, to = Store.TAG.o;
    if ((tid === ti || tid === to) && Store.arity(h) === 1) {
      const c = ratlitTheory.canonicalize(Store.child(h, 0));
      const cTid = Store.tagId(c);
      if (cTid === _TAG_RATLIT) {
        const n = Store.child(c, 0), d = Store.child(c, 1);
        return putRat(tid === ti ? 2n * n + d : 2n * n, d);
      }
      if (cTid === _TAG_BINLIT) {
        const n = Store.child(c, 0);
        return putRat(tid === ti ? 2n * n + 1n : 2n * n, 1n);
      }
      return c === Store.child(h, 0) ? h : Store.put1(Store.tag(h), c);
    }

    // Leaf types — no recursion needed
    if (tid === _TAG_RATLIT || tid === _TAG_BINLIT || tid === _TAG_STRLIT ||
        tid === _TAG_CHARLIT || tid === _TAG_FREEVAR || tid === _TAG_METAVAR) return h;

    if (tid === _TAG_ARRLIT) {
      const elems = Store.getArrayElements(h);
      if (!elems || elems.length === 0) return h;
      let changed = false;
      const newElems = new Uint32Array(elems.length);
      for (let i = 0; i < elems.length; i++) {
        const ne = ratlitTheory.canonicalize(elems[i]);
        newElems[i] = ne;
        if (ne !== elems[i]) changed = true;
      }
      return changed ? Store.putArray(newElems) : h;
    }

    const arity = Store.arity(h);
    if (arity === 0) return h;
    let changed = false;
    const nc = [];
    for (let i = 0; i < arity; i++) {
      const c = Store.child(h, i);
      if (typeof c === 'number' && Store.isTerm(c)) {
        const rc = ratlitTheory.canonicalize(c);
        nc.push(rc);
        if (rc !== c) changed = true;
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(Store.tag(h), nc) : h;
  }
};

let _installed = false;

/**
 * Install global ratlit wiring: the first-arg classifier (ratlit goals index
 * into the 'rat' clause bucket) and the backchain leaf-tag registration
 * (ratlit is non-decomposable in resolution). Idempotent. Theory COMPOSITION
 * stays per-caller (calculusConfig.theories / backchain opts.theories) — only
 * the classification/leaf registries are global, like the tag registry itself.
 */
function installRatlitTheory() {
  if (_installed) return;
  _installed = true;
  registerFirstArgClassifier(_TAG_RATLIT, () => 'rat');
  registerLeafTag(_TAG_RATLIT);
}

export { ratlitTheory, putRat, ratParts, isRatTerm, installRatlitTheory };
export default { ratlitTheory, putRat, ratParts, isRatTerm, installRatlitTheory };
