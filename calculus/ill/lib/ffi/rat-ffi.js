/**
 * Rational FFI — the q-operation family (TODO_0265 Phase 1, D8.1 revised).
 *
 * Split namespaces, no overloading (Denis, 2026-08-18): the bin family
 * (plus, mul, lt, … — bin.ill) and the rational family (qplus, qsub, qmul,
 * qdiv, qlt, qle, qeq, qneq, qeq_bool — rat.ill) never share a predicate.
 * One rule instead of a per-predicate memory: on rationals, use q-ops.
 * Bins coerce to n/1, so q-ops are total on the numeric sort — till-side
 * arithmetic uses q-ops exclusively (Phase 3's window-expression lowering
 * emits them).
 *
 * Semantics on ℚ≥0 (negatives are outside rat(N,D)'s range — debt/dual
 * grades deferred): qsub is CHECKED (fails on negative — a saturating monus
 * would be a silent-clamp bug factory for time stamps), qdiv is exact field
 * division (fails on zero divisor; deliberately distinct from bin div's
 * Euclidean quotient — those are different operations, same as Haskell's
 * Integral.div vs Fractional./).
 *
 * Results go through putRat, so they are canonical (den = 1 → binlit) and
 * hash-equal to what clause resolution derives after canonicalization —
 * the FFI-principle agreement the fuzzer checks (§3.12).
 */

import * as rat from '../../../../lib/rat.js';
import { ratParts, putRat } from '../../../../lib/kernel/rat-term.js';

const EMPTY_THETA = [];
const _FAIL_CONV = { success: false, reason: 'conversion_failed' };

/**
 * Decode one input as a rational (bins coerce to n/1); null if it is not a
 * ground numeral. NEGATIVE numerators are rejected: the v1 contract is ℚ≥0
 * (rat(N, D) ranges over bin = ℕ; ratlitTheory.rewrite refuses n < 0), so
 * the clause path can neither represent nor derive them. Accepting them here
 * would let the FFI succeed where clause resolution fails — violating the
 * FFI principle (audit round 11). Signed STORAGE stays (D14: no migration
 * later); signed SEMANTICS arrive with debt/dual grades.
 */
function _decode1(h) {
  const p = ratParts(h);
  return (p === null || p[0] < 0n) ? null : p;
}

function _decode2(args) {
  const a = _decode1(args[0]);
  if (a === null) return null;
  const b = _decode1(args[1]);
  if (b === null) return null;
  return [a, b];
}

/**
 * Multi-modal on the tower (TODO_0273): forward mode A + B = C, plus the
 * SOLVE modes with one addend free and the result ground — the residual
 * C ⊖ known, checked like qsub (negative ⇒ fail: no valid residual exists,
 * matching clause-path derivability). This is the tower's complete decision
 * procedure for solve mode; bin args reach it through num.plus fallback
 * (they coerce to n/1 and putRat re-canonicalizes den-1 results to binlit).
 */
function qplus(args) {
  const pa = _decode1(args[0]);
  const pb = _decode1(args[1]);
  if (pa && pb) {
    return { success: true, theta: [[args[2], putRat(...rat.add(pa, pb))]] };
  }
  const known = pa || pb;
  if (known) {
    const pc = _decode1(args[2]);
    if (pc) {
      const d = rat.sub(pc, known);
      if (d[0] < 0n) return { success: false, reason: 'negative_result' };
      return { success: true, theta: [[pa ? args[1] : args[0], putRat(...d)]] };
    }
  }
  return _FAIL_CONV;
}

/** Checked subtraction: fails on negative results (ℚ≥0). */
function qsub(args) {
  const ps = _decode2(args);
  if (!ps) return _FAIL_CONV;
  const d = rat.sub(ps[0], ps[1]);
  if (d[0] < 0n) return { success: false, reason: 'negative_result' };
  return { success: true, theta: [[args[2], putRat(...d)]] };
}

function qmul(args) {
  const ps = _decode2(args);
  if (!ps) return _FAIL_CONV;
  return { success: true, theta: [[args[2], putRat(...rat.mul(ps[0], ps[1]))]] };
}

/** Exact (field) division: fails on zero divisor. */
function qdiv(args) {
  const ps = _decode2(args);
  if (!ps) return _FAIL_CONV;
  const r = rat.div(ps[0], ps[1]);
  if (r === null) return { success: false, reason: 'division_by_zero' };
  return { success: true, theta: [[args[2], putRat(...r)]] };
}

function _qcmp(args) {
  const ps = _decode2(args);
  return ps ? rat.cmp(ps[0], ps[1]) : null;
}

function qlt(args) {
  const c = _qcmp(args);
  return c === null ? _FAIL_CONV : { success: c < 0, theta: EMPTY_THETA };
}

function qle(args) {
  const c = _qcmp(args);
  return c === null ? _FAIL_CONV : { success: c <= 0, theta: EMPTY_THETA };
}

function qeq(args) {
  const c = _qcmp(args);
  return c === null ? _FAIL_CONV : { success: c === 0, theta: EMPTY_THETA };
}

function qneq(args) {
  const c = _qcmp(args);
  return c === null ? _FAIL_CONV : { success: c !== 0, theta: EMPTY_THETA };
}

function qeq_bool(args) {
  const c = _qcmp(args);
  if (c === null) return _FAIL_CONV;
  return { success: true, theta: [[args[2], putRat(c === 0 ? 1n : 0n, 1n)]] };
}

/**
 * Order-theoretic selection (TODO_0284 P2): the rational instances behind
 * the COLLAPSED tower names min/max (num.min/num.max dispatch — bin.ill's
 * min/max clauses are the bin instance, gill's /q clauses the instance at
 * the bound; both agree on the shared subsort, so the coherence law lets
 * the names share — unlike qsub/qdiv). The result is an ARGUMENT, so it is
 * already canonical; putRat re-canonicalizes for the hash-for-hash FFI
 * agreement anyway.
 */
function qmin(args) {
  const ps = _decode2(args);
  if (!ps) return _FAIL_CONV;
  const m = rat.cmp(ps[0], ps[1]) <= 0 ? ps[0] : ps[1];
  return { success: true, theta: [[args[2], putRat(...m)]] };
}

function qmax(args) {
  const ps = _decode2(args);
  if (!ps) return _FAIL_CONV;
  const m = rat.cmp(ps[0], ps[1]) >= 0 ? ps[0] : ps[1];
  return { success: true, theta: [[args[2], putRat(...m)]] };
}

export { qplus, qsub, qmul, qdiv, qlt, qle, qeq, qneq, qeq_bool, qmin, qmax };
export default { qplus, qsub, qmul, qdiv, qlt, qle, qeq, qneq, qeq_bool, qmin, qmax };
