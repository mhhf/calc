/**
 * Rational FFI — shared module (TODO_0265 Phase 1, D8.1).
 *
 * Two surfaces, matching the clause layer in calculus/till/prelude/rat.ill:
 *
 * 1. OVERLOAD fallbacks (gated): the existing FFI functions for
 *    plus/mul/lt/le/eq/neq/eq_bool keep their bin×bin fast path and, on
 *    bin-decode failure, tail-call the matching function here. The gate —
 *    at least one argument genuinely rational-represented (ratlit or
 *    rat(N,D)) — guarantees pure-bin semantics never change. Only the
 *    operations whose bin and rational semantics COINCIDE on the shared
 *    domain are overloaded.
 *
 * 2. EXPLICIT q-operations (ungated, bins coerce to n/1): qplus, qsub,
 *    qmul, qdiv, qlt, qle, qneq. sub/div/mod are NOT overloaded — bin sub
 *    is a saturating monus and bin div is Euclidean; neither lifts
 *    coherently to ℚ (the shared relation would become non-functional).
 *    The rational counterparts are qsub (checked: fails on negative) and
 *    qdiv (exact: fails on zero divisor).
 *
 * Results go through putRat, so they are canonical (den = 1 → binlit) and
 * hash-equal to what clause resolution derives after canonicalization —
 * the FFI-principle agreement the fuzzer checks.
 */

import * as rat from '../../rat.js';
import { ratParts, putRat, isRatTerm } from './ratlit-theory.js';

const EMPTY_THETA = [];

/** Decode all n inputs as rationals (bins coerce to n/1); null if any fails. */
function _decodeAll(args, n) {
  const out = new Array(n);
  for (let i = 0; i < n; i++) {
    const p = ratParts(args[i]);
    if (p === null) return null;
    out[i] = p;
  }
  return out;
}

/** Overload gate: decode iff at least one input is genuinely rational. */
function _decodeGated(args, n) {
  for (let i = 0; i < n; i++) {
    if (isRatTerm(args[i])) return _decodeAll(args, n);
  }
  return null;
}

// ── Overload fallbacks (gated) ───────────────────────────────────────

function plus(args) {
  const [a, b, c] = args;
  // Forward mode + + -
  {
    const ps = _decodeGated([a, b], 2);
    if (ps) return { success: true, theta: [[c, putRat(...rat.add(ps[0], ps[1]))]] };
  }
  // Reverse mode - + +: A = C − B, failing on negative (mirrors bin plus)
  {
    const ps = _decodeGated([c, b], 2);
    if (ps) {
      const d = rat.sub(ps[0], ps[1]);
      if (d[0] < 0n) return { success: false, reason: 'negative_result' };
      return { success: true, theta: [[a, putRat(...d)]] };
    }
  }
  return null;
}

function mul(args) {
  const [a, b, c] = args;
  const ps = _decodeGated([a, b], 2);
  if (!ps) return null;
  return { success: true, theta: [[c, putRat(...rat.mul(ps[0], ps[1]))]] };
}

function _cmpGated(args) {
  const ps = _decodeGated(args, 2);
  return ps ? rat.cmp(ps[0], ps[1]) : null;
}

function lt(args) {
  const c = _cmpGated(args);
  return c === null ? null : { success: c < 0, theta: EMPTY_THETA };
}

function le(args) {
  const c = _cmpGated(args);
  return c === null ? null : { success: c <= 0, theta: EMPTY_THETA };
}

function eq(args) {
  const c = _cmpGated(args);
  return c === null ? null : { success: c === 0, theta: EMPTY_THETA };
}

function neq(args) {
  const c = _cmpGated(args);
  return c === null ? null : { success: c !== 0, theta: EMPTY_THETA };
}

function eq_bool(args) {
  const c = _cmpGated(args);
  if (c === null) return null;
  return { success: true, theta: [[args[2], putRat(c === 0 ? 1n : 0n, 1n)]] };
}

// ── Explicit q-operations (ungated; bins coerce) ─────────────────────

const _FAIL_CONV = { success: false, reason: 'conversion_failed' };

function qplus(args) {
  const ps = _decodeAll(args, 2);
  if (!ps) return _FAIL_CONV;
  return { success: true, theta: [[args[2], putRat(...rat.add(ps[0], ps[1]))]] };
}

/** Checked subtraction: fails on negative results (ℚ≥0). */
function qsub(args) {
  const ps = _decodeAll(args, 2);
  if (!ps) return _FAIL_CONV;
  const d = rat.sub(ps[0], ps[1]);
  if (d[0] < 0n) return { success: false, reason: 'negative_result' };
  return { success: true, theta: [[args[2], putRat(...d)]] };
}

function qmul(args) {
  const ps = _decodeAll(args, 2);
  if (!ps) return _FAIL_CONV;
  return { success: true, theta: [[args[2], putRat(...rat.mul(ps[0], ps[1]))]] };
}

/** Exact (field) division: fails on zero divisor. */
function qdiv(args) {
  const ps = _decodeAll(args, 2);
  if (!ps) return _FAIL_CONV;
  const r = rat.div(ps[0], ps[1]);
  if (r === null) return { success: false, reason: 'division_by_zero' };
  return { success: true, theta: [[args[2], putRat(...r)]] };
}

function _qcmp(args) {
  const ps = _decodeAll(args, 2);
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

function qneq(args) {
  const c = _qcmp(args);
  return c === null ? _FAIL_CONV : { success: c !== 0, theta: EMPTY_THETA };
}

export { plus, mul, lt, le, eq, neq, eq_bool, qplus, qsub, qmul, qdiv, qlt, qle, qneq };
export default { plus, mul, lt, le, eq, neq, eq_bool, qplus, qsub, qmul, qdiv, qlt, qle, qneq };
