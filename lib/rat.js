/**
 * Exact rational arithmetic — pure BigInt pairs, no Store dependency.
 *
 * A rational is a pair [num, den] of BigInts with den > 0. norm() is the
 * only constructor: gcd-reduced, sign carried by num, zero = [0n, 1n].
 * All operations return normalized pairs (TODO_0265 Phase 1, D3/D14).
 *
 * The module is total on ℚ (signed); ℚ≥0 policies (saturating sub, bin
 * mirroring) belong to the FFI layer, not here.
 */

'use strict';

/** Non-negative gcd; gcd(x, 0) = |x|, gcd(0, 0) = 0. */
function gcd(a, b) {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  while (b !== 0n) { const t = a % b; a = b; b = t; }
  return a;
}

/**
 * Normalize n/d: gcd-reduced, den > 0.
 * @throws {RangeError} on d === 0n (constructing 1/0 is a programming error).
 */
function norm(n, d) {
  if (d === 0n) throw new RangeError('rat: zero denominator');
  if (d < 0n) { n = -n; d = -d; }
  if (n === 0n) return [0n, 1n];
  const g = gcd(n, d);
  return [n / g, d / g];
}

/** a/b + c/d */
function add([a, b], [c, d]) { return norm(a * d + c * b, b * d); }

/** a/b − c/d (exact, signed) */
function sub([a, b], [c, d]) { return norm(a * d - c * b, b * d); }

/** (a/b) · (c/d) */
function mul([a, b], [c, d]) { return norm(a * c, b * d); }

/** (a/b) ÷ (c/d); null on division by zero. */
function div([a, b], [c, d]) { return c === 0n ? null : norm(a * d, b * c); }

/** Three-way compare: sign of a/b − c/d as -1 | 0 | 1. */
function cmp([a, b], [c, d]) {
  const l = a * d, r = c * b; // b, d > 0 — cross-multiplication preserves order
  return l < r ? -1 : l > r ? 1 : 0;
}

/** True iff the (normalized) pair denotes an integer. */
function isInt([, d]) { return d === 1n; }

export { gcd, norm, add, sub, mul, div, cmp, isInt };
export default { gcd, norm, add, sub, mul, div, cmp, isInt };
