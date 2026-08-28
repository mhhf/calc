/**
 * Stateless PRF family (D17) + the 'sample' aggregation realization
 * (grade-algebra.md; TODO_0284 P1b — extracted from timed/timed.js so
 * non-timed consumers, e.g. will's decimation loop (TODO_0292), draw
 * from the SAME family the conflict chooser uses).
 *
 * No RNG state anywhere: every draw is a pure function of a seed and
 * content-derived identity, so runs are reproducible and — when the
 * inputs are chosen covariantly — horizon-split invariant. Moved
 * VERBATIM: the settle-determinism PRF pins depend on these exact mixes.
 */

import { add, cmp, mul } from '../rat.js';

/** 32-bit finalizer mix (xor-shift-multiply) — the PRF core. */
function mix32(x) {
  x = Math.imul(x ^ (x >>> 16), 0x45d9f3b);
  x = Math.imul(x ^ (x >>> 13), 0x45d9f3b);
  return (x ^ (x >>> 16)) >>> 0;
}

/** Hash a theta binding array (undefined-safe, position-mixed). */
function thetaHash(theta) {
  let h = 0;
  for (let i = 0; i < theta.length; i++) {
    h = mix32(h ^ (((theta[i] === undefined ? -1 : theta[i]) | 0) + 0x9e3779b9) ^ i);
  }
  return h >>> 0;
}

/** FNV-1a over a string (32-bit) — for covariant candidate keys. */
function strHash(s) {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 0x01000193);
  return h >>> 0;
}

/**
 * The 'sample' aggregation realization (grade-algebra.md measure class,
 * THY_0026 T3): map a 32-bit PRF value into the cumulative-weight
 * interval of exactly one alternative — alternative i is drawn iff
 * (u32/2³²)·total ∈ [Σ_{j<i} w_j, Σ_{j≤i} w_j). Interval lengths are the
 * renormalized masses, so the draw is unbiased by construction, exact in
 * rationals (never through a float), and a zero-mass alternative has an
 * empty interval — it is never drawn.
 *
 * weightAt(i) returns the exact [n,d] weight of alternative i; total is
 * the exact mass Σ w_i. For a validated distribution (weights sum to 1)
 * pass total = [1n, 1n] (the default) — evaluation then stays LAZY past
 * the sampled interval, which is what lets fire-time weight resolution
 * (timed woplus) skip alternatives it never reaches.
 */
function sampleIndex(u32, n, weightAt, total = [1n, 1n]) {
  const u = mul(total, [BigInt(u32 >>> 0), 4294967296n]);
  let cum = [0n, 1n];
  for (let i = 0; i < n; i++) {
    cum = add(cum, weightAt(i));
    if (cmp(u, cum) < 0) return i;
  }
  return n - 1;   // u = 1 − ε edge
}

export { mix32, thetaHash, strHash, sampleIndex };
export default { mix32, thetaHash, strHash, sampleIndex };
