/**
 * Rational term construction + representation reading — canonical ℚ in
 * the Store (TODO_0265, D3/D14).
 *
 * Kernel-level so the parser (exact `@` literals), the engine, and the
 * certificate checkers all build/read the SAME canonical form:
 * gcd-reduced, den > 0, and integer rationals (den = 1, num ≥ 0)
 * collapse to binlit — ℚ ⊇ ℕ, one hash per value, which is what keeps
 * timed cohorts from splitting on representation. Floats never touch
 * this path.
 *
 * ratParts/isRatTerm moved here from the engine's ratlit-theory
 * (RES_0143 L10): representation READING is kernel-numeric
 * infrastructure — the TCB's fire-check consumes ratParts, so it must
 * not live beside solver/registration machinery. The equational THEORY
 * (rewrite/canonicalize) and its registration stay calculus-side
 * (calculus/till/lib/ratlit-theory.js), registered via cc.theories.
 */

import Store from './store.js';
import { norm } from '../rat.js';

const _TAG_RATLIT = Store.TAG.ratlit;
const _TAG_BINLIT = Store.TAG.binlit;
const _TAG_ATOM = Store.TAG.atom;

// 'rat' is a dynamic predicate tag (registered by rat.ill) — resolve lazily.
function _tagRat() { return Store.TAG.rat; }

/**
 * Store a rational in canonical form.
 * @param {bigint} n @param {bigint} d
 * @returns {number} term hash
 */
function putRat(n, d) {
  const [n2, d2] = norm(n, d);
  if (d2 === 1n && n2 >= 0n) return Store.put1('binlit', n2);
  return Store.put('ratlit', [n2, d2]);
}

/** Minimal bin decoder (binlit + i/o/e structural numeral chains). */
function binVal(h) {
  const tid = Store.tagId(h);
  if (tid === _TAG_BINLIT) return Store.child(h, 0);
  if (tid === _TAG_ATOM) return Store.child(h, 0) === 'e' ? 0n : null;
  const t = Store.tag(h);
  if ((t === 'i' || t === 'o') && Store.arity(h) === 1) {
    const rest = binVal(Store.child(h, 0));
    if (rest === null) return null;
    return t === 'i' ? rest * 2n + 1n : rest * 2n;
  }
  return null;
}

/**
 * Decode a hash as a rational pair [num, den], or null.
 * Accepts ratlit, bin forms (coerced to n/1), and structural rat(N, D)
 * with decodable bin children. Does NOT require canonical input.
 */
function ratParts(h) {
  const tid = Store.tagId(h);
  if (tid === _TAG_RATLIT) return [Store.child(h, 0), Store.child(h, 1)];
  const tr = _tagRat();
  if (tr !== undefined && tid === tr && Store.arity(h) === 2) {
    const n = binVal(Store.child(h, 0));
    const d = binVal(Store.child(h, 1));
    if (n === null || d === null || d === 0n) return null;
    return [n, d];
  }
  const n = binVal(h);
  return n === null ? null : [n, 1n];
}

/** True iff the hash is a genuinely rational representation (ratlit or rat(·,·)) —
 *  the FFI dispatch gate: bin×bin must keep bin semantics (integer div!). */
function isRatTerm(h) {
  const tid = Store.tagId(h);
  if (tid === _TAG_RATLIT) return true;
  const tr = _tagRat();
  return tr !== undefined && tid === tr;
}

export { putRat, ratParts, isRatTerm, binVal };
export default { putRat, ratParts, isRatTerm, binVal };
