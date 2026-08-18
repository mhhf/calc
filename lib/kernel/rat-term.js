/**
 * Rational term construction — canonical ℚ in the Store (TODO_0265, D3/D14).
 *
 * Kernel-level so both the parser (exact `@` literals) and the engine
 * theories build the SAME canonical form: gcd-reduced, den > 0, and
 * integer rationals (den = 1, num ≥ 0) collapse to binlit — ℚ ⊇ ℕ, one
 * hash per value, which is what keeps timed cohorts from splitting on
 * representation. Floats never touch this path.
 */

import Store from './store.js';
import { norm } from '../rat.js';

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

export { putRat };
export default { putRat };
