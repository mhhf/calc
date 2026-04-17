/**
 * TODO_0216 Phase 3 (idea N) — `Substitution` type
 *
 * Formalises the "θ is idempotent" invariant that was previously maintained
 * by an inline comment at substitute.js:87. No representation change; this
 * wraps the array-of-pairs so callers have a place to hang an optional debug
 * assertion without paying its cost in release builds.
 *
 * Invariant: for every (v, val) in pairs, `apply(val, pairs) === val`.
 *   i.e. `apply(apply(h, θ), θ) === apply(h, θ)` for any h.
 *
 * All 15 `apply()` callers already preserve this invariant (see the caller
 * audit in TODO_0216 Execution Plan). The class is an opt-in wrapper for new
 * code; the legacy `[[v,val], ...]` array form remains the hot-path shape.
 *
 * Activate debug-mode assertion with CALC_0216_SUBST_ASSERT=1.
 */

const _ASSERT_ENABLED = (typeof process !== 'undefined') &&
  (process.env.CALC_0216_SUBST_ASSERT === '1');

class Substitution {
  /**
   * @param {Array<[number, number]>} pairs - [[varHash, valueHash], ...]
   */
  constructor(pairs) {
    this._pairs = pairs;
    if (_ASSERT_ENABLED) this._assertIdempotent();
  }

  /**
   * @param {Array<[number, number]>} pairs
   * @returns {Substitution}
   */
  static fromPairs(pairs) {
    return new Substitution(pairs);
  }

  /** Alias for fromPairs. */
  static of(pairs) {
    return new Substitution(pairs);
  }

  /** Empty substitution — identity on every term. */
  static empty() {
    return new Substitution([]);
  }

  /** Legacy array form for the hot path. */
  toArray() {
    return this._pairs;
  }

  get size() {
    return this._pairs.length;
  }

  /**
   * Apply this substitution to a term.
   * @param {number} h - Term hash
   * @returns {number}
   */
  apply(h) {
    // Resolve apply lazily to break the require cycle with substitute.js.
    const substitute = require('./substitute');
    return substitute.apply(h, this._pairs);
  }

  /**
   * Compose two idempotent substitutions: (σ ∘ τ)(x) = σ(τ(x)).
   * Result is re-closed so it stays idempotent.
   * @param {Substitution} other
   * @returns {Substitution}
   */
  compose(other) {
    const substitute = require('./substitute');
    const out = [];
    // τ values get σ applied.
    for (let i = 0; i < other._pairs.length; i++) {
      const [v, val] = other._pairs[i];
      out.push([v, substitute.apply(val, this._pairs)]);
    }
    // σ keeps whatever isn't shadowed by τ's domain.
    const otherDom = new Set(other._pairs.map(p => p[0]));
    for (let i = 0; i < this._pairs.length; i++) {
      const [v, val] = this._pairs[i];
      if (!otherDom.has(v)) out.push([v, val]);
    }
    return new Substitution(out);
  }

  /**
   * Debug check — O(|θ|²) in the worst case; gated behind
   * CALC_0216_SUBST_ASSERT so release builds don't pay for it.
   */
  _assertIdempotent() {
    const substitute = require('./substitute');
    for (let i = 0; i < this._pairs.length; i++) {
      const [, val] = this._pairs[i];
      const reapplied = substitute.apply(val, this._pairs);
      if (reapplied !== val) {
        throw new Error(
          `[0216-N] Substitution violates idempotence at entry ${i}: ` +
          `apply(val=${val}, θ) = ${reapplied} (θ=${JSON.stringify(this._pairs)})`
        );
      }
    }
  }
}

module.exports = { Substitution };
