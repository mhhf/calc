/**
 * Focused Proof State
 *
 * Tracks state for focused proof search (Andreoli's focusing discipline).
 *
 * Phases:
 * - 'inversion': Eagerly apply invertible rules (no choice)
 * - 'focus': Decompose a chosen non-invertible formula
 *
 * Focus can be on:
 * - Right ('R'): A positive formula in the succedent
 * - Left ('L'): A negative formula in the linear context (by hash)
 */

class FocusedProofState {
  /**
   * @param {Object} opts
   * @param {'inversion'|'focus'} [opts.phase] - Current phase
   * @param {'L'|'R'|null} [opts.position] - Focus position
   * @param {string|null} [opts.focusHash] - Hash of focused formula (for left focus)
   */
  constructor(opts = {}) {
    this.phase = opts.phase || 'inversion';
    this.position = opts.position || null;
    this.focusHash = opts.focusHash || null;
  }

  /**
   * Deep copy state
   */
  copy() {
    return new FocusedProofState({
      phase: this.phase,
      position: this.position,
      focusHash: this.focusHash
    });
  }

  /**
   * Enter focus phase on a formula
   * @param {'L'|'R'} position - Left or right
   * @param {string|null} hash - Formula hash (for left focus)
   */
  focus(position, hash = null) {
    this.phase = 'focus';
    this.position = position;
    this.focusHash = hash;
  }

  /**
   * Exit focus phase (blur)
   */
  blur() {
    this.phase = 'inversion';
    this.position = null;
    this.focusHash = null;
  }

  /**
   * Check if in focus phase
   */
  isFocused() {
    return this.phase === 'focus';
  }

  /**
   * Check if in inversion phase
   */
  isInversion() {
    return this.phase === 'inversion';
  }

  /**
   * Check if focused on right
   */
  isFocusedRight() {
    return this.isFocused() && this.position === 'R';
  }

  /**
   * Check if focused on left
   */
  isFocusedLeft() {
    return this.isFocused() && this.position === 'L';
  }

  /**
   * For debugging
   */
  toString() {
    if (this.isInversion()) return 'inversion';
    return `focus(${this.position}${this.focusHash ? ':' + this.focusHash.slice(0, 8) : ''})`;
  }

  /**
   * Serialize to plain object
   */
  toJSON() {
    return {
      phase: this.phase,
      position: this.position,
      focusHash: this.focusHash
    };
  }
}

/**
 * Create inversion state
 */
function inversion() {
  return new FocusedProofState({ phase: 'inversion' });
}

/**
 * Create focus state
 */
function focus(position, hash = null) {
  return new FocusedProofState({
    phase: 'focus',
    position,
    focusHash: hash
  });
}

module.exports = {
  FocusedProofState,
  inversion,
  focus
};
