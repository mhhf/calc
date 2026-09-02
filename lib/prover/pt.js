/**
 * Generic Proof Tree
 *
 * Represents a proof tree node in automated proof search.
 * Prover-specific state goes in the `state` field.
 *
 * Uses content-addressed sequents for efficient resource tracking.
 */

import Seq from '../kernel/sequent.js';
import Store from '../kernel/store.js';
class ProofTree {
  /**
   * @param {Object} opts
   * @param {Object} opts.conclusion - Goal sequent
   * @param {ProofTree[]} [opts.premises] - Child proof trees
   * @param {string} [opts.rule] - Applied rule name
   * @param {boolean} [opts.proven] - Whether this node is proven
   * @param {*} [opts.state] - Prover-specific state (e.g., FocusedProofState)
   */
  constructor(opts = {}) {
    this.conclusion = opts.conclusion;
    this.premises = opts.premises || [];
    this.rule = opts.rule || null;
    this.proven = opts.proven || false;

    // Prover-specific state
    this.state = opts.state || null;
  }

  /**
   * Deep copy the proof tree
   */
  copy() {
    return new ProofTree({
      conclusion: this.conclusion ? Seq.copy(this.conclusion) : null,
      premises: this.premises.map(p => p.copy()),
      rule: this.rule,
      proven: this.proven,
      state: this.state?.copy?.() ?? this.state
    });
  }

  /**
   * Check if this is an unproven goal (leaf that needs work)
   */
  isGoal() {
    return this.rule === null && !this.proven;
  }

  /**
   * Check if this is a leaf (no premises)
   */
  isLeaf() {
    return this.premises.length === 0;
  }

  /**
   * Check if entire subtree is proven
   */
  isComplete() {
    if (!this.proven) return false;
    return this.premises.every(p => p.isComplete());
  }

  /**
   * Convert to plain object (for debugging/serialization)
   */
  toJSON() {
    return {
      rule: this.rule,
      proven: this.proven,
      conclusion: summarizeSequent(this.conclusion),
      premises: this.premises.map(p => p.toJSON())
    };
  }

  /**
   * Render as string (simple format)
   */
  toString(indent = 0) {
    const pad = '  '.repeat(indent);
    const status = this.proven ? '✓' : (this.rule ? '?' : '○');
    const rule = this.rule || '???';
    const conc = summarizeSequent(this.conclusion);

    let s = `${pad}${status} [${rule}] ${conc}\n`;
    for (const p of this.premises) {
      s += p.toString(indent + 1);
    }
    return s;
  }
}

/**
 * Summarize sequent as string (for debugging — zone-name-agnostic)
 */
function summarizeSequent(s) {
  if (!s) return '?';

  // Render each context zone generically; last zone printed without separator
  const parts = Object.entries(s.contexts).map(([, ctx]) =>
    ctx.length > 0 ? ctx.map(f => Store.tag(f) || '?').join(', ') : '·'
  );
  const succStr = Store.tag(s.succedent) || '?';

  return `${parts.join(' ; ')} ⊢ ${succStr}`;
}

/**
 * Create proof tree from goal sequent
 */
function fromGoal(sequent) {
  return new ProofTree({ conclusion: sequent });
}

/**
 * Create leaf (axiom) proof tree
 */
function leaf(sequent, rule) {
  return new ProofTree({
    conclusion: sequent,
    rule,
    proven: true,
    premises: []
  });
}

export { ProofTree, fromGoal, leaf };
export default { ProofTree, fromGoal, leaf };
