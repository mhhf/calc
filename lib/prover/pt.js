/**
 * Generic Proof Tree
 *
 * Represents a proof tree node in automated proof search.
 * Prover-specific state goes in the `state` field.
 *
 * Uses content-addressed sequents for efficient resource tracking.
 */

const Seq = require('../kernel/sequent');

class ProofTree {
  /**
   * @param {Object} opts
   * @param {Object} opts.conclusion - Goal sequent
   * @param {ProofTree[]} [opts.premisses] - Child proof trees
   * @param {string} [opts.rule] - Applied rule name
   * @param {boolean} [opts.proven] - Whether this node is proven
   * @param {Object} [opts.delta_in] - Resources available (multiset snapshot)
   * @param {Object} [opts.delta_out] - Resources remaining after proof
   * @param {*} [opts.state] - Prover-specific state (e.g., FocusedProofState)
   */
  constructor(opts = {}) {
    this.conclusion = opts.conclusion;
    this.premisses = opts.premisses || [];
    this.rule = opts.rule || null;
    this.proven = opts.proven || false;

    // Resource tracking (content-addressed)
    // Format: { [hash]: { formula, count } }
    this.delta_in = opts.delta_in || {};
    this.delta_out = opts.delta_out || {};

    // Prover-specific state
    this.state = opts.state || null;
  }

  /**
   * Deep copy the proof tree
   */
  copy() {
    return new ProofTree({
      conclusion: this.conclusion ? Seq.copy(this.conclusion) : null,
      premisses: this.premisses.map(p => p.copy()),
      rule: this.rule,
      proven: this.proven,
      delta_in: copyDelta(this.delta_in),
      delta_out: copyDelta(this.delta_out),
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
   * Check if this is a leaf (no premisses)
   */
  isLeaf() {
    return this.premisses.length === 0;
  }

  /**
   * Check if entire subtree is proven
   */
  isComplete() {
    if (!this.proven) return false;
    return this.premisses.every(p => p.isComplete());
  }

  /**
   * Get all unproven goals in the tree (DFS)
   */
  getGoals() {
    if (this.isGoal()) return [this];
    return this.premisses.flatMap(p => p.getGoals());
  }

  /**
   * Count nodes in tree
   */
  size() {
    return 1 + this.premisses.reduce((sum, p) => sum + p.size(), 0);
  }

  /**
   * Get depth of tree
   */
  depth() {
    if (this.premisses.length === 0) return 1;
    return 1 + Math.max(...this.premisses.map(p => p.depth()));
  }

  /**
   * Convert to plain object (for debugging/serialization)
   */
  toJSON() {
    return {
      rule: this.rule,
      proven: this.proven,
      conclusion: summarizeSequent(this.conclusion),
      premisses: this.premisses.map(p => p.toJSON())
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
    for (const p of this.premisses) {
      s += p.toString(indent + 1);
    }
    return s;
  }
}

/**
 * Copy a delta (resource snapshot)
 */
function copyDelta(delta) {
  const result = {};
  for (const [h, entry] of Object.entries(delta)) {
    result[h] = {
      formula: require('../kernel/substitute').copy(entry.formula),
      count: entry.count
    };
  }
  return result;
}

/**
 * Summarize sequent as string (for debugging)
 */
function summarizeSequent(s) {
  if (!s) return '?';

  const linear = Seq.getContext(s, 'linear');
  const cart = Seq.getContext(s, 'cartesian');

  const linearStr = linear.length > 0
    ? linear.map(f => f?.tag || '?').join(', ')
    : '·';
  const cartStr = cart.length > 0
    ? cart.map(f => f?.tag || '?').join(', ') + ' ; '
    : '';
  const succStr = s.succedent?.tag || '?';

  return `${cartStr}${linearStr} ⊢ ${succStr}`;
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
    premisses: []
  });
}

module.exports = {
  ProofTree,
  fromGoal,
  leaf
};
