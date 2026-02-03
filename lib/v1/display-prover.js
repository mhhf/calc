/**
 * DisplayProver - Generic Display Calculus Prover
 *
 * A theory-compliant prover that:
 * - Works with TreeSequent (tree-based representation)
 * - Uses display postulates to "display" formulas before rule application
 * - Supports both DFS and BFS search strategies
 * - No optimizations (faithful to display calculus theory)
 *
 * Key concepts:
 * - Display property: Any subformula can be "displayed" (isolated) using structural rules
 * - Structural rules: Exchange, associativity, unit, contraction, weakening
 * - Logical rules: Only apply to displayed formulas
 *
 * The display calculus approach:
 * 1. Check if a logical rule directly matches the goal
 * 2. If not, apply structural rules to display the active formula
 * 3. Apply the logical rule
 * 4. Recursively prove premises
 */

const { profiler } = require('./profiler.js');
const { TreeSequent, LNLTreeSequent } = require('./sequent-tree.js');

/**
 * Search strategy enum
 */
const SearchStrategy = {
  DFS: 'dfs',  // Depth-first search (less memory, may not terminate)
  BFS: 'bfs'   // Breadth-first search (more memory, complete)
};

/**
 * Proof step in the search tree
 */
class ProofStep {
  constructor(sequent, ruleName = null, premises = [], parent = null) {
    this.sequent = sequent;
    this.ruleName = ruleName;
    this.premises = premises;
    this.parent = parent;
    this.proved = false;
  }

  /**
   * Check if this is a leaf (axiom or stuck)
   */
  isLeaf() {
    return this.premises.length === 0;
  }

  /**
   * Mark this step and propagate proof status up
   */
  markProved() {
    this.proved = true;
    if (this.parent && this.parent.allPremisesProved()) {
      this.parent.markProved();
    }
  }

  /**
   * Check if all premises are proved
   */
  allPremisesProved() {
    return this.premises.every(p => p.proved);
  }
}

/**
 * Generic Display Calculus Prover
 */
class DisplayProver {
  /**
   * Create a display prover
   *
   * @param {Object} options
   * @param {string} options.strategy - Search strategy ('dfs' or 'bfs')
   * @param {number} options.maxDepth - Maximum search depth (default: 100)
   * @param {Object} options.calc - Calculus database with rules
   * @param {Object} options.structuralRules - Structural rules (display postulates)
   * @param {Object} options.logicalRules - Logical rules
   */
  constructor(options = {}) {
    this.strategy = options.strategy || SearchStrategy.DFS;
    this.maxDepth = options.maxDepth || 100;
    this.calc = options.calc || null;
    this.structuralRules = options.structuralRules || {};
    this.logicalRules = options.logicalRules || {};
    this.debug = options.debug || false;
  }

  /**
   * Main proof search entry point
   *
   * @param {TreeSequent} goal - The goal sequent to prove
   * @returns {Object} - { success, proofTree, steps, debug }
   */
  prove(goal) {
    profiler.count('display-prover.prove');
    const endTime = profiler.time('display-prover.prove');

    const root = new ProofStep(goal);
    const result = this.strategy === SearchStrategy.BFS
      ? this.proveBFS(root)
      : this.proveDFS(root, 0);

    endTime();
    return {
      success: root.proved,
      proofTree: root,
      steps: this.countSteps(root),
      debug: this.debug ? this.collectDebug(root) : null
    };
  }

  /**
   * Depth-first search proof strategy
   */
  proveDFS(step, depth) {
    if (depth > this.maxDepth) {
      return false;
    }

    profiler.count('display-prover.dfs.step');

    // 1. Try to close with identity/axiom
    if (this.tryIdentity(step)) {
      step.markProved();
      return true;
    }

    // 2. Get applicable rules (logical + structural)
    const actions = this.getApplicableActions(step);

    // 3. Try each action
    for (const action of actions) {
      const newStep = this.applyAction(step, action);
      if (!newStep) continue;

      // Create premise steps
      step.ruleName = action.ruleName;
      step.premises = newStep.premises.map(seq =>
        new ProofStep(seq, null, [], step)
      );

      // Recursively prove all premises
      let allProved = true;
      for (const premise of step.premises) {
        if (!this.proveDFS(premise, depth + 1)) {
          allProved = false;
          break;
        }
      }

      if (allProved) {
        step.markProved();
        return true;
      }

      // Backtrack: clear premises
      step.premises = [];
      step.ruleName = null;
    }

    return false;
  }

  /**
   * Breadth-first search proof strategy
   */
  proveBFS(root) {
    profiler.count('display-prover.bfs.start');

    // Queue of (step, depth) pairs
    const queue = [{ step: root, depth: 0 }];
    const visited = new Set();

    while (queue.length > 0) {
      const { step, depth } = queue.shift();

      if (depth > this.maxDepth) continue;

      // Skip if already visited (by sequent hash)
      const hash = step.sequent.getHash().toString();
      if (visited.has(hash)) continue;
      visited.add(hash);

      profiler.count('display-prover.bfs.step');

      // Try identity
      if (this.tryIdentity(step)) {
        step.markProved();
        if (root.proved) return true;
        continue;
      }

      // Get applicable actions
      const actions = this.getApplicableActions(step);

      for (const action of actions) {
        const newStep = this.applyAction(step, action);
        if (!newStep) continue;

        // Create premise steps and add to queue
        step.ruleName = action.ruleName;
        step.premises = newStep.premises.map(seq =>
          new ProofStep(seq, null, [], step)
        );

        for (const premise of step.premises) {
          queue.push({ step: premise, depth: depth + 1 });
        }
      }
    }

    return root.proved;
  }

  /**
   * Try to close the goal with identity rule
   * Identity: A ⊢ A (formula on both sides match)
   */
  tryIdentity(step) {
    const seq = step.sequent;

    // For TreeSequent: check if antecedent equals succedent
    if (seq instanceof LNLTreeSequent) {
      // LNL identity: · ; A ⊢ A
      // Cartesian must be empty, linear must be exactly A
      if (!this.isEmpty(seq.cartesian)) return false;
      if (!this.treesEqual(seq.linear, seq.succedent)) return false;
      step.ruleName = 'Id';
      return true;
    } else {
      // Simple identity: A ⊢ A
      if (!this.treesEqual(seq.antecedent, seq.succedent)) return false;
      step.ruleName = 'Id';
      return true;
    }
  }

  /**
   * Check if a structure tree is empty (unit element)
   */
  isEmpty(tree) {
    if (!tree) return true;
    if (typeof tree === 'string') return tree === '' || tree === 'I' || tree === '·';
    if (tree.id && this.calc) {
      const rule = this.calc.rules[tree.id];
      if (rule && (rule.ruleName.includes('Empty') || rule.ruleName.includes('Neutral'))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check if two trees are structurally equal
   */
  treesEqual(t1, t2) {
    if (t1 === t2) return true;
    if (!t1 || !t2) return false;

    // Use hash comparison if available
    if (t1.hash && t2.hash) {
      return t1.hash === t2.hash;
    }

    // Structural comparison
    if (t1.id !== t2.id) return false;
    if (!t1.vals || !t2.vals) return t1 === t2;
    if (t1.vals.length !== t2.vals.length) return false;

    for (let i = 0; i < t1.vals.length; i++) {
      if (!this.treesEqual(t1.vals[i], t2.vals[i])) return false;
    }
    return true;
  }

  /**
   * Get all applicable actions for the current step
   * Returns both logical rules and structural rules (display postulates)
   */
  getApplicableActions(step) {
    const actions = [];

    // 1. Try logical rules that match directly
    for (const [name, rule] of Object.entries(this.logicalRules)) {
      if (this.ruleMatches(step.sequent, rule)) {
        actions.push({ type: 'logical', ruleName: name, rule });
      }
    }

    // 2. Try structural rules to enable other matches
    for (const [name, rule] of Object.entries(this.structuralRules)) {
      if (this.structuralRuleApplicable(step.sequent, rule)) {
        actions.push({ type: 'structural', ruleName: name, rule });
      }
    }

    return actions;
  }

  /**
   * Check if a logical rule matches the current sequent
   * (This is a placeholder - actual implementation depends on rule format)
   */
  ruleMatches(sequent, rule) {
    // TODO: Implement pattern matching against rule conclusion
    // This requires unification of the sequent with the rule's conclusion
    return false;
  }

  /**
   * Check if a structural rule can be applied
   */
  structuralRuleApplicable(sequent, rule) {
    // TODO: Implement structural rule applicability check
    return false;
  }

  /**
   * Apply an action (rule application) to a proof step
   */
  applyAction(step, action) {
    profiler.count(`display-prover.apply.${action.type}`);

    // TODO: Implement actual rule application
    // This returns { premises: [TreeSequent, ...] }
    return null;
  }

  /**
   * Count total steps in proof tree
   */
  countSteps(step) {
    let count = 1;
    for (const premise of step.premises) {
      count += this.countSteps(premise);
    }
    return count;
  }

  /**
   * Collect debug info from proof tree
   */
  collectDebug(step, depth = 0) {
    return {
      depth,
      sequent: step.sequent.toString(),
      rule: step.ruleName,
      proved: step.proved,
      premises: step.premises.map(p => this.collectDebug(p, depth + 1))
    };
  }
}

// =============================================================================
// Specialized LNL Display Prover
// =============================================================================

/**
 * LNL Display Prover - specialized for LNL family
 *
 * Handles the 3-arg sequent (Γ ; Δ ⊢ A) with:
 * - Cartesian structural rules (exchange, assoc, unit, contraction, weakening)
 * - Linear structural rules (exchange, assoc, unit)
 * - Bridge rules between modes (F ⊣ G adjunction)
 */
class LNLDisplayProver extends DisplayProver {
  constructor(options = {}) {
    super(options);
    this.cartesianRules = options.cartesianRules || {};
    this.linearRules = options.linearRules || {};
    this.bridgeRules = options.bridgeRules || {};
  }

  /**
   * Get applicable actions for LNL sequent
   */
  getApplicableActions(step) {
    const actions = super.getApplicableActions(step);

    // Add mode-specific structural rules
    const seq = step.sequent;
    if (seq instanceof LNLTreeSequent) {
      // Cartesian structural rules
      for (const [name, rule] of Object.entries(this.cartesianRules)) {
        if (this.structuralRuleApplicable(seq.cartesian, rule)) {
          actions.push({ type: 'cartesian-structural', ruleName: name, rule });
        }
      }

      // Linear structural rules
      for (const [name, rule] of Object.entries(this.linearRules)) {
        if (this.structuralRuleApplicable(seq.linear, rule)) {
          actions.push({ type: 'linear-structural', ruleName: name, rule });
        }
      }

      // Bridge rules
      for (const [name, rule] of Object.entries(this.bridgeRules)) {
        if (this.bridgeRuleApplicable(seq, rule)) {
          actions.push({ type: 'bridge', ruleName: name, rule });
        }
      }
    }

    return actions;
  }

  /**
   * Check if a bridge rule (between modes) is applicable
   */
  bridgeRuleApplicable(sequent, rule) {
    // TODO: Implement bridge rule applicability
    return false;
  }
}

// =============================================================================
// Exports
// =============================================================================

module.exports = {
  DisplayProver,
  LNLDisplayProver,
  ProofStep,
  SearchStrategy
};
