/**
 * Prover API
 *
 * High-level interface for proof search.
 * Uses focused proof search (Andreoli's focusing) for efficiency.
 */

const { createProver, buildRuleSpecs } = require('../focused');
const { buildRuleSpecsFromMeta } = require('../rule-interpreter');
const Seq = require('../../kernel/sequent');

/**
 * Create a prover for a calculus
 * @param {Object} calculus - Loaded calculus from lib/calculus
 * @returns {Object} Prover with prove() method
 */
function create(calculus) {
  const focused = createProver(calculus);
  // Use precomputed rule spec meta if available, otherwise compute from scratch
  const { specs: ruleSpecs, alternatives } = calculus.ruleSpecMeta
    ? buildRuleSpecsFromMeta(calculus.ruleSpecMeta, calculus.rules)
    : buildRuleSpecs(calculus);

  return {
    /**
     * Prove a sequent
     * @param {Object|string[]} goal - Sequent or [linearCtx, succedent]
     * @param {Object} [opts] - { maxDepth }
     * @returns {{ success: boolean, proofTree?: ProofTree }}
     */
    prove(goal, opts = {}) {
      // Normalize goal to sequent
      const seq = normalizeGoal(goal, calculus);
      return focused.prove(seq, { rules: ruleSpecs, alternatives, ...opts });
    },

    // Expose internals for debugging/testing
    findInvertible: focused.findInvertible,
    chooseFocus: focused.chooseFocus,
    tryIdentity: focused.tryIdentity,
    ruleSpecs
  };
}

/**
 * Shorthand: prove a goal directly (creates ephemeral prover)
 * @param {Object} calculus - Loaded calculus
 * @param {Object|string[]} goal - Sequent or [linearCtx, succedent]
 * @param {Object} [opts] - { maxDepth }
 */
function prove(calculus, goal, opts = {}) {
  return create(calculus).prove(goal, opts);
}

/**
 * Normalize goal to sequent object
 */
function normalizeGoal(goal, calculus) {
  // Already a sequent
  if (goal?.succedent) return goal;

  // Array format: [linearFormulas, succedent]
  if (Array.isArray(goal) && goal.length === 2) {
    const [linear, succ] = goal;
    const linearFormulas = linear.map(f =>
      typeof f === 'string' ? calculus.parse(f) : f
    );
    const succFormula = typeof succ === 'string' ? calculus.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  }

  throw new Error('Invalid goal: expected sequent or [linearCtx, succedent]');
}

module.exports = { create, prove };
