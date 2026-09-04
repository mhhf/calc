/**
 * Prover API
 *
 * High-level interface for proof search.
 * Uses focused proof search (Andreoli's focusing) for efficiency.
 */

import { createProver } from '../focused.js';
import { initRuleSpecs } from '../rule-interpreter.js';
import Seq from '../../kernel/sequent.js';
/**
 * Create a prover for a calculus
 * @param {Object} calculus - Loaded calculus from lib/calculus
 * @returns {Object} Prover with prove() method
 */
function create(calculus) {
  const focused = createProver(calculus);
  const { specs: ruleSpecs, alternatives } = initRuleSpecs(calculus);

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
    const ctxStruct = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
    const CZ = ctxStruct.consumableZone;
    const SZ = ctxStruct.copySource;
    const [linear, succ] = goal;
    const linearFormulas = linear.map(f =>
      typeof f === 'string' ? calculus.parse(f) : f
    );
    const succFormula = typeof succ === 'string' ? calculus.parse(succ) : succ;
    // Wrapper-routed consumable columns (TODO_0285); single-zone calculi
    // get { [CZ]: linearFormulas } unchanged.
    return Seq.seq({ ...Seq.routeContexts(ctxStruct, linearFormulas), [SZ]: [] }, succFormula);
  }

  throw new Error('Invalid goal: expected sequent or [linearCtx, succedent]');
}

export { create, prove };
export default { create, prove };
