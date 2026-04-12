/**
 * Existential resolution for LNL forward chaining.
 *
 * Layer: LNL (Linear-Non-Linear)
 *
 * Resolves existential variables (∃-quantified positions in consequents)
 * after linear matching succeeds. Resolution strategy:
 *   1. Per-goal: compiled FFI step (O(1), no term traversal) → fallback provePersistent
 *   2. Remaining unbound slots → freshEvar (symbolic witness)
 *
 * Existentials never block a rule from firing — freshEvar is the fallback.
 */

const { freshEvar } = require('../../kernel/fresh');
const { executeCompiledStep } = require('../opt/existential-compile');

// Reusable 1-element array for single-goal provePersistent calls
const _singleGoal = [0];

/**
 * Collect existential goals in consequent-persistent order.
 * Used as fallback when _existentialGoalOrder is not pre-computed.
 */
function _collectGoals(rule) {
  const goalSet = new Set();
  for (const slot of rule.existentialSlots) {
    const sg = rule.existentialGoals[slot];
    if (sg) for (const g of sg) goalSet.add(g);
  }
  const goals = [];
  for (const p of (rule.consequent.persistent || [])) {
    if (goalSet.has(p)) goals.push(p);
  }
  return goals;
}

/**
 * Resolve existential variables in theta after matching.
 *
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object} rule - Compiled rule with existentialSlots/existentialGoals
 * @param {Object} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, definitions, backchainIndex }
 * @param {Object} matchOpts - Match options with provePersistent callback
 * @returns {boolean} Always true — exists never blocks the rule
 */
function resolveExistentials(theta, slots, rule, state, calc, matchOpts) {
  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return true;

  // Use pre-computed goal order (from compileExistentialChain) or collect on demand
  const goals = rule._existentialGoalOrder || _collectGoals(rule);

  if (goals.length > 0) {
    const chain = rule._compiledExChain;
    const useCompiled = chain && matchOpts && matchOpts.useCompiledSteps
      && !matchOpts.onProveSuccess && !matchOpts.onProveFail && !matchOpts.evidence;
    const provePersistent = matchOpts && matchOpts.provePersistent;

    if (useCompiled) {
      // Per-step: try compiled FFI, fall back to provePersistent for that goal
      for (let i = 0; i < goals.length; i++) {
        const step = i < chain.length ? chain[i] : null;
        if (step && executeCompiledStep(step, theta, slots)) continue;
        if (provePersistent) {
          _singleGoal[0] = goals[i];
          provePersistent(_singleGoal, 0, theta, slots, state, calc, null, matchOpts);
        }
      }
    } else if (provePersistent) {
      provePersistent(goals, 0, theta, slots, state, calc, null, matchOpts);
    }
  }

  // Remaining unbound slots → freshEvar (symbolic witness)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;
}

module.exports = { resolveExistentials };
