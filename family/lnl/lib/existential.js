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

import { freshEvar } from '../../../lib/kernel/fresh.js';
import { EMPTY_MATCH_OPTS } from '../../../lib/engine/match.js';
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
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts. EMPTY_MATCH_OPTS is the canonical empty default.
 *
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object} rule - Compiled rule with existentialSlots/existentialGoals
 * @param {Object} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, definitions, backchainIndex }
 * @param {Object} [matchOpts] - Frozen match options (defaults to EMPTY_MATCH_OPTS)
 * @returns {boolean} Always true — exists never blocks the rule
 */
function resolveEx(theta, slots, rule, state, calc, matchOpts = EMPTY_MATCH_OPTS) {
  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return true;

  // Use pre-computed goal order (from compileExChain) or collect on demand
  const goals = rule._existentialGoalOrder || _collectGoals(rule);

  if (goals.length > 0) {
    const chain = rule._compiledExChain;
    const _execExStep = matchOpts.execExStep;
    const useCompiled = chain && _execExStep && matchOpts.useCompiledSteps
      && !matchOpts.onProveSuccess && !matchOpts.onProveFail && !matchOpts.evidence;
    const provePersistent = matchOpts.provePersistent;

    // One loop for every mode (compiled fast path differs only in trying the
    // compiled FFI step first) — modes must not diverge semantically.
    for (let i = 0; i < goals.length; i++) {
      let proved = false;
      const step = useCompiled && i < chain.length ? chain[i] : null;
      if (step && _execExStep(step, theta, slots)) {
        proved = true;
      } else if (provePersistent) {
        _singleGoal[0] = goals[i];
        proved = provePersistent(_singleGoal, 0, theta, slots, state, calc, null, matchOpts) === 1;
      }
      if (!proved) {
        // Eager eigenvariable introduction (TODO_0307): a goal that failed to
        // determine its ∃-outputs freshens them NOW. Later goals then see an
        // opaque evar — never an open pattern slot, which every tier would
        // treat as a wildcard and resolve against an arbitrary stored fact.
        for (const slot of rule.existentialSlots) {
          if (theta[slot] !== undefined) continue;
          const sg = rule.existentialGoals[slot];
          if (sg && sg.includes(goals[i])) theta[slot] = freshEvar();
        }
      }
    }
  }

  // Remaining unbound slots → freshEvar (symbolic witness)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;
}

export { resolveEx };
export default { resolveEx };
