/**
 * Existential resolution for LNL forward chaining.
 *
 * Layer: LNL (Linear-Non-Linear)
 *
 * Resolves existential variables (∃-quantified positions in consequents)
 * after linear matching succeeds. Resolution strategy:
 *   1. Prove existential goals via provePersistent (state → clause resolution)
 *   2. Remaining unbound slots → freshEvar (symbolic witness)
 *
 * Existentials never block a rule from firing — freshEvar is the fallback.
 */

const { freshEvar } = require('../../kernel/fresh');

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

  // Collect existential goals in consequent-persistent order (preserves dependency chain).
  const goalSet = new Set();
  for (const slot of rule.existentialSlots) {
    const sg = rule.existentialGoals[slot];
    if (sg) for (const g of sg) goalSet.add(g);
  }
  const goals = [];
  for (const p of (rule.consequent.persistent || [])) {
    if (goalSet.has(p)) goals.push(p);
  }

  // Prove goals via provePersistent callback
  if (goals.length > 0 && matchOpts && matchOpts.provePersistent) {
    matchOpts.provePersistent(goals, 0, theta, slots, state, calc);
  }

  // Remaining unbound slots → freshEvar (symbolic witness)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;
}

module.exports = { resolveExistentials };
