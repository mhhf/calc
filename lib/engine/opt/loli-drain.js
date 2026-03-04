/**
 * Persistent-trigger loli drain optimization.
 *
 * Eagerly fires all persistent-trigger lolis in state before continuing
 * DFS exploration. Safe because persistent-trigger lolis consume only
 * themselves and guards depend only on persistent state.
 */

const Store = require('../../kernel/store');
const { matchLoli } = require('../match');
const { mutateState } = require('../state-ops');

/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 */
function isPersistentTriggerLoli(h, roles) {
  const loliTag = roles?.implication || 'loli';
  if (Store.tag(h) !== loliTag) return false;
  return isAllPersistentAntecedent(Store.child(h, 0), roles);
}

function isAllPersistentAntecedent(h, roles) {
  const t = Store.tag(h);
  const productTag = roles?.product || 'tensor';
  const bangTag = roles?.exponential || 'bang';
  if (t === productTag) return isAllPersistentAntecedent(Store.child(h, 0), roles) && isAllPersistentAntecedent(Store.child(h, 1), roles);
  if (t === bangTag) return true;
  return false;
}

/**
 * Eagerly fire all persistent-trigger lolis in state.
 * Records all mutations in linArena/perArena for automatic undo.
 *
 * @param {Object} state - Mutable FactSet-based State
 * @param {Arena} linArena - Undo arena for linear FactSet
 * @param {Arena} perArena - Undo arena for persistent FactSet
 * @param {Object} calc - Calculus context
 */
function drainPersistentLolis(state, linArena, perArena, calc) {
  const roles = calc?.roles;
  const loliTag = Store.TAG[roles?.implication || 'loli'];
  let drained = true;
  while (drained) {
    drained = false;
    const loliGroup = state.linear.group(loliTag);
    const lolis = new Array(loliGroup.length);
    for (let i = 0; i < loliGroup.length; i++) lolis[i] = loliGroup[i];

    for (let i = 0; i < lolis.length; i++) {
      const h = lolis[i];
      if (!state.linear.has(loliTag, h)) continue;
      if (!isPersistentTriggerLoli(h, roles)) continue;
      const m = matchLoli(h, state, calc);
      if (!m) continue;
      if (m.rule.consequentAlts.length > 1) continue;
      const alts = m.rule.consequentAlts;
      mutateState(state, m.consumed, m.theta,
        alts[0].linear, alts[0].persistent, m.slots, null, linArena, perArena);
      drained = true;
      break;
    }
  }
}

module.exports = {
  isPersistentTriggerLoli,
  isAllPersistentAntecedent,
  drainPersistentLolis,
};
