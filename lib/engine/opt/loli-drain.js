/**
 * Persistent-trigger loli drain optimization.
 *
 * Eagerly fires all persistent-trigger lolis in state before continuing
 * DFS exploration. Safe because persistent-trigger lolis consume only
 * themselves and guards depend only on persistent state.
 */

const Store = require('../../kernel/store');
const { matchLoli } = require('../match');

const _TAG_LOLI = Store.TAG.loli;

/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 */
function isPersistentTriggerLoli(h) {
  if (Store.tagId(h) !== _TAG_LOLI) return false;
  return isAllPersistentAntecedent(Store.child(h, 0));
}

function isAllPersistentAntecedent(h) {
  const t = Store.tag(h);
  if (t === 'tensor') return isAllPersistentAntecedent(Store.child(h, 0)) && isAllPersistentAntecedent(Store.child(h, 1));
  if (t === 'bang') return true;
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
 * @param {Function} mutateState - State mutation function
 */
function drainPersistentLolis(state, linArena, perArena, calc, mutateState) {
  let drained = true;
  while (drained) {
    drained = false;
    const loliGroup = state.linear.group(_TAG_LOLI);
    const lolis = new Array(loliGroup.length);
    for (let i = 0; i < loliGroup.length; i++) lolis[i] = loliGroup[i];

    for (let i = 0; i < lolis.length; i++) {
      const h = lolis[i];
      if (!state.linear.has(_TAG_LOLI, h)) continue;
      if (!isPersistentTriggerLoli(h)) continue;
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
