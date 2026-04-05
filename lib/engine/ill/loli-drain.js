/**
 * Persistent-trigger loli drain optimization.
 *
 * Layer: ILL (Intuitionistic Linear Logic)
 *
 * Eagerly fires all persistent-trigger lolis in state before continuing
 * DFS exploration. Safe because persistent-trigger lolis consume only
 * themselves (the loli fact) and their guards depend only on persistent
 * state (which is never consumed).
 *
 * For 'guided' execution profile: evidenceOut collects per-firing records
 * { loliHash, match } — these become additional loli_l proof term nodes
 * interleaved between compiled rule steps in the explore tree.
 * NOTE: explore.js branch evidence attachment is deferred — the drain
 * evidence is collected here but not yet wired into explore tree proof terms.
 */

const Store = require('../../kernel/store');
const { GRADE_W } = require('../grades');
const { matchLoli } = require('../match');
const { mutateState } = require('../state-ops');
const { resolveConnectives } = require('../compile');

/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 */
function isPersistentTriggerLoli(h, rc) {
  if (Store.tag(h) !== rc.implication) return false;
  return isAllPersistentAntecedent(Store.child(h, 0), rc);
}

function isAllPersistentAntecedent(h, rc) {
  const t = Store.tag(h);
  if (t === rc.product) return isAllPersistentAntecedent(Store.child(h, 0), rc) && isAllPersistentAntecedent(Store.child(h, 1), rc);
  if (t === rc.exponential) {
    return Store.child(h, 0) === GRADE_W;
  }
  return false;
}

/**
 * Eagerly fire all persistent-trigger lolis in state.
 * Records all mutations in linArena/perArena for automatic undo.
 *
 * @param {Object} state - Mutable FactSet-based State
 * @param {Arena} linArena - Undo arena for linear FactSet
 * @param {Arena} perArena - Undo arena for persistent FactSet
 * @param {Object} calc - Calculus context (must have connectives)
 * @param {Array|null} evidenceOut - When non-null, pushes { loliHash, match } per firing
 * @param {Object} matchOpts - Match options (connectives for matchLoli)
 */
function drainPersistentLolis(state, linArena, perArena, calc, evidenceOut, matchOpts) {
  const rc = matchOpts?.connectives || (calc?.connectives ? resolveConnectives(calc.connectives) : null);
  if (!rc || !rc.implication) return;
  const loliTag = Store.TAG[rc.implication];
  const drainMatchOpts = matchOpts || (evidenceOut ? { evidence: true, connectives: rc } : { connectives: rc });
  let drained = true;
  while (drained) {
    drained = false;
    const loliGroup = state.linear.group(loliTag);
    const lolis = new Array(loliGroup.length);
    for (let i = 0; i < loliGroup.length; i++) lolis[i] = loliGroup[i];

    for (let i = 0; i < lolis.length; i++) {
      const h = lolis[i];
      if (!state.linear.has(loliTag, h)) continue;
      if (!isPersistentTriggerLoli(h, rc)) continue;
      const m = matchLoli(h, state, calc, drainMatchOpts);
      if (!m) continue;
      if (m.rule.consequentAlts.length > 1) continue;
      if (evidenceOut) evidenceOut.push({ loliHash: h, match: m });
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
