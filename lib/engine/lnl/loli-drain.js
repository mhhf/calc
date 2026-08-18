/**
 * Persistent-trigger loli drain optimization.
 *
 * Layer: LNL (Linear-Non-Linear)
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

import Store from '../../kernel/store.js';
import { defaultGradeConfig } from '../grades.js';
import { matchLoli } from './loli.js';
import { mutateState } from '../state-ops.js';
import { EMPTY_MATCH_OPTS } from '../match.js';
/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 * `gw` is the current gradeW() ID, hoisted by the caller — stable within a
 * single drain since the Store is never reindexed mid-execution.
 */
function isPersLoli(h, rc, gw) {
  if (Store.tag(h) !== rc.implication) return false;
  return isAllPersistentAntecedent(Store.child(h, 0), rc, gw);
}

function isAllPersistentAntecedent(h, rc, gw) {
  const t = Store.tag(h);
  if (t === rc.product) return isAllPersistentAntecedent(Store.child(h, 0), rc, gw) && isAllPersistentAntecedent(Store.child(h, 1), rc, gw);
  if (t === rc.exponential) {
    return Store.child(h, 0) === gw;
  }
  return false;
}

/**
 * Eagerly fire all persistent-trigger lolis in state.
 * Records all mutations in linArena/perArena for automatic undo.
 *
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts. EMPTY_MATCH_OPTS is the canonical empty default.
 *
 * @param {Object} state - Mutable FactSet-based State
 * @param {Arena} linArena - Undo arena for linear FactSet
 * @param {Arena} perArena - Undo arena for persistent FactSet
 * @param {Object} calc - Calculus context (must have connectives)
 * @param {Array|null} evidenceOut - When non-null, pushes { loliHash, match } per firing
 * @param {Object} [matchOpts] - Frozen match options (defaults to EMPTY_MATCH_OPTS)
 */
function drainLolis(state, linArena, perArena, calc, evidenceOut, matchOpts = EMPTY_MATCH_OPTS) {
  const rc = matchOpts.connectives;
  if (!rc || !rc.implication) return;
  const loliTag = Store.TAG[rc.implication];
  // hoisted: stable across this drain (no reindex mid-exec); the grade atom
  // comes from the resolved connectives record (calculus gradeConfig, default ILL)
  const gw = (rc.gradeOmega || defaultGradeConfig.gradeOmega)();
  let drained = true;
  while (drained) {
    drained = false;
    const loliGroup = state.linear.group(loliTag);
    const lolis = new Array(loliGroup.length);
    for (let i = 0; i < loliGroup.length; i++) lolis[i] = loliGroup[i];

    for (let i = 0; i < lolis.length; i++) {
      const h = lolis[i];
      if (!state.linear.has(loliTag, h)) continue;
      if (!isPersLoli(h, rc, gw)) continue;
      const m = matchLoli(h, state, calc, matchOpts);
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

export { drainLolis };
export default { drainLolis };
