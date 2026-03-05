/**
 * Constraint solver integration for branch pruning.
 *
 * Wraps EqNeqSolver lifecycle in explore: seeding, feeding persistent
 * facts from arena, and SAT-filtering oplus alternatives.
 *
 * EqNeqSolver class stays in lib/engine/constraint.js (general data structure).
 */

const { applyIndexed: subApplyIdx } = require('../../kernel/substitute');
const { INSERT_OP } = require('../fact-set');

/**
 * Feed newly-added persistent facts from perArena into the solver.
 * Reads arena records from checkpoint to current cursor, looking for INSERT ops.
 *
 * @param {EqNeqSolver} solver - Constraint solver
 * @param {Arena} perArena - Persistent FactSet arena
 * @param {number} checkpoint - Arena checkpoint before mutation
 */
function feedPersistent(solver, perArena, checkpoint) {
  const buf = perArena.buf;
  for (let i = checkpoint; i < perArena.cursor; i += 4) {
    if (buf[i] === INSERT_OP) {
      solver.addConstraint(buf[i + 2]); // hash is at offset +2
    }
  }
}

/**
 * SAT-filter oplus alternatives via constraint solver.
 * Returns array of surviving alternative indices.
 *
 * @param {EqNeqSolver} solver - Constraint solver
 * @param {Object[]} alts - Consequent alternatives
 * @param {Array} theta - Substitution bindings
 * @param {Object} slots - Metavar slot mapping
 * @returns {number[]} Indices of SAT alternatives
 */
function filterAltsBySAT(solver, alts, theta, slots) {
  const satAlts = [];
  for (let i = 0; i < alts.length; i++) {
    const scp = solver.checkpoint();
    for (const pattern of alts[i].persistent) {
      const h = subApplyIdx(pattern, theta, slots);
      solver.addConstraint(h);
    }
    if (solver.checkSAT()) satAlts.push(i);
    solver.restore(scp);
  }
  return satAlts;
}

module.exports = {
  feedPersistent,
  filterAltsBySAT,
};
