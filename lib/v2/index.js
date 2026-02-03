/**
 * v2 Calc API
 *
 * Main entry point for the refactored proof calculus system.
 *
 * Usage:
 *   const calc = require('./lib/v2');
 *   const ill = await calc.loadILL();
 *   const result = calc.prove(ill, [['A'], 'A']);
 */

const calculus = require('./calculus');
const prover = require('./prover');
const Seq = require('./kernel/sequent');
const { copy, apply } = require('./kernel/substitute');
const { unify, match } = require('./kernel/unify');
const { isAtomic, freeVars, contains, copy: copyAST } = require('./kernel/ast');

module.exports = {
  // Calculus loading
  load: calculus.load,
  loadILL: calculus.loadILL,

  // Proof search
  prove: prover.prove,
  createProver: prover.create,

  // Sequent operations
  Seq,

  // AST utilities
  ast: {
    copy: copyAST,
    isAtomic,
    freeVars,
    contains
  },

  // Substitution
  substitute: { copy, apply },

  // Unification
  unify: { unify, match }
};
