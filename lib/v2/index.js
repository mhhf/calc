/**
 * v2 Calc API
 *
 * Main entry point for the refactored proof calculus system.
 *
 * Usage:
 *   const calc = require('./lib/v2');
 *
 *   // Load calculus and prove
 *   const ill = await calc.loadILL();
 *   const result = calc.prove(ill, [['A'], 'A']);
 *
 *   // Or use CLI-style string parsing
 *   const result = await calc.proveString('P, P -o Q |- Q');
 */

const calculus = require('./calculus');
const prover = require('./prover');
const Seq = require('./kernel/sequent');
const { copy, apply } = require('./kernel/substitute');
const { unify, match } = require('./kernel/unify');
const { isAtomic, freeVars, contains, copy: copyAST } = require('./kernel/ast');
const { createSequentParser } = require('./parser/sequent-parser');

// Cached ILL instance
let cachedILL = null;

/**
 * Prove a sequent string using ILL
 * @param {string} sequentStr - e.g., "P, P -o Q |- Q"
 * @param {Object} [opts] - { maxDepth, debug }
 * @returns {Promise<{ success, proofTree, sequent }>}
 */
async function proveString(sequentStr, opts = {}) {
  if (!cachedILL) {
    cachedILL = await calculus.loadILL();
  }

  const sp = createSequentParser(cachedILL);
  const seq = sp.parseSequent(sequentStr);

  const p = prover.create(cachedILL);
  const result = p.prove(seq, opts);

  return {
    ...result,
    sequent: seq,
    formatted: sp.formatSequent(seq)
  };
}

/**
 * Parse a formula string using ILL
 * @param {string} formulaStr - e.g., "A * B -o C"
 * @returns {Promise<Object>} AST
 */
async function parseFormula(formulaStr) {
  if (!cachedILL) {
    cachedILL = await calculus.loadILL();
  }
  return cachedILL.parse(formulaStr);
}

/**
 * Parse a sequent string using ILL
 * @param {string} sequentStr - e.g., "A, B |- C"
 * @returns {Promise<Object>} Sequent object
 */
async function parseSequent(sequentStr) {
  if (!cachedILL) {
    cachedILL = await calculus.loadILL();
  }
  const sp = createSequentParser(cachedILL);
  return sp.parseSequent(sequentStr);
}

/**
 * Render a formula/sequent as string
 * @param {Object} ast - Formula or sequent
 * @param {string} format - 'ascii' or 'latex'
 * @returns {Promise<string>}
 */
async function render(ast, format = 'ascii') {
  if (!cachedILL) {
    cachedILL = await calculus.loadILL();
  }

  // If it's a sequent, format it
  if (ast?.succedent) {
    const sp = createSequentParser(cachedILL);
    // For latex, we'd need to add latex formatting support
    return sp.formatSequent(ast, format);
  }

  // Otherwise it's a formula
  return cachedILL.render(ast, format);
}

module.exports = {
  // Calculus loading
  load: calculus.load,
  loadILL: calculus.loadILL,

  // High-level CLI-compatible API
  proveString,
  parseFormula,
  parseSequent,
  render,

  // Proof search
  prove: prover.prove,
  createProver: prover.create,

  // Sequent operations
  Seq,

  // Parser
  createSequentParser,

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
