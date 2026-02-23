/**
 * Calc API — Node.js Entry Point
 *
 * Thin wrapper over lib/api.js — loads calculus from .calc/.rules files
 * then delegates to the shared API facade.
 *
 * Usage:
 *   const calc = require('./lib');
 *   const ill = await calc.loadILL();
 *   const result = calc.prove(ill, [['A'], 'A']);
 *   // Or: const result = await calc.proveString('P, P -o Q |- Q');
 */

const calculus = require('./calculus');
const prover = require('./prover');
const { createCalcAPI } = require('./api');
const Seq = require('./kernel/sequent');
const { copy, apply } = require('./kernel/substitute');
const { unify, match } = require('./kernel/unify');
const { isAtomic, freeVars, copy: copyAST } = require('./kernel/ast');
const { createSequentParser } = require('./parser/sequent-parser');

// Cached API instance (lazy-loaded from filesystem)
let _api = null;

async function ensureInit() {
  if (!_api) {
    const ill = await calculus.loadILL();
    _api = createCalcAPI(ill);
  }
  return _api;
}

/** Prove a sequent string using ILL */
async function proveString(sequentStr, opts = {}) {
  return (await ensureInit()).proveString(sequentStr, opts);
}

/** Parse a formula string using ILL */
async function parseFormula(formulaStr) {
  return (await ensureInit()).parseFormula(formulaStr);
}

/** Parse a sequent string using ILL */
async function parseSequent(sequentStr) {
  return (await ensureInit()).parseSequent(sequentStr);
}

/** Render a formula/sequent as string */
async function render(ast, format = 'ascii') {
  return (await ensureInit()).render(ast, format);
}

module.exports = {
  // Calculus loading
  load: calculus.load,
  loadILL: calculus.loadILL,

  // High-level CLI-compatible API (async, lazy-loads ILL)
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
  ast: { copy: copyAST, isAtomic, freeVars },

  // Substitution
  substitute: { copy, apply },

  // Unification
  unify: { unify, match }
};
