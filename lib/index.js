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

import calculus from './calculus/index.js';
import prover from './prover/strategy/auto.js';
import { createCalcAPI } from './api.js';
import Seq from './kernel/sequent.js';
import { copy, apply } from './kernel/substitute.js';
import { unify, match } from './kernel/unify.js';
import { isAtomic, freeVars, copy as copyAST } from './kernel/ast.js';
import { sequentParser } from './parser/sequent-parser.js';
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

const load = calculus.load;
const loadILL = calculus.loadILL;
const prove = prover.prove;
const createProver = prover.create;
const ast = { copy: copyAST, isAtomic, freeVars };
const substitute = { copy, apply };
const unifyNS = { unify, match };

export {
  load,
  loadILL,
  proveString,
  parseFormula,
  parseSequent,
  render,
  prove,
  createProver,
  Seq,
  sequentParser,
  ast,
  substitute,
  unifyNS as unify,
};

export default {
  load,
  loadILL,
  proveString,
  parseFormula,
  parseSequent,
  render,
  prove,
  createProver,
  Seq,
  sequentParser,
  ast,
  substitute,
  unify: unifyNS,
};
