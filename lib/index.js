/**
 * Calc API — Node.js Entry Point (calculus-generic)
 *
 * Generic prover/kernel surface over lib/api.js. Holds NO calculus:
 * ILL-implicit conveniences (loadILL, proveString, parseFormula,
 * parseSequent, render) live on the ILL facade — calculus/ill/index.js
 * (TODO_0086: lib/ knows no calculus location).
 *
 * Usage:
 *   import { loadILL, proveString } from './calculus/ill/index.js';
 *   import calc from './lib/index.js';
 *   const ill = loadILL();
 *   const result = calc.prove(ill, [['A'], 'A']);
 */

import calculus from './calculus/index.js';
import prover from './prover/strategy/auto.js';
import { createCalcAPI } from './api.js';
import Seq from './kernel/sequent.js';
import { copy, apply } from './kernel/substitute.js';
import { unify, match } from './kernel/unify.js';
import { isAtomic, freeVars, copy as copyAST } from './kernel/ast.js';
import { sequentParser } from './parser/sequent-parser.js';

const load = calculus.load;
const prove = prover.prove;
const createProver = prover.create;
const ast = { copy: copyAST, isAtomic, freeVars };
const substitute = { copy, apply };
const unifyNS = { unify, match };

export {
  load,
  createCalcAPI,
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
  createCalcAPI,
  prove,
  createProver,
  Seq,
  sequentParser,
  ast,
  substitute,
  unify: unifyNS,
};
