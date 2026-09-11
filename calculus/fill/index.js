/**
 * fill engine entry — the generic engine pre-bound to the fill calculus
 * config (ILL + μ/ν fixed points). Mirrors calculus/ill/index.js: callers
 * that mean "load this as fill" import THIS module; the API surface matches,
 * with the fill config filled in. An explicit opts.calculusConfig still wins
 * (spread order).
 *
 * fill exists to firewall the experimental μMALL / cyclic-proof frontier from
 * production ILL — μ/ν live here, not in ill.calc/ill.rules, so ILL's EVM
 * proof path carries no fixpoint machinery.
 */

'use strict';

import mde from '../../lib/engine/index.js';
import fillConfig from './calculus-config.js';
import { loadFill } from './lib/forward-parser.js';
import { createCalcAPI } from '../../lib/api.js';
import { classifyLeaf as _classifyLeaf, showInteresting as _showInteresting } from '../../lib/engine/show.js';

// Debug/inspection helpers pre-bound to ILL's EVM domain policy (inherited).
const classifyLeaf = (state) =>
  _classifyLeaf(state, fillConfig.domain.classifyLeafPolicy);
const showInteresting = (state, opts = {}) =>
  _showInteresting(state, { exclude: fillConfig.domain.showExclude, ...opts });

const load = (filePath, opts = {}) =>
  mde.load(filePath, { calculusConfig: fillConfig, ...opts });
const precompile = (filePaths, cachePath, opts = {}) =>
  mde.precompile(filePaths, cachePath, { calculusConfig: fillConfig, ...opts });
const loadPrecompiled = (cachePath, opts = {}) =>
  mde.loadPrecompiled(cachePath, { calculusConfig: fillConfig, ...opts });

const { hasMonad, decomposeQuery, prove, exec, createState,
  compileRule, Store, _composeCacheKey } = mde;

const parseExpr = (src) => mde.parseExpr(src, fillConfig.loader);

// ── fill backward-prover API (mirrors ILL's). loadFill loads the sequent
// calculus (fill.calc + [ill.rules, fill.rules]); the string helpers lazily
// build the shared CalcAPI over it. Synchronous, like ILL's. ──
let _api = null;
function _ensureInit() {
  if (!_api) _api = createCalcAPI(loadFill());
  return _api;
}
/** Prove a sequent string using fill */
function proveString(sequentStr, opts = {}) {
  return _ensureInit().proveString(sequentStr, opts);
}
/** Parse a formula string using fill */
function parseFormula(formulaStr) {
  return _ensureInit().parseFormula(formulaStr);
}
/** Parse a sequent string using fill */
function parseSequent(sequentStr) {
  return _ensureInit().parseSequent(sequentStr);
}
/** Render a formula/sequent as string */
function render(ast, format = 'ascii') {
  return _ensureInit().render(ast, format);
}

export {
  fillConfig,
  load,
  precompile,
  loadPrecompiled,
  loadFill,
  proveString,
  parseFormula,
  parseSequent,
  render,
  parseExpr,
  hasMonad,
  decomposeQuery,
  prove,
  exec,
  createState,
  compileRule,
  Store,
  _composeCacheKey,
  classifyLeaf,
  showInteresting,
};
export default {
  ...mde,
  fillConfig,
  load,
  precompile,
  loadPrecompiled,
  parseExpr,
  loadFill,
  proveString,
  parseFormula,
  parseSequent,
  render,
  classifyLeaf,
  showInteresting,
};
