/**
 * rill engine entry — the generic engine pre-bound to the rill calculus config
 * (fill + the ○ next-time modality). Mirrors calculus/fill/index.js: callers
 * that mean "load this as rill" import THIS module; the API surface matches, with
 * the rill config filled in. An explicit opts.calculusConfig still wins.
 *
 * rill exists to firewall the experimental temporal / FRP frontier from fill's
 * audited μMALL core — ○ lives here, not in fill.calc/fill.rules, so fill stays a
 * clean, minimal ILL + μ/ν base.
 */

'use strict';

import mde from '../../lib/engine/index.js';
import rillConfig from './calculus-config.js';
import { loadRill } from './lib/forward-parser.js';
import { createCalcAPI } from '../../lib/api.js';
import { classifyLeaf as _classifyLeaf, showInteresting as _showInteresting } from '../../lib/engine/show.js';

// Debug/inspection helpers pre-bound to ILL's EVM domain policy (inherited).
const classifyLeaf = (state) =>
  _classifyLeaf(state, rillConfig.domain.classifyLeafPolicy);
const showInteresting = (state, opts = {}) =>
  _showInteresting(state, { exclude: rillConfig.domain.showExclude, ...opts });

const load = (filePath, opts = {}) =>
  mde.load(filePath, { calculusConfig: rillConfig, ...opts });
const precompile = (filePaths, cachePath, opts = {}) =>
  mde.precompile(filePaths, cachePath, { calculusConfig: rillConfig, ...opts });
const loadPrecompiled = (cachePath, opts = {}) =>
  mde.loadPrecompiled(cachePath, { calculusConfig: rillConfig, ...opts });

const { hasMonad, decomposeQuery, prove, exec, createState,
  compileRule, Store, _composeCacheKey } = mde;

const parseExpr = (src) => mde.parseExpr(src, rillConfig.loader);

// ── rill backward-prover API (mirrors fill's). loadRill loads the sequent
// calculus (rill.calc + [ill.rules, fill.rules, rill.rules]); the string helpers
// lazily build the shared CalcAPI over it. Synchronous, like fill's. ──
let _api = null;
function _ensureInit() {
  if (!_api) _api = createCalcAPI(loadRill());
  return _api;
}
/** Prove a sequent string using rill */
function proveString(sequentStr, opts = {}) {
  return _ensureInit().proveString(sequentStr, opts);
}
/** Parse a formula string using rill */
function parseFormula(formulaStr) {
  return _ensureInit().parseFormula(formulaStr);
}
/** Parse a sequent string using rill */
function parseSequent(sequentStr) {
  return _ensureInit().parseSequent(sequentStr);
}
/** Render a formula/sequent as string */
function render(ast, format = 'ascii') {
  return _ensureInit().render(ast, format);
}

export {
  rillConfig,
  load,
  precompile,
  loadPrecompiled,
  loadRill,
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
  rillConfig,
  load,
  precompile,
  loadPrecompiled,
  parseExpr,
  loadRill,
  proveString,
  parseFormula,
  parseSequent,
  render,
  classifyLeaf,
  showInteresting,
};
