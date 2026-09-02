/**
 * ILL engine entry — the generic engine pre-bound to the ILL calculus
 * config (audit 2026-09-02). mde.load/precompile/loadPrecompiled require
 * an explicit opts.calculusConfig; the engine holds no default. Callers
 * that mean "load this as ILL" import THIS module instead of
 * lib/engine/index.js — same API surface, config filled in. An explicit
 * opts.calculusConfig still wins (spread order), so mixed-calculus
 * callers keep working.
 *
 * normalizeQuery (EVM bytecode-normalizing query decomposition) is
 * re-exported here — it is ILL domain machinery, not generic engine API.
 */

'use strict';

import mde from '../../lib/engine/index.js';
import illConfig from './calculus-config.js';
import { normalizeQuery } from './lib/bytecode-normalize.js';
import { loadILL } from './lib/forward-parser.js';
import { createCalcAPI } from '../../lib/api.js';

const load = (filePath, opts = {}) =>
  mde.load(filePath, { calculusConfig: illConfig, ...opts });
const precompile = (filePaths, cachePath, opts = {}) =>
  mde.precompile(filePaths, cachePath, { calculusConfig: illConfig, ...opts });
const loadPrecompiled = (cachePath, sellOpts = {}) =>
  mde.loadPrecompiled(cachePath, { calculusConfig: illConfig, ...sellOpts });

const { hasMonad, decomposeQuery, prove, exec, createState,
  compileRule, Store, _composeCacheKey } = mde;

// parseExpr bound to ILL's loader config (the engine's parseExpr requires
// an explicit loaderConfig since TODO_0086 — no baked-in calculus parser).
const parseExpr = (src) => mde.parseExpr(src, illConfig.loader);

// ── ILL-implicit backward-prover API (moved from lib/index.js,
// TODO_0086: lib/ holds no calculus paths). loadILL loads the sequent
// calculus (ill.calc + ill.rules); the string helpers lazily build the
// shared CalcAPI over it.
let _api = null;
async function _ensureInit() {
  if (!_api) _api = createCalcAPI(loadILL());
  return _api;
}
/** Prove a sequent string using ILL */
async function proveString(sequentStr, opts = {}) {
  return (await _ensureInit()).proveString(sequentStr, opts);
}
/** Parse a formula string using ILL */
async function parseFormula(formulaStr) {
  return (await _ensureInit()).parseFormula(formulaStr);
}
/** Parse a sequent string using ILL */
async function parseSequent(sequentStr) {
  return (await _ensureInit()).parseSequent(sequentStr);
}
/** Render a formula/sequent as string */
async function render(ast, format = 'ascii') {
  return (await _ensureInit()).render(ast, format);
}

export {
  illConfig,
  load,
  precompile,
  loadPrecompiled,
  normalizeQuery,
  loadILL,
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
};
export default {
  ...mde,
  illConfig,
  load,
  precompile,
  loadPrecompiled,
  normalizeQuery,
  parseExpr,
  loadILL,
  proveString,
  parseFormula,
  parseSequent,
  render,
};
