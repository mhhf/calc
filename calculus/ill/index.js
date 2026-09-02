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

const load = (filePath, opts = {}) =>
  mde.load(filePath, { calculusConfig: illConfig, ...opts });
const precompile = (filePaths, cachePath, opts = {}) =>
  mde.precompile(filePaths, cachePath, { calculusConfig: illConfig, ...opts });
const loadPrecompiled = (cachePath, sellOpts = {}) =>
  mde.loadPrecompiled(cachePath, { calculusConfig: illConfig, ...sellOpts });

const { parseExpr, hasMonad, decomposeQuery, prove, exec, createState,
  compileRule, Store, _composeCacheKey } = mde;

export {
  illConfig,
  load,
  precompile,
  loadPrecompiled,
  normalizeQuery,
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
};
