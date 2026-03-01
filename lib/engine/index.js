/**
 * MDE Module - Load and work with MDE/Celf files
 *
 * Minimal API following Unix philosophy:
 * - load(filePath) - load MDE file, returns { types, clauses, forwardRules }
 * - parseExpr(src) - parse expression string to hash
 * - prove(goal) - backward chaining proof search
 * - exec(state, rules) - run forward chaining
 */

const convert = require('./convert');
const forward = require('./forward');
const backward = require('./prove');
const Store = require('../kernel/store');
const { serialize, deserialize } = require('./store-binary');
const fs = require('fs');
const path = require('path');

/**
 * Load MDE file and prepare for execution.
 * @param {string|string[]} filePath - file path(s) to load
 * @param {Object} [opts]
 * @param {string} [opts.cache] - binary cache file path. If file exists, loads from it.
 *   If not, parses and auto-writes cache for next time.
 * @returns {Object}
 */
function load(filePath, opts = {}) {
  if (opts.cache && fs.existsSync(opts.cache)) {
    return loadPrecompiled(opts.cache);
  }

  const { types, clauses, forwardRules, queries } = convert.load(filePath);

  // Auto-write cache on miss (includes compiled rules for fast restore)
  if (opts.cache) {
    const compiledRules = forwardRules.map(r => forward.compileRule(r));
    const metadata = {
      types: Object.fromEntries(types),
      clauses: Object.fromEntries(
        Array.from(clauses.entries()).map(([k, v]) => [k, v])
      ),
      forwardRules,
      compiledRules: _serializeCompiledRules(compiledRules),
      queries: Object.fromEntries(queries)
    };
    const snap = Store.snapshot(metadata);
    const buf = serialize(snap);
    fs.mkdirSync(path.dirname(opts.cache), { recursive: true });
    fs.writeFileSync(opts.cache, buf);
  }

  return _buildCalc(types, clauses, forwardRules, queries);
}

/**
 * Build calc context from loaded data (shared by load and loadPrecompiled)
 * @param {Object} [opts]
 * @param {Array} [opts.compiledRules] - pre-compiled rules from cache
 */
function _buildCalc(types, clauses, forwardRules, queries, opts = {}) {
  // Use cached compiled rules or compile from scratch
  const compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r));

  // Build backward prover index once at load time (2x speedup)
  const backwardIndex = backward.buildIndex(clauses, types);

  // Capture calc context for backward proving
  const calcContext = { types, clauses, backwardIndex };

  return {
    types,
    clauses,
    queries,
    forwardRules: compiledRules,

    // Backward chaining proof search
    prove: (goal, opts) => backward.prove(goal, clauses, types, opts),

    // Forward chaining execution (auto-injects calc for backward proving)
    exec: (state, opts = {}) => forward.run(state, compiledRules, { ...opts, calc: calcContext })
  };
}

/**
 * Serialize compiled rules for JSON storage.
 * Converts Set fields (freevars, persistentDeps) to arrays.
 */
function _serializeCompiledRules(rules) {
  return rules.map(r => {
    if (!r.linearMeta) return r;
    const lm = {};
    for (const k in r.linearMeta) {
      const m = r.linearMeta[k];
      lm[k] = {
        ...m,
        freevars: m.freevars instanceof Set ? [...m.freevars] : m.freevars,
        persistentDeps: m.persistentDeps instanceof Set ? [...m.persistentDeps] : m.persistentDeps,
      };
    }
    return { ...r, linearMeta: lm };
  });
}

/**
 * Deserialize compiled rules from JSON storage.
 * Converts array fields (freevars, persistentDeps) back to Sets.
 */
function _deserializeCompiledRules(rules) {
  return rules.map(r => {
    if (!r.linearMeta) return r;
    const lm = {};
    for (const k in r.linearMeta) {
      const m = r.linearMeta[k];
      lm[k] = {
        ...m,
        freevars: Array.isArray(m.freevars) ? new Set(m.freevars) : m.freevars,
        persistentDeps: Array.isArray(m.persistentDeps) ? new Set(m.persistentDeps) : m.persistentDeps,
      };
    }
    return { ...r, linearMeta: lm };
  });
}

/**
 * Precompile MDE files to binary cache.
 * Includes compiled forward rules for fast restore.
 * @param {string|string[]} filePaths - source files to precompile
 * @param {string} cachePath - output binary file path
 * @returns {{ types, clauses, forwardRules, queries, byteSize }}
 */
function precompile(filePaths, cachePath) {
  Store.clear();
  const { types, clauses, forwardRules, queries } = convert.load(filePaths);

  // Compile rules and include in cache for fast restore
  const compiledRules = forwardRules.map(r => forward.compileRule(r));

  const metadata = {
    types: Object.fromEntries(types),
    clauses: Object.fromEntries(
      Array.from(clauses.entries()).map(([k, v]) => [k, v])
    ),
    forwardRules,
    compiledRules: _serializeCompiledRules(compiledRules),
    queries: Object.fromEntries(queries)
  };

  const snap = Store.snapshot(metadata);
  const buf = serialize(snap);

  fs.mkdirSync(path.dirname(cachePath), { recursive: true });
  fs.writeFileSync(cachePath, buf);

  return { types, clauses, forwardRules, queries, byteSize: buf.length };
}

/**
 * Load from precompiled binary cache.
 * Restores Store state and uses cached compiled rules.
 * @param {string} cachePath - binary cache file path
 * @returns {Object} calc context (same shape as load())
 */
function loadPrecompiled(cachePath) {
  const buf = fs.readFileSync(cachePath);
  const data = deserialize(buf);
  Store.restore(data);

  const { types: typesObj, clauses: clausesObj, forwardRules, compiledRules, queries: queriesObj } = data.metadata;

  const types = new Map(Object.entries(typesObj));
  const clauses = new Map(Object.entries(clausesObj));
  const queries = new Map(Object.entries(queriesObj));

  return _buildCalc(types, clauses, forwardRules, queries, {
    compiledRules: _deserializeCompiledRules(compiledRules)
  });
}

module.exports = {
  load,
  precompile,
  loadPrecompiled,
  parseExpr: convert.parseExpr,
  hasMonad: convert.hasMonad,
  decomposeQuery: convert.decomposeQuery,
  // Backward chaining
  prove: backward.prove,
  // Forward chaining
  exec: forward.run,
  createState: forward.createState,
  compileRule: forward.compileRule,
  Store
};
