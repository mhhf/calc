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

/**
 * Load MDE file and prepare for execution
 * @param {string} filePath
 * @returns {Promise<Object>}
 */
async function load(filePath) {
  const { types, clauses, forwardRules, queries } = await convert.load(filePath);

  // Precompile forward rules
  const compiledRules = forwardRules.map(r => forward.compileRule(r));

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

module.exports = {
  load,
  parseExpr: convert.parseExpr,
  hasMonad: convert.hasMonad,
  decomposeQuery: convert.decomposeQuery,
  // Backward chaining
  prove: backward.prove,
  extractSolution: backward.extractSolution,
  // Forward chaining
  exec: forward.run,
  createState: forward.createState,
  compileRule: forward.compileRule,
  Store
};
