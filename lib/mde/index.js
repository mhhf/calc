/**
 * MDE Module - Load and work with MDE/Celf files
 *
 * Minimal API following Unix philosophy:
 * - load(filePath) - load MDE file, returns { types, clauses, forwardRules }
 * - parseExpr(src) - parse expression string to hash
 * - exec(state, rules) - run forward chaining
 */

const convert = require('./convert');
const forward = require('../v2/prover/forward');
const Store = require('../v2/kernel/store');

/**
 * Load MDE file and prepare for execution
 * @param {string} filePath
 * @returns {Promise<Object>}
 */
async function load(filePath) {
  const { types, clauses, forwardRules } = await convert.load(filePath);

  // Precompile forward rules
  const compiledRules = forwardRules.map(r => forward.compileRule(r));

  return {
    types,
    clauses,
    forwardRules: compiledRules,
    // Convenience: run forward execution
    exec: (state, opts) => forward.run(state, compiledRules, opts)
  };
}

module.exports = {
  load,
  parseExpr: convert.parseExpr,
  hasMonad: convert.hasMonad,
  // Forward chaining
  exec: forward.run,
  createState: forward.createState,
  compileRule: forward.compileRule,
  Store
};
