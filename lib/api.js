/**
 * Shared Calc API — environment-agnostic facade over a calculus object.
 *
 * Both lib/index.js (Node.js) and lib/browser.js (browser) delegate here
 * after constructing their calculus via different paths:
 *   - Node.js: loads from .calc/.rules files
 *   - Browser: hydrates from pre-bundled JSON
 *
 * Usage:
 *   const api = createCalcAPI(calculus);
 *   api.proveString('A, A -o B |- B');
 */

const prover = require('./prover/strategy/auto');
const Seq = require('./kernel/sequent');
const Store = require('./kernel/store');
const { createManualProofAPI } = require('./prover/strategy/manual');
const { sequentParser } = require('./parser/sequent-parser');

/**
 * Create a complete API facade for a loaded calculus.
 * @param {Object} calculus - Fully constructed calculus object
 * @returns {Object} API with prove, parse, render, etc.
 */
function createCalcAPI(calculus) {
  let _manualProofAPI = null;
  const _seqParser = sequentParser(calculus);

  return {
    /** Prove a sequent string */
    proveString(sequentStr, opts = {}) {
      const seq = _seqParser.parseSequent(sequentStr);
      const p = prover.create(calculus);
      const result = p.prove(seq, opts);
      return {
        ...result,
        sequent: seq,
        formatted: _seqParser.formatSequent(seq)
      };
    },

    /** Parse a formula string */
    parseFormula(formulaStr) {
      return calculus.parse(formulaStr);
    },

    /** Parse a sequent string */
    parseSequent(sequentStr) {
      return _seqParser.parseSequent(sequentStr);
    },

    /** Render a formula or sequent */
    render(ast, format = 'ascii') {
      if (ast?.succedent) {
        return _seqParser.formatSequent(ast, format);
      }
      return calculus.render(ast, format);
    },

    /** Create a reusable prover */
    createProver() {
      return prover.create(calculus);
    },

    /** Create a sequent parser */
    sequentParser() {
      return sequentParser(calculus);
    },

    /** Get or create the cached ManualProofAPI */
    getManualProofAPI() {
      if (!_manualProofAPI) _manualProofAPI = createManualProofAPI(calculus);
      return _manualProofAPI;
    },

    /** Direct access to the underlying calculus */
    calculus,

    // Re-exported modules
    Seq,
    Store,
    createManualProofAPI,
  };
}

module.exports = { createCalcAPI };
