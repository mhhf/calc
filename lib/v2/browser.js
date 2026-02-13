/**
 * v2 Browser-Compatible API
 *
 * This module provides the same API as lib/v2/index.js but works in browsers
 * by loading from a pre-bundled JSON file instead of reading .calc/.rules files.
 *
 * Usage in browser:
 *   import * as calcV2 from '@lib/v2/browser';
 *
 *   // Initialize (call once)
 *   await calcV2.init();
 *
 *   // Then use the same API
 *   const result = await calcV2.proveString('A, A -o B |- B');
 */

const prover = require('./prover');
const Seq = require('./kernel/sequent');
const AST = require('./kernel/ast');
const Store = require('./kernel/store');
const { copy, apply, occurs } = require('./kernel/substitute');
const { unify, match } = require('./kernel/unify');
const { createManualProofAPI } = require('./prover/manual');
const { buildAST, buildParser, buildRenderer } = require('./calculus/builders');

// Cached calculus instance (hydrated from bundle)
let calculus = null;
let bundleData = null;

/**
 * Initialize from pre-bundled data
 * @param {Object} bundle - Pre-processed ILL bundle (from ill-v2.json)
 */
function initFromBundle(bundle) {
  if (!bundle?.constructors) {
    throw new Error('Invalid bundle: missing constructors');
  }
  bundleData = bundle;
  calculus = hydrateCalculus(bundle);
  return calculus;
}

/**
 * Hydrate a calculus from bundle data
 * Recreates the runtime functions (parse, render, AST constructors)
 */
function hydrateCalculus(bundle) {
  const { constructors, rules, polarity, invertible, directives } = bundle;

  // Build AST constructor functions
  const ASTConstructors = buildAST(constructors);

  // Build parser
  const parse = buildParser(constructors);

  // Build renderer
  const render = buildRenderer(constructors);

  return {
    name: bundle.name,
    baseTypes: bundle.baseTypes,
    constructors,
    directives,
    rules,
    polarity,
    invertible,
    AST: ASTConstructors,
    parse,
    render,

    // Utility functions
    connectivesFor: (typeName) => {
      return Object.values(constructors).filter(c => c.returnType === typeName);
    },
    isPositive: (tag) => polarity[tag] === 'positive',
    isNegative: (tag) => polarity[tag] === 'negative',
    isInvertible: (ruleName) => invertible[ruleName] === true
  };
}

/**
 * Create sequent parser for the loaded calculus
 */
function createSequentParser() {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  function parseSequent(input) {
    const src = input.trim();
    const parts = src.split('|-');
    if (parts.length !== 2) {
      throw new Error(`Invalid sequent: expected '|-' turnstile in "${src}"`);
    }

    const [antecedentStr, succedentStr] = parts.map(s => s.trim());
    const succedent = parseHyp(succedentStr);

    const linearFormulas = [];
    if (antecedentStr) {
      const hyps = splitTopLevel(antecedentStr, ',');
      for (const hyp of hyps) {
        const formula = parseHyp(hyp.trim());
        if (formula) linearFormulas.push(formula);
      }
    }

    return Seq.fromArrays(linearFormulas, [], succedent);
  }

  function parseHyp(input) {
    const trimmed = input.trim();
    if (!trimmed) return null;

    const colonIdx = trimmed.indexOf(':');
    if (colonIdx > 0) {
      const formulaStr = trimmed.slice(colonIdx + 1).trim();
      return calculus.parse(formulaStr);
    }

    return calculus.parse(trimmed);
  }

  function splitTopLevel(str, delim) {
    const parts = [];
    let depth = 0;
    let start = 0;

    for (let i = 0; i < str.length; i++) {
      const c = str[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      else if (c === delim && depth === 0) {
        parts.push(str.slice(start, i));
        start = i + 1;
      }
    }

    parts.push(str.slice(start));
    return parts.filter(s => s.trim());
  }

  function formatSequent(seq, format = 'ascii') {
    const linear = Seq.getContext(seq, 'linear');
    const cart = Seq.getContext(seq, 'cartesian');

    const formatFormula = (f) => calculus.render(f, format);

    const linearPart = linear.map(formatFormula).join(', ');
    const cartPart = cart.length > 0 ? cart.map(formatFormula).join(', ') + ' ; ' : '';
    const succedentPart = formatFormula(seq.succedent);

    if (format === 'latex') {
      const turnstile = '\\vdash';
      if (cartPart) {
        return `${cartPart}${linearPart} ${turnstile} ${succedentPart}`;
      }
      return linearPart ? `${linearPart} ${turnstile} ${succedentPart}` : `${turnstile} ${succedentPart}`;
    }

    if (cartPart) {
      return `${cartPart}${linearPart} |- ${succedentPart}`;
    }
    return linearPart ? `${linearPart} |- ${succedentPart}` : `|- ${succedentPart}`;
  }

  return {
    parseSequent,
    parseHyp,
    formatSequent
  };
}

// ============================================================================
// High-Level API (same as lib/v2/index.js)
// ============================================================================

/**
 * Prove a sequent string
 */
async function proveString(sequentStr, opts = {}) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  const sp = createSequentParser();
  const seq = sp.parseSequent(sequentStr);

  const p = prover.create(calculus);
  const result = p.prove(seq, opts);

  return {
    ...result,
    sequent: seq,
    formatted: sp.formatSequent(seq)
  };
}

/**
 * Parse a formula string
 */
function parseFormula(formulaStr) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');
  return calculus.parse(formulaStr);
}

/**
 * Parse a sequent string
 */
function parseSequent(sequentStr) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');
  const sp = createSequentParser();
  return sp.parseSequent(sequentStr);
}

/**
 * Render a formula or sequent
 */
function render(ast, format = 'ascii') {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  if (ast?.succedent) {
    const sp = createSequentParser();
    return sp.formatSequent(ast, format);
  }

  return calculus.render(ast, format);
}

/**
 * Get the loaded calculus
 */
function getCalculus() {
  return calculus;
}

/**
 * Check if initialized
 */
function isInitialized() {
  return calculus !== null;
}

/**
 * Create a manual proof API instance (uses the loaded calculus)
 */
function getManualProofAPI() {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');
  return createManualProofAPI(calculus);
}

module.exports = {
  // Initialization
  initFromBundle,
  isInitialized,
  getCalculus,

  // High-level API
  proveString,
  parseFormula,
  parseSequent,
  render,
  createSequentParser,

  // Proof search
  prove: prover.prove,
  createProver: prover.create,

  // Manual proof API (single source of truth for interactive proofs)
  getManualProofAPI,
  createManualProofAPI,

  // Sequent operations
  Seq,

  // Content-addressed store (for hash lookup)
  Store,

  // AST utilities
  ast: {
    copy: AST.copy,
    isAtomic: AST.isAtomic,
    freeVars: AST.freeVars,
    occurs
  },

  // Substitution
  substitute: { copy, apply },

  // Unification
  unify: { unify, match }
};
