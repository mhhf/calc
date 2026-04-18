/**
 * Browser-Compatible API
 *
 * Thin wrapper over lib/api.js — hydrates a calculus from pre-bundled JSON
 * then delegates to the shared API facade.
 *
 * Usage:
 *   import * as calc from '@lib/browser';
 *   calc.initFromBundle(bundle);
 *   const result = calc.proveString('A, A -o B |- B');
 */

import { createCalcAPI } from './api.js';
import { buildAST, buildParser, parserFromTables, buildRenderer, rendererFromFormats, deriveRoles } from './calculus/builders.js';
import { createManualProofAPI } from './prover/strategy/manual.js';
import * as Seq from './kernel/sequent.js';
import * as Store from './kernel/store.js';

// Cached API instance (hydrated from bundle)
let _api = null;

function ensureInit() {
  if (!_api) throw new Error('Call initFromBundle() first');
  return _api;
}

/**
 * Hydrate a calculus from bundle data.
 * Recreates runtime functions (parse, render, AST constructors) from precomputed tables.
 */
function hydrateCalculus(bundle) {
  const { constructors, rules, polarity, invertible, directives } = bundle;

  const ASTConstructors = buildAST(constructors);

  const parse = bundle.parserTables
    ? parserFromTables(bundle.parserTables)
    : buildParser(constructors);

  const render = bundle.rendererFormats
    ? rendererFromFormats(bundle.rendererFormats)
    : buildRenderer(constructors);

  const ruleSpecMeta = bundle.ruleSpecMeta || null;

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
    ruleSpecMeta,
    connectivesFor: bundle.connectivesByType
      ? (typeName) => (bundle.connectivesByType[typeName] || []).map(n => constructors[n])
      : (typeName) => Object.values(constructors).filter(c => c.returnType === typeName),
    isPositive: (tag) => polarity[tag] === 'positive',
    isNegative: (tag) => polarity[tag] === 'negative',
    isInvertible: (ruleName) => invertible[ruleName] === true,
    roles: deriveRoles(constructors, polarity)
  };
}

/**
 * Initialize from pre-bundled data
 * @param {Object} bundle - Pre-processed ILL bundle (from ill.json)
 */
function initFromBundle(bundle) {
  if (!bundle?.constructors) {
    throw new Error('Invalid bundle: missing constructors');
  }
  const calculus = hydrateCalculus(bundle);
  _api = createCalcAPI(calculus);
  return calculus;
}

function isInitialized() { return _api !== null; }
function getCalculus() { return _api ? _api.calculus : null; }

const proveString         = (...a) => ensureInit().proveString(...a);
const parseFormula        = (...a) => ensureInit().parseFormula(...a);
const parseSequent        = (...a) => ensureInit().parseSequent(...a);
const render              = (...a) => ensureInit().render(...a);
const sequentParser       = ()     => ensureInit().sequentParser();
const createProver        = (...a) => ensureInit().createProver(...a);
const getManualProofAPI   = ()     => ensureInit().getManualProofAPI();

export {
  initFromBundle,
  getCalculus,
  isInitialized,
  proveString,
  parseFormula,
  parseSequent,
  render,
  sequentParser,
  createProver,
  getManualProofAPI,
  createManualProofAPI,
  Seq,
  Store,
};

export default {
  initFromBundle,
  getCalculus,
  isInitialized,
  proveString,
  parseFormula,
  parseSequent,
  render,
  sequentParser,
  createProver,
  getManualProofAPI,
  createManualProofAPI,
  Seq,
  Store,
};
