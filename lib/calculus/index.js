/**
 * Calculus Module
 *
 * Loads calculus definition from .family/.calc/.rules files and generates:
 * - AST constructors (e.g., tensor(a, b), loli(a, b))
 * - Parser for object-language formulas
 * - Renderer with @ascii/@latex support
 * - Inference rules with metadata (invertibility, polarity)
 *
 * NOTHING is hardcoded - everything is generated from the spec files.
 */

const generator = require('../meta-parser/loader');
const path = require('path');
const { buildAST, buildParser, buildRenderer, computeConnectivesByType } = require('./builders');

// Cache for loaded calculi
const cache = new Map();

/**
 * Load a calculus from spec files
 * @param {string} calcPath - Path to .calc file
 * @param {string} rulesPath - Path to .rules file (optional)
 * @returns {Promise<Calculus>} Loaded calculus with AST, parser, renderer, rules
 */
async function load(calcPath, rulesPath = null) {
  const cacheKey = `${calcPath}:${rulesPath || ''}`;
  if (cache.has(cacheKey)) return cache.get(cacheKey);

  // Use existing generator infrastructure to load with @extends chain
  const spec = await generator.loadWithExtends(calcPath);

  // Load rules if path provided
  let rules = {};
  if (rulesPath) {
    rules = loadRules(rulesPath, spec.constructors);
  }

  // Build calculus object from spec
  const calculus = buildCalculus(spec, rules);

  cache.set(cacheKey, calculus);
  return calculus;
}

/**
 * Load the default ILL calculus with rules
 */
async function loadILL() {
  const baseDir = path.join(__dirname, '../../calculus/ill');
  return load(
    path.join(baseDir, 'ill.calc'),
    path.join(baseDir, 'ill.rules')
  );
}

/**
 * Load inference rules from .rules file (sequent notation)
 */
function loadRules(rulesPath, constructors) {
  const fs = require('fs');
  const text = fs.readFileSync(rulesPath, 'utf8');
  const parseFormula = buildParser(constructors);
  const { parseRules2 } = require('../rules/rules2-parser');
  return parseRules2(text, parseFormula);
}

/**
 * Build calculus runtime from extracted spec
 */
function buildCalculus(spec, rules = {}) {
  const { baseTypes, constructors, directives } = spec;

  // Group constructors by return type (names only, resolve to objects for connectivesFor)
  const byTypeName = computeConnectivesByType(constructors);

  // Build AST constructors
  const AST = buildAST(constructors);

  // Build parser
  const parser = buildParser(constructors);

  // Build renderer
  const render = buildRenderer(constructors);

  // Build polarity map - explicit @polarity OR inferred from rule structure
  const polarity = {};
  const { inferPolarityFromRules, inferInvertibilityFromRule } = require('../meta/focusing');
  const inferredPolarity = inferPolarityFromRules(rules);

  for (const [name, constr] of Object.entries(constructors)) {
    if (constr.annotations.polarity) {
      // Explicit annotation takes precedence
      polarity[name] = constr.annotations.polarity;
    } else if (inferredPolarity[name]) {
      // Fall back to inference
      polarity[name] = inferredPolarity[name];
    }
  }

  // Build invertibility map - explicit @invertible OR inferred from polarity
  const invertible = {};
  for (const [name, rule] of Object.entries(rules)) {
    if (rule.invertible !== null) {
      // Explicit annotation
      invertible[name] = rule.invertible;
    } else {
      // Infer from polarity and rule position (L/R)
      const inferred = inferInvertibilityFromRule(name, rule, polarity);
      if (inferred !== null) {
        invertible[name] = inferred;
      }
    }
  }

  return {
    name: directives.family || 'calculus',
    baseTypes,
    constructors,
    directives,
    rules,
    AST,
    parse: parser,
    render,

    // Focusing metadata
    polarity,      // connective -> 'positive' | 'negative'
    invertible,    // rule -> true | false

    // Utility: get all connectives for a type
    connectivesFor: (typeName) => (byTypeName[typeName] || []).map(n => constructors[n]),

    // Utility: check if a connective is positive/negative
    isPositive: (tag) => polarity[tag] === 'positive',
    isNegative: (tag) => polarity[tag] === 'negative',

    // Utility: check if a rule is invertible
    isInvertible: (ruleName) => invertible[ruleName] === true
  };
}


/**
 * Clear the cache
 */
function clearCache() {
  cache.clear();
}

module.exports = {
  load,
  loadILL,
  clearCache
};
