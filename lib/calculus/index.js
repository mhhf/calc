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

import generator from '../meta-parser/loader.js';
import path from 'path';
import Store from '../kernel/store.js';
import { buildAST, buildParser, buildRenderer, connByType, deriveRoles } from './builders.js';
import { computationRole } from '../engine/formula-utils.js';
// Hoisted by tools/esm-hoist.js:
import fs from 'fs';
import { parseRules2 } from '../rules/rules2-parser.js';
import { monadRules } from './modes.js';
import { inferPolarityFromRules, inferInvertibilityFromRule } from '../meta/focusing.js';

// Cache for loaded calculi
const cache = new Map();

// TODO_0218: flush the calculus cache on Store.clear() so that two consecutive
// cold loads in the same process produce byte-identical Store arenas. The
// cache's `buildCalculus()` side-effect-allocates atoms for type-name roots
// (e.g., 'formula', 'grade', 'sequent'); when the cache is hot, these atoms
// do not get re-allocated and the second load's Store arena drifts from the
// first. Flushing the cache forces buildCalculus to re-run, which is ~5ms —
// a worthwhile tax for cross-run reproducibility that the compose cache
// depends on.
Store.onClear(() => cache.clear());

/**
 * Load a calculus from spec files
 * @param {string} calcPath - Path to .calc file
 * @param {string} rulesPath - Path to .rules file (optional)
 * @param {Object} [opts] - { parser, theory }: parser options for BOTH the
 *   rules file and calculus.parse (graded/timed syntax), and the theory
 *   engine ({ prove }) discharging template theory premises (TODO_0273).
 *   NOTE: the cache key is path-based — one opts flavor per path pair.
 * @returns {Calculus} Loaded calculus with AST, parser, renderer, rules
 */
function load(calcPath, rulesPath = null, opts = {}) {
  // rulesPath may be a LIST of .rules files (later files extend earlier
  // ones — will inherits gill's backward fragment by reference and adds
  // its own; .rules files have no @extends mechanism, TODO_0298 item 1).
  const rulesPaths = rulesPath == null ? [] : [].concat(rulesPath);
  const cacheKey = `${calcPath}:${rulesPaths.join('+')}`;
  if (cache.has(cacheKey)) return cache.get(cacheKey);

  // Use existing generator infrastructure to load with @extends chain
  const spec = generator.loadChain(calcPath);

  // Load rules if path(s) provided — a rule name may appear in one file
  // only (silent override would hide a shadowed base rule)
  let rules = {};
  for (const rp of rulesPaths) {
    const next = loadRules(rp, spec.constructors, opts);
    for (const name of Object.keys(next)) {
      if (name in rules) {
        throw new Error(`rule '${name}' defined in more than one rules file (${rp})`);
      }
    }
    Object.assign(rules, next);
  }

  // Build calculus object from spec
  const calculus = buildCalculus(spec, rules, opts);

  cache.set(cacheKey, calculus);
  return calculus;
}

/**
 * Load the default ILL calculus with rules
 */
function loadILL() {
  const baseDir = path.join(import.meta.dirname, '../../calculus/ill');
  return load(
    path.join(baseDir, 'ill.calc'),
    path.join(baseDir, 'ill.rules')
  );
}

/**
 * Load inference rules from .rules file (sequent notation)
 */
function loadRules(rulesPath, constructors, opts = {}) {
  const text = fs.readFileSync(rulesPath, 'utf8');
  const parseFormula = buildParser(constructors, opts.parser);

  const rules = parseRules2(text, parseFormula);

  // Theory premises must name predicates the theory can actually speak
  // about — a typo'd predicate would otherwise load fine and make the rule
  // silently never applicable (TODO_0274 item 1). `has` is optional on the
  // theory interface; a bare { prove } theory skips this check.
  const theory = opts.theory;
  if (theory && typeof theory.has === 'function') {
    for (const [name, rule] of Object.entries(rules)) {
      for (const tg of rule.descriptor?.template?.theoryGoals ?? []) {
        const tag = Store.tag(tg.goal);
        if (!theory.has(tag)) {
          throw new Error(`rule '${name}': unknown theory predicate '${tag}' — not an FFI predicate or a clause/definition head of the calculus theory`);
        }
      }
    }
  }

  return rules;
}

/**
 * Build calculus runtime from extracted spec
 */
function buildCalculus(spec, rules = {}, opts = {}) {
  const { baseTypes, constructors, directives } = spec;

  // Group constructors by return type (names only, resolve to objects for connectivesFor)
  const byTypeName = connByType(constructors);

  // Build AST constructors
  const AST = buildAST(constructors);

  // Build parser
  const parser = buildParser(constructors, opts.parser);

  // Build renderer
  const render = buildRenderer(constructors);

  // Inject monad rules only if calculus defines a computation (category
  // 'monad') connective — found by category, not by name, so a calculus may
  // call its graded monad anything (shared default: monad). The role record drives
  // rule names, arity, and premise indices (see modes.js).
  const compEntry = Object.entries(constructors).find(
    ([, c]) => c.annotations?.category === 'monad');
  if (compEntry) {
    const comp = computationRole(compEntry[0], compEntry[1].argTypes?.length ?? 0);
    if (comp) {
      // Injected defaults never clobber rules from the .rules file — a
      // calculus may declare its own monad rules (till: graded bind/unit).
      const mRules = monadRules(comp);
      for (const [name, rule] of Object.entries(mRules))
        if (!(name in rules)) rules[name] = rule;
    }
  }

  // Build polarity map - explicit @polarity OR inferred from rule structure
  const polarity = {};

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

  // Derive connective roles from annotations + polarity
  const roles = deriveRoles(constructors, polarity);

  return {
    name: directives.family || 'calculus',
    baseTypes,
    constructors,
    sortEdges: spec.sortEdges || [],
    directives,
    rules,
    roles,
    AST,
    parse: parser,
    render,

    // Theory engine ({ prove }) discharging template theory premises
    // (TODO_0273: `<- !qsub F E H` — the arithmetic theory is the
    // semantics); null for calculi without theory premises.
    theory: opts.theory || null,

    // Context structure: zones and copy semantics
    contextStructure: {
      zones: ['linear', 'cartesian'],
      copySource: 'cartesian',
      copyTarget: 'linear',
    },

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

export { load, loadILL, clearCache };
export default { load, loadILL, clearCache };
