/**
 * Generic Rule Interpreter
 *
 * Reads rule ASTs from calculus.rules and produces spec objects
 * for the prover. Each spec has: numPremises, copyContext,
 * makePremises, and optionally requiresEmptyDelta, structural,
 * movesToCartesian, extraLinear.
 *
 * Core idea: parse rule head to find the principal connective
 * and its formula var bindings (A, B), parse each premise to
 * find what formulas are added to linear/cartesian context,
 * then build a makePremises that uses Store.child to extract
 * the concrete subformulas at runtime.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { analyzeContextFlow } = require('../meta/focusing');

const FORMULA_VARS = new Set(['A', 'B', 'C', 'F']);

// -- AST helpers --

function flattenApp(term) {
  const args = [];
  while (term?.type === 'TermApp') {
    args.unshift(term.arg);
    term = term.func;
  }
  return { func: term, args };
}

const isVar = (node) => node?.type === 'TermVar';
const isIdent = (node, name) => node?.type === 'TermIdent' && node.name === name;

// -- Sequent/rule parsing --

function parseDeriv(term) {
  const { func, args } = flattenApp(term);
  if (!isIdent(func, 'deriv') || args.length !== 1)
    throw new Error(`Expected deriv(seq(...))`);
  const seq = flattenApp(args[0]);
  if (!isIdent(seq.func, 'seq') || seq.args.length !== 3)
    throw new Error(`Expected seq(cart, linear, succ)`);
  return { cart: seq.args[0], linear: seq.args[1], succ: seq.args[2] };
}

/**
 * Extract principal formula from hyp(any, connective(A, B)).
 * Returns { connective, formulaBindings } or null.
 */
function extractPrincipal(node) {
  const { func, args } = flattenApp(node);
  if (!isIdent(func, 'hyp') || args.length !== 2) return null;
  const formula = args[1];
  if (isVar(formula)) return null; // bare variable, no connective

  const { func: conn, args: connArgs } = flattenApp(formula);
  if (conn?.type !== 'TermIdent') return null;

  return {
    connective: conn.name,
    formulaBindings: connArgs
      .map((a, i) => isVar(a) ? { name: a.name, childIdx: i } : null)
      .filter(Boolean)
  };
}

/**
 * Walk a context AST (comma-tree), find the hyp with a principal connective.
 */
function findPrincipal(node) {
  const { func, args } = flattenApp(node);
  if (isIdent(func, 'comma') && args.length === 2)
    return findPrincipal(args[0]) || findPrincipal(args[1]);
  if (isIdent(func, 'hyp') && args.length === 2)
    return extractPrincipal(node);
  return null;
}

/**
 * Collect formula var names that appear as hyp(any, VAR) in a context AST.
 */
function collectHypVars(node) {
  const results = [];
  const { func, args } = flattenApp(node);
  if (isIdent(func, 'comma') && args.length === 2) {
    results.push(...collectHypVars(args[0]), ...collectHypVars(args[1]));
  } else if (isIdent(func, 'hyp') && args.length === 2 && isVar(args[1])) {
    results.push(args[1].name);
  }
  return results;
}

/**
 * Get the succedent variable name from hyp(any, X) or null.
 */
function getSuccedentVar(succAST) {
  const { func, args } = flattenApp(succAST);
  return (isIdent(func, 'hyp') && args.length === 2 && isVar(args[1]))
    ? args[1].name : null;
}

// -- Rule analysis --

function analyzeHead(rule) {
  const head = parseDeriv(rule.head);
  const succPrincipal = extractPrincipal(head.succ);
  const linPrincipal = !succPrincipal ? findPrincipal(head.linear) : null;
  const principalSide = succPrincipal ? 'r' : linPrincipal ? 'l' : null;

  return {
    head,
    principal: succPrincipal || linPrincipal,
    principalSide,
    emptyLinear: isIdent(head.linear, 'empty'),
  };
}

function analyzePremise(premiseAST, headInfo) {
  const premise = parseDeriv(premiseAST);
  const premLinVars = collectHypVars(premise.linear);
  const premCartVars = collectHypVars(premise.cart);
  const headCartVars = collectHypVars(headInfo.head.cart);
  const headSuccVar = getSuccedentVar(headInfo.head.succ);
  const succVar = getSuccedentVar(premise.succ);

  return {
    extraLinearFormulas: premLinVars.filter(v => FORMULA_VARS.has(v)),
    extraCartesianFormulas: premCartVars.filter(v => FORMULA_VARS.has(v) && !headCartVars.includes(v)),
    succedentVar: succVar !== headSuccVar ? succVar : null,
  };
}

/**
 * Determine the spec key for a rule.
 * Standard rules: name as-is (tensor_r, with_l1, ...).
 * Non-standard names: use connective_side (promotion → bang_r, dereliction → bang_l).
 * Structural rules: keep name (copy).
 */
function specKey(rule, headInfo) {
  if (rule.name === 'id') return null;
  if (!headInfo.principal) return rule.name; // structural (copy)

  const expected = `${headInfo.principal.connective}_${headInfo.principalSide}`;
  const base = expected.replace(/_[lr]$/, '') + '_';
  // with_l1, with_l2, etc. start with the base
  if (rule.name === expected || rule.name.startsWith(base)) return rule.name;
  return expected; // promotion → bang_r, dereliction → bang_l
}

// -- Spec builders --

function buildMakePremises(headInfo, premiseSpecs) {
  const { principal } = headInfo;

  return (formula, seq, idx) => {
    const bindings = {};
    if (principal) {
      for (const b of principal.formulaBindings)
        bindings[b.name] = Store.child(formula, b.childIdx);
    }
    const cart = Seq.getContext(seq, 'cartesian');

    return premiseSpecs.map(ps => {
      const linear = ps.extraLinearFormulas.map(v => bindings[v] ?? formula);
      const extraCart = ps.extraCartesianFormulas.map(v => bindings[v] ?? formula);
      const premCart = extraCart.length > 0 ? [...cart, ...extraCart] : cart;
      const succ = ps.succedentVar ? (bindings[ps.succedentVar] ?? seq.succedent) : seq.succedent;
      return Seq.fromArrays(linear, premCart, succ);
    });
  };
}

function buildExtraLinear(headInfo, premiseSpecs) {
  const resolve = (varName, formula) => {
    const b = headInfo.principal.formulaBindings.find(b => b.name === varName);
    return b ? Store.child(formula, b.childIdx) : formula;
  };

  if (premiseSpecs.length === 1) {
    return (formula) =>
      premiseSpecs[0].extraLinearFormulas.map(v => resolve(v, formula));
  }
  return (formula, premiseIdx) => {
    const ps = premiseSpecs[premiseIdx ?? 0];
    return ps.extraLinearFormulas.map(v => resolve(v, formula));
  };
}

// -- Main entry point --

/**
 * Build rule specs from calculus rule ASTs.
 * @returns {{ specs: Object, alternatives: Object }}
 */
function buildRuleSpecsFromAST(calculus) {
  const specs = {};
  const alternatives = {};

  for (const [name, rule] of Object.entries(calculus.rules)) {
    if (name === 'id') continue;

    const headInfo = analyzeHead(rule);
    const key = specKey(rule, headInfo);
    if (!key) continue;

    const premiseSpecs = rule.premises.map(p => analyzePremise(p, headInfo));
    const flow = analyzeContextFlow(rule);

    const spec = {
      numPremises: rule.numPremises,
      copyContext: flow === 'copy',
    };

    if (headInfo.emptyLinear && rule.numPremises > 0) spec.requiresEmptyDelta = true;
    if (rule.structural) spec.structural = true;
    if (premiseSpecs.some(ps => ps.extraCartesianFormulas.length > 0)) spec.movesToCartesian = true;

    // extraLinear (skip for structural rules like copy)
    if (!rule.structural && premiseSpecs.some(ps => ps.extraLinearFormulas.length > 0))
      spec.extraLinear = buildExtraLinear(headInfo, premiseSpecs);

    // makePremises
    if (rule.numPremises === 0) {
      spec.makePremises = () => [];
    } else if (rule.structural) {
      spec.makePremises = (formula, seq) => {
        const cart = Seq.getContext(seq, 'cartesian');
        const linear = Seq.getContext(seq, 'linear');
        return [Seq.fromArrays([...linear, formula], cart, seq.succedent)];
      };
    } else {
      spec.makePremises = buildMakePremises(headInfo, premiseSpecs);
    }

    // Handle key collisions (dereliction and absorption both map to bang_l)
    if (specs[key]) {
      specs[name] = spec;
      if (!alternatives[key]) alternatives[key] = [];
      alternatives[key].push(name);
    } else {
      specs[key] = spec;
    }
  }

  return { specs, alternatives };
}

module.exports = { buildRuleSpecsFromAST };
