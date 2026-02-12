/**
 * Generic Rule Interpreter
 *
 * Reads rule ASTs from calculus.rules and produces spec objects
 * identical to the hand-coded buildRuleSpecs in focused/prover.js.
 *
 * Each spec has: numPremises, copyContext, makePremises, and optionally
 * requiresEmptyDelta, structural, movesToCartesian, extraLinear.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { analyzeContextFlow } = require('../meta/focusing');

// Formula vars (A, B, C, F) vs context vars (D, D', G, etc.)
const FORMULA_VARS = new Set(['A', 'B', 'C', 'F']);

/**
 * Flatten curried TermApp chain into { func, args }
 */
function flattenApp(term) {
  const args = [];
  while (term?.type === 'TermApp') {
    args.unshift(term.arg);
    term = term.func;
  }
  return { func: term, args };
}

/**
 * Check if AST node is a TermVar (metavariable)
 */
function isVar(node) {
  return node?.type === 'TermVar';
}

/**
 * Check if AST node is a TermIdent with a given name
 */
function isIdent(node, name) {
  return node?.type === 'TermIdent' && node.name === name;
}

/**
 * Check if a var name is a formula variable
 */
function isFormulaVar(name) {
  // Formula vars: single letter A-F (but not D,E which are context)
  // Actually the convention is A, B, C, F are formula vars
  return FORMULA_VARS.has(name);
}

/**
 * Parse a seq(...) AST into { cart, linear, succ }
 * Each is the raw AST subtree.
 */
function parseSeq(seqAST) {
  const { func, args } = flattenApp(seqAST);
  if (!isIdent(func, 'seq') || args.length !== 3) {
    throw new Error(`Expected seq(cart, linear, succ), got ${func?.name} with ${args.length} args`);
  }
  return { cart: args[0], linear: args[1], succ: args[2] };
}

/**
 * Parse deriv(seq(...)) into the seq parts
 */
function parseDeriv(term) {
  const { func, args } = flattenApp(term);
  if (!isIdent(func, 'deriv') || args.length !== 1) {
    throw new Error(`Expected deriv(seq(...)), got ${func?.name}`);
  }
  return parseSeq(args[0]);
}

/**
 * Extract the principal formula from a hyp(any, connective(A, B)) term.
 * Returns { connective, formulaBindings: [{name, childIdx}] } or null.
 */
function extractPrincipal(hypAST) {
  const { func, args } = flattenApp(hypAST);
  if (!isIdent(func, 'hyp') || args.length !== 2) return null;
  // args[1] is the formula: either a TermVar or connective(A, B, ...)
  const formulaAST = args[1];
  if (isVar(formulaAST)) return null; // Just a variable, no connective

  const { func: connFunc, args: connArgs } = flattenApp(formulaAST);
  if (connFunc?.type !== 'TermIdent') return null;

  const bindings = [];
  for (let i = 0; i < connArgs.length; i++) {
    if (isVar(connArgs[i])) {
      bindings.push({ name: connArgs[i].name, childIdx: i });
    }
  }

  return {
    connective: connFunc.name,
    formulaBindings: bindings
  };
}

/**
 * Collect all hyp(any, X) nodes from a linear/cart context AST.
 * Returns array of { varName, AST } for formula vars in hyp positions.
 */
function collectHypFormulas(contextAST) {
  const results = [];

  function walk(node) {
    const { func, args } = flattenApp(node);
    if (isIdent(func, 'comma') && args.length === 2) {
      walk(args[0]);
      walk(args[1]);
    } else if (isIdent(func, 'hyp') && args.length === 2) {
      const formulaPart = args[1];
      if (isVar(formulaPart)) {
        results.push({ varName: formulaPart.name });
      } else {
        // connective(A, B) — extract sub-vars
        const { func: cFunc, args: cArgs } = flattenApp(formulaPart);
        if (cFunc?.type === 'TermIdent') {
          for (let i = 0; i < cArgs.length; i++) {
            if (isVar(cArgs[i])) {
              results.push({ varName: cArgs[i].name, connective: cFunc.name, childIdx: i });
            }
          }
        }
      }
    } else if (isVar(node)) {
      // Context variable (D, D', G, etc.) - skip
    } else if (isIdent(node, 'empty')) {
      // Empty context - skip
    }
  }

  walk(contextAST);
  return results;
}

/**
 * Collect formula var names that appear as hyp(any, VAR) in a context AST.
 * Only returns simple formula vars (not wrapped in connective).
 */
function collectSimpleHypVars(contextAST) {
  const results = [];

  function walk(node) {
    const { func, args } = flattenApp(node);
    if (isIdent(func, 'comma') && args.length === 2) {
      walk(args[0]);
      walk(args[1]);
    } else if (isIdent(func, 'hyp') && args.length === 2) {
      const formulaPart = args[1];
      if (isVar(formulaPart)) {
        results.push(formulaPart.name);
      }
    }
  }

  walk(contextAST);
  return results;
}

/**
 * Get the succedent variable name from hyp(any, X) or null
 */
function getSuccedentVar(succAST) {
  const { func, args } = flattenApp(succAST);
  if (isIdent(func, 'hyp') && args.length === 2) {
    const formulaPart = args[1];
    if (isVar(formulaPart)) {
      return formulaPart.name;
    }
  }
  return null;
}

/**
 * Collect context var names from AST (non-formula TermVars)
 */
function collectContextVars(ast) {
  const vars = new Set();
  function walk(node) {
    if (!node) return;
    if (isVar(node) && !isFormulaVar(node.name)) {
      vars.add(node.name);
    }
    if (node.type === 'TermApp') {
      walk(node.func);
      walk(node.arg);
    }
  }
  walk(ast);
  return vars;
}

/**
 * Analyze the head of a rule to extract structural information.
 */
function analyzeHead(rule) {
  const head = parseDeriv(rule.head);

  // Determine principal formula location and bindings
  // Check succedent for principal
  const succPrincipal = extractPrincipal(head.succ);

  // Check linear context for principal
  let linPrincipal = null;
  let principalSide = null;

  if (succPrincipal) {
    principalSide = 'r';
  } else {
    // Walk linear to find the hyp with a connective
    function findPrincipalInContext(node) {
      const { func, args } = flattenApp(node);
      if (isIdent(func, 'comma') && args.length === 2) {
        return findPrincipalInContext(args[0]) || findPrincipalInContext(args[1]);
      }
      if (isIdent(func, 'hyp') && args.length === 2) {
        const p = extractPrincipal(node);
        if (p) return p;
      }
      return null;
    }
    linPrincipal = findPrincipalInContext(head.linear);
    if (linPrincipal) principalSide = 'l';
  }

  // For structural rules (copy), principal may be in cartesian
  let cartPrincipal = null;
  if (!succPrincipal && !linPrincipal) {
    function findPrincipalInCart(node) {
      const { func, args } = flattenApp(node);
      if (isIdent(func, 'comma') && args.length === 2) {
        return findPrincipalInCart(args[0]) || findPrincipalInCart(args[1]);
      }
      if (isIdent(func, 'hyp') && args.length === 2) {
        return extractPrincipal(node);
      }
      return null;
    }
    cartPrincipal = findPrincipalInCart(head.cart);
    if (cartPrincipal) principalSide = 'cart';
  }

  const principal = succPrincipal || linPrincipal || cartPrincipal;
  const emptyLinear = isIdent(head.linear, 'empty');

  // Collect context vars from head positions
  const headLinearContextVars = collectContextVars(head.linear);
  const headCartContextVars = collectContextVars(head.cart);

  return {
    head,
    principal,
    principalSide,
    emptyLinear,
    headLinearContextVars,
    headCartContextVars
  };
}

/**
 * Analyze a premise relative to the head.
 */
function analyzePremise(premiseAST, headInfo) {
  const premise = parseDeriv(premiseAST);

  // Collect formula vars that appear as hyp(any, VAR) in premise linear context
  // that are NOT context vars from the head's linear context
  const premiseLinearHypVars = collectSimpleHypVars(premise.linear);
  const extraLinearFormulas = premiseLinearHypVars.filter(v => isFormulaVar(v));

  // Collect formula vars in premise cartesian that aren't in head cartesian
  const premiseCartHypVars = collectSimpleHypVars(premise.cart);
  const headCartHypVars = collectSimpleHypVars(headInfo.head.cart);
  const extraCartesianFormulas = premiseCartHypVars.filter(
    v => isFormulaVar(v) && !headCartHypVars.includes(v)
  );

  // Determine succedent
  const succVar = getSuccedentVar(premise.succ);
  // If succedent var differs from head's succedent var, it's a new binding
  const headSuccVar = getSuccedentVar(headInfo.head.succ);

  return {
    extraLinearFormulas,
    extraCartesianFormulas,
    succedentVar: succVar !== headSuccVar ? succVar : null
  };
}

/**
 * Determine the spec key name for a rule.
 * Most rules: name as-is. promotion -> bang_r, dereliction -> bang_l.
 */
function specKeyForRule(rule, headInfo) {
  const name = rule.name;

  // id is handled separately
  if (name === 'id') return null;

  // Rules with non-standard names: use connective + side
  if (headInfo.principal && headInfo.principalSide !== 'cart') {
    const expectedName = `${headInfo.principal.connective}_${headInfo.principalSide}`;
    // Check if name matches expected pattern (includes with_l1, with_l2)
    if (name === expectedName || name.startsWith(expectedName.replace(/_[lr]$/, '') + '_')) {
      return name;
    }
    // Non-standard name: promotion -> bang_r, dereliction -> bang_l
    return expectedName;
  }

  // Structural rules: keep original name
  return name;
}

/**
 * Build rule specs from calculus rule ASTs.
 *
 * @param {Object} calculus - Loaded calculus with .rules
 * @returns {{ specs: Object, alternatives: Object }}
 */
function buildRuleSpecsFromAST(calculus) {
  const { rules } = calculus;
  const specs = {};
  const alternatives = {};

  for (const [name, rule] of Object.entries(rules)) {
    if (name === 'id') continue; // Handled separately by prover

    const headInfo = analyzeHead(rule);
    const key = specKeyForRule(rule, headInfo);
    if (!key) continue;

    const flow = analyzeContextFlow(rule);
    const copyContext = flow === 'copy';

    // Analyze premises
    const premiseSpecs = rule.premises.map(p => analyzePremise(p, headInfo));

    // Build metadata
    const spec = {
      numPremises: rule.numPremises,
      copyContext,
    };

    // requiresEmptyDelta: head has empty linear AND has premises
    if (headInfo.emptyLinear && rule.numPremises > 0) {
      spec.requiresEmptyDelta = true;
    }

    // structural
    if (rule.structural) {
      spec.structural = true;
    }

    // movesToCartesian: any premise has formula vars in cartesian that head doesn't
    if (premiseSpecs.some(ps => ps.extraCartesianFormulas.length > 0)) {
      spec.movesToCartesian = true;
    }

    // extraLinear: for rules that add formula children to linear context
    // Skip for structural rules (copy) where principal is in cartesian
    const hasExtraLinear = !rule.structural &&
      premiseSpecs.some(ps => ps.extraLinearFormulas.length > 0);
    if (hasExtraLinear) {
      if (premiseSpecs.length === 1) {
        // Single premise: extraLinear returns all extra formulas
        spec.extraLinear = (formula) => {
          return premiseSpecs[0].extraLinearFormulas.map(varName => {
            const binding = headInfo.principal.formulaBindings.find(b => b.name === varName);
            return binding ? Store.child(formula, binding.childIdx) : formula;
          });
        };
      } else {
        // Multiple premises: extraLinear takes premiseIdx
        spec.extraLinear = (formula, premiseIdx) => {
          const ps = premiseSpecs[premiseIdx !== undefined ? premiseIdx : 0];
          return ps.extraLinearFormulas.map(varName => {
            const binding = headInfo.principal.formulaBindings.find(b => b.name === varName);
            return binding ? Store.child(formula, binding.childIdx) : formula;
          });
        };
      }
    }

    // Build makePremises
    if (rule.numPremises === 0) {
      // Axiom rule (one_r): no premises
      spec.makePremises = (formula, seq, idx) => [];
    } else if (rule.structural) {
      // Special case: copy (structural rule, copies formula from cart to linear)
      spec.makePremises = (formula, seq, idx) => {
        const cart = Seq.getContext(seq, 'cartesian');
        const linear = Seq.getContext(seq, 'linear');
        return [Seq.fromArrays([...linear, formula], cart, seq.succedent)];
      };
    } else {
      spec.makePremises = buildMakePremises(headInfo, premiseSpecs);
    }

    // Check for key collision (e.g., dereliction and absorption both map to bang_l)
    if (specs[key]) {
      // Key already taken: store under original name and record as alternative
      specs[name] = spec;
      if (!alternatives[key]) alternatives[key] = [];
      alternatives[key].push(name);
    } else {
      specs[key] = spec;
      // If key differs from name, record for reverse lookup
      if (key !== name) {
        // e.g., promotion -> bang_r: no collision, just a rename
      }
    }
  }

  return { specs, alternatives };
}

/**
 * Build the makePremises function for a non-structural rule.
 */
function buildMakePremises(headInfo, premiseSpecs) {
  const { principal } = headInfo;

  return (formula, seq, idx) => {
    // Bind formula vars from principal: A -> Store.child(formula, 0), etc.
    const bindings = {};
    if (principal) {
      for (const b of principal.formulaBindings) {
        bindings[b.name] = Store.child(formula, b.childIdx);
      }
    }

    const cart = Seq.getContext(seq, 'cartesian');

    return premiseSpecs.map(ps => {
      const linear = ps.extraLinearFormulas.map(v => {
        if (bindings[v] !== undefined) return bindings[v];
        return formula; // fallback: shouldn't happen
      });

      const extraCart = ps.extraCartesianFormulas.map(v => {
        if (bindings[v] !== undefined) return bindings[v];
        return formula;
      });

      const premCart = extraCart.length > 0 ? [...cart, ...extraCart] : cart;

      const succ = ps.succedentVar
        ? (bindings[ps.succedentVar] !== undefined ? bindings[ps.succedentVar] : seq.succedent)
        : seq.succedent;

      return Seq.fromArrays(linear, premCart, succ);
    });
  };
}

module.exports = { buildRuleSpecsFromAST };
