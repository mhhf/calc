/**
 * Rule Descriptor Extraction
 *
 * Walks TermApp ASTs from parsed .rules files and produces flat
 * descriptor objects. All TermApp walking is isolated here —
 * downstream code (rule-interpreter, focusing) never sees TermApp.
 *
 * Descriptor shape:
 * {
 *   connective: string|null,  // e.g. 'tensor', 'loli', 'bang'
 *   side: 'l'|'r'|null,       // principal formula position
 *   arity: number,            // connective arity (0, 1, 2)
 *   copyContext: boolean,     // context copied to all premises
 *   emptyLinear: boolean,     // conclusion has empty linear context
 *   contextSplit: boolean,    // context split across premises
 *   contextFlow: string,      // 'empty'|'axiom'|'preserved'|'split'|'copy'
 *   premises: [{ linear?: [idx], cartesian?: [idx], succedent?: idx }]
 * }
 */

// Formula vars vs context (structural) vars
const FORMULA_VARS = new Set(['A', 'B', 'C', 'F']);
const isContextVar = (name) => name.length === 1 && /[A-Z]/.test(name) && !FORMULA_VARS.has(name);

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

function extractPrincipal(node) {
  const { func, args } = flattenApp(node);
  if (!isIdent(func, 'hyp') || args.length !== 2) return null;
  const formula = args[1];
  if (isVar(formula)) return null;

  const { func: conn, args: connArgs } = flattenApp(formula);
  if (conn?.type !== 'TermIdent') return null;

  return {
    connective: conn.name,
    formulaBindings: connArgs
      .map((a, i) => isVar(a) ? { name: a.name, childIdx: i } : null)
      .filter(Boolean)
  };
}

function findPrincipal(node) {
  const { func, args } = flattenApp(node);
  if (isIdent(func, 'comma') && args.length === 2)
    return findPrincipal(args[0]) || findPrincipal(args[1]);
  if (isIdent(func, 'hyp') && args.length === 2)
    return extractPrincipal(node);
  return null;
}

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

function getSuccedentVar(succAST) {
  const { func, args } = flattenApp(succAST);
  return (isIdent(func, 'hyp') && args.length === 2 && isVar(args[1]))
    ? args[1].name : null;
}

// -- Context flow analysis (from focusing.js) --

function extractContextVars(term) {
  const vars = new Set();
  (function walk(node) {
    if (!node) return;
    if (node.type === 'TermVar' && isContextVar(node.name)) vars.add(node.name);
    if (node.type === 'TermApp') { walk(node.func); walk(node.arg); }
  })(term);
  return [...vars];
}

function hasEmptyLinearContext(term) {
  if (!term) return false;
  if (term.type === 'TermApp') {
    const { func, args } = flattenApp(term);
    if (func.type === 'TermIdent' && func.name === 'seq' && args.length >= 2)
      return args[1]?.type === 'TermIdent' && args[1].name === 'empty';
    if (func.type === 'TermIdent' && func.name === 'deriv' && args.length >= 1)
      return hasEmptyLinearContext(args[0]);
  }
  return false;
}

function analyzeContextFlow(rule) {
  if (hasEmptyLinearContext(rule.head)) return 'empty';
  if (rule.premises.length === 0) return 'axiom';
  if (rule.premises.length === 1) return 'preserved';

  const conclusionVars = extractContextVars(rule.head);
  const premiseVarsArray = rule.premises.map(extractContextVars);

  let allCopied = true;
  for (const v of conclusionVars) {
    if (!premiseVarsArray.every(pVars => pVars.includes(v))) allCopied = false;
  }
  return allCopied ? 'copy' : 'split';
}

// -- Head analysis --

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

// -- Main entry point --

/**
 * Extract a flat descriptor from a rule with TermApp head/premises.
 * @param {Object} rule - { head, premises, structural, numPremises }
 * @returns {Object} descriptor
 */
function extractDescriptor(rule) {
  const headInfo = analyzeHead(rule);
  const flow = analyzeContextFlow(rule);
  const principal = headInfo.principal;

  const descriptor = {
    connective: principal ? principal.connective : null,
    side: headInfo.principalSide,
    arity: principal ? principal.formulaBindings.length : 0,
    copyContext: flow === 'copy',
    emptyLinear: headInfo.emptyLinear,
    contextSplit: flow === 'split',
    contextFlow: flow,
  };

  // Build premise descriptors using child index mapping
  if (rule.premises.length > 0 && principal) {
    const bindingMap = {};
    for (const b of principal.formulaBindings) {
      bindingMap[b.name] = b.childIdx;
    }

    descriptor.premises = rule.premises.map(p => {
      const ps = analyzePremise(p, headInfo);
      const pDesc = {};

      if (ps.extraLinearFormulas.length > 0) {
        pDesc.linear = ps.extraLinearFormulas.map(v => bindingMap[v] ?? -1);
      }
      if (ps.extraCartesianFormulas.length > 0) {
        pDesc.cartesian = ps.extraCartesianFormulas.map(v => bindingMap[v] ?? -1);
      }
      if (ps.succedentVar != null) {
        pDesc.succedent = bindingMap[ps.succedentVar] ?? -1;
      }

      return pDesc;
    });
  } else {
    descriptor.premises = [];
  }

  return descriptor;
}

module.exports = { extractDescriptor, analyzeContextFlow };
