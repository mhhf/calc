/**
 * Focusing Metadata - Simplified
 *
 * Infers polarity and invertibility from rule structure:
 * - Empty linear context → positive
 * - Context preserved (1 premise) → negative
 * - Context split across premises → positive
 * - Context copied to all premises → negative
 */

// Structure vars (context positions) vs formula vars (excluded from flow analysis)
// Context: D, E, G, H, ... Z (single uppercase letters except formula vars)
// Formula: A, B, C, F (excluded from context flow analysis)
const FORMULA_VARS = new Set(['A', 'B', 'C', 'F']);
const isContextVar = (name) => name.length === 1 && /[A-Z]/.test(name) && !FORMULA_VARS.has(name);

/**
 * Extract context variable names from AST term
 */
function extractContextVars(term) {
  const vars = new Set();

  (function walk(node) {
    if (!node) return;
    if (node.type === 'TermVar' && isContextVar(node.name)) {
      vars.add(node.name);
    }
    if (node.type === 'TermApp') {
      walk(node.func);
      walk(node.arg);
    }
  })(term);

  return [...vars];
}

/**
 * Flatten nested TermApp into { func, args }
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
 * Check if term has empty linear context (seq(G, empty, C) pattern)
 */
function hasEmptyLinearContext(term) {
  if (!term) return false;

  if (term.type === 'TermApp') {
    const { func, args } = flattenApp(term);

    // seq(G, D, C) - check if D (linear context at position 1) is empty
    if (func.type === 'TermIdent' && func.name === 'seq' && args.length >= 2) {
      return args[1]?.type === 'TermIdent' && args[1].name === 'empty';
    }

    // Recurse into deriv(seq(...))
    if (func.type === 'TermIdent' && func.name === 'deriv' && args.length >= 1) {
      return hasEmptyLinearContext(args[0]);
    }
  }
  return false;
}

/**
 * Analyze context flow: how do context vars flow from conclusion to premises?
 * Returns: 'empty' | 'preserved' | 'split' | 'copy' | 'unknown'
 */
function analyzeContextFlow(rule) {
  if (hasEmptyLinearContext(rule.head)) return 'empty';
  if (rule.premises.length === 0) return 'axiom';
  if (rule.premises.length === 1) return 'preserved';

  // Multiple premises: check if context vars are split or copied
  const conclusionVars = extractContextVars(rule.head);
  const premiseVarsArray = rule.premises.map(extractContextVars);

  // For each conclusion var, check if it appears in all premises (copy) or just some (split)
  let allCopied = true;
  for (const v of conclusionVars) {
    const appearsInAll = premiseVarsArray.every(pVars => pVars.includes(v));
    if (!appearsInAll) allCopied = false;
  }

  return allCopied ? 'copy' : 'split';
}

/**
 * Map context flow to polarity
 */
function flowToPolarity(flow) {
  if (flow === 'empty' || flow === 'split') return 'positive';
  if (flow === 'preserved' || flow === 'copy') return 'negative';
  return null;
}

/**
 * Infer polarity for all connectives from right-introduction rules
 */
function inferPolarityFromRules(rules) {
  const polarity = {};

  for (const [name, rule] of Object.entries(rules)) {
    if (rule.structural) continue;

    // Only right rules determine polarity
    const match = name.match(/^(.+)_[rR]$|^(promotion)$|^(one_r)$/);
    if (!match) continue;

    const connective = match[1] || (name === 'promotion' ? 'bang' : name.replace(/_r$/, ''));
    const flow = analyzeContextFlow(rule);
    const pol = flowToPolarity(flow);

    if (pol) polarity[connective] = pol;
  }

  return polarity;
}

/**
 * Infer invertibility from polarity and rule position
 *
 * Focusing discipline:
 * - Positive + left = invertible (e.g., tensor_l)
 * - Positive + right = NOT invertible (e.g., tensor_r)
 * - Negative + right = invertible (e.g., loli_r)
 * - Negative + left = NOT invertible (e.g., loli_l)
 */
function inferInvertibilityFromRule(ruleName, rule, polarity) {
  if (rule.structural) return true;

  const match = ruleName.match(/^(.+)_([lr])(\d?)$/i);
  if (!match) return null;

  const [, connective, side] = match;
  const pol = polarity[connective];
  if (!pol) return null;

  const isRight = side.toLowerCase() === 'r';
  return pol === 'negative' ? isRight : !isRight;
}

/**
 * Build focusing metadata for a calculus (for validation and debugging)
 */
function buildFocusingMeta(calculus) {
  const { rules, polarity: explicitPolarity } = calculus;

  // Infer polarity from rules
  const inferredPolarity = inferPolarityFromRules(rules);

  // Group rules by connective
  const rulesByConnective = {};
  for (const [name, rule] of Object.entries(rules)) {
    if (rule.structural) continue;
    const match = name.match(/^(.+)_([lr])(\d?)$/i);
    if (match) {
      const [, conn, side] = match;
      if (!rulesByConnective[conn]) rulesByConnective[conn] = { left: [], right: [] };
      rulesByConnective[conn][side === 'l' ? 'left' : 'right'].push(name);
    }
  }

  // Context modes for binary rules
  const contextModes = {};
  for (const [name, rule] of Object.entries(rules)) {
    if (!rule.structural && rule.numPremises >= 2) {
      const flow = analyzeContextFlow(rule);
      contextModes[name] = flow === 'copy' ? 'copy' : flow === 'split' ? 'split' : 'unknown';
    }
  }

  return {
    polarity: explicitPolarity,
    inferredPolarity,
    contextModes,
    rulesByConnective,

    validate() {
      const mismatches = [];
      for (const [conn, inferred] of Object.entries(inferredPolarity)) {
        const explicit = explicitPolarity[conn];
        if (explicit && explicit !== inferred) {
          mismatches.push({ connective: conn, explicit, inferred });
        }
      }
      return mismatches;
    }
  };
}

// Legacy exports for compatibility
const inferPolarity = (flowResult) => flowToPolarity(flowResult.type || flowResult);

module.exports = {
  analyzeContextFlow,
  extractContextVars,
  inferPolarity,
  buildFocusingMeta,
  inferPolarityFromRules,
  inferInvertibilityFromRule
};
