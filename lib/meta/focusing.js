/**
 * Focusing Metadata
 *
 * Infers polarity and invertibility from rule descriptors:
 * - Empty linear context → positive
 * - Context preserved (1 premise) → negative
 * - Context split across premises → positive
 * - Context copied to all premises → negative
 *
 * No TermApp walking — reads rule.descriptor.contextFlow.
 */

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
    const match = name.match(/^(.+)_[rR]\d*$|^(promotion)$|^(one_r)$/);
    if (!match) continue;

    const connective = match[1] || (name === 'promotion' ? 'bang' : name.replace(/_r$/, ''));
    const flow = rule.descriptor?.contextFlow;
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
      const flow = rule.descriptor?.contextFlow;
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
  flowToPolarity,
  buildFocusingMeta,
  inferPolarityFromRules,
  inferInvertibilityFromRule,
  inferPolarity
};
