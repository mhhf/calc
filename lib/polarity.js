/**
 * Polarity Inference Module
 *
 * Infers polarity and context mode from rule structure at load time.
 * This eliminates the need for explicit polarity specification in ll.json.
 *
 * Algorithm:
 * For each connective with a _R (right-introduction) rule:
 * 1. Extract structural context variables (?X, ?Y) - NOT formula vars (F?A)
 * 2. Analyze how context flows from conclusion to premises:
 *    - PRESERVED: Same var in premise as in conclusion (unary rules)
 *    - COPIED: Same var in ALL premises (additive, e.g., With_R)
 *    - SPLIT: Vars split across premises (multiplicative, e.g., Tensor_R)
 *    - REQUIRES_EMPTY: Conclusion requires empty context I (e.g., Bang_R)
 * 3. Infer polarity:
 *    - NEGATIVE: Context preserved or copied (invertible)
 *    - POSITIVE: Context split or requires empty (not invertible)
 *
 * Special cases:
 * - Lax/Monad: Semantically positive despite context-preserving rules
 *   (modalities representing suspended computations)
 */

/**
 * Extract structural context variables (not formula metavars)
 * @param {string} ruleStr - Rule string like "?X, ?Y |- -- : F?A"
 * @returns {string[]} Array of context variable names
 */
function extractContextVars(ruleStr) {
  // Remove formula/term variable patterns first
  const withoutFormulaVars = ruleStr
    .replace(/F\?[A-Z]+/g, 'FVAR')      // F?A, F?B, etc
    .replace(/AT\?[A-Z]+/g, 'ATVAR')    // AT?A, etc
    .replace(/A\?[A-Z]+/g, 'AVAR')      // A?A, A?B, etc
    .replace(/T\?[A-Z]+/g, 'TVAR');     // T?A, etc

  // Now extract remaining ?X patterns - these are structural vars
  const matches = withoutFormulaVars.match(/\?[A-Z]+/g) || [];
  return [...new Set(matches)];
}

/**
 * Check if conclusion requires empty context (I instead of ?X)
 */
function requiresEmptyContext(conclusionStr) {
  const parts = conclusionStr.split('|-');
  if (parts.length !== 2) return false;
  const antecedent = parts[0].trim();
  return antecedent === 'I';
}

/**
 * Analyze how context variables flow from conclusion to premises
 * @param {string} conclusionStr - Conclusion sequent string
 * @param {string[]} premiseStrs - Array of premise sequent strings
 * @returns {Object} Flow analysis result
 */
function analyzeContextFlow(conclusionStr, premiseStrs) {
  const conclusionVars = extractContextVars(conclusionStr);
  const premiseVarsArray = premiseStrs.map(extractContextVars);

  // Check for empty context requirement
  if (requiresEmptyContext(conclusionStr)) {
    return { type: 'REQUIRES_EMPTY', conclusionVars, premiseVarsArray };
  }

  // If only one premise, check if context is preserved
  if (premiseStrs.length === 1) {
    const premiseVars = premiseVarsArray[0];
    const allPreserved = conclusionVars.every(v => premiseVars.includes(v));
    return {
      type: allPreserved ? 'PRESERVED' : 'UNKNOWN',
      conclusionVars,
      premiseVarsArray
    };
  }

  // Multiple premises - check if split or copied
  if (premiseStrs.length >= 2) {
    const varBehaviors = {};

    for (const v of conclusionVars) {
      const appearsIn = premiseVarsArray
        .map((pVars, i) => pVars.includes(v) ? i : -1)
        .filter(i => i >= 0);

      if (appearsIn.length === premiseStrs.length) {
        varBehaviors[v] = 'COPIED';
      } else if (appearsIn.length === 1) {
        varBehaviors[v] = 'SPLIT';
      } else if (appearsIn.length === 0) {
        varBehaviors[v] = 'ABSENT';
      } else {
        varBehaviors[v] = 'PARTIAL';
      }
    }

    const behaviors = Object.values(varBehaviors);
    let type;
    if (behaviors.every(b => b === 'COPIED')) {
      type = 'COPIED';
    } else if (behaviors.some(b => b === 'SPLIT')) {
      type = 'SPLIT';
    } else {
      type = 'MIXED';
    }

    return { type, conclusionVars, premiseVarsArray, varBehaviors };
  }

  return { type: 'UNKNOWN', conclusionVars, premiseVarsArray };
}

/**
 * Infer polarity from context flow analysis
 * @param {Object} flowAnalysis - Result from analyzeContextFlow
 * @param {string} connective - Connective name (e.g., 'Formula_Lax')
 * @returns {'positive' | 'negative' | 'unknown'}
 */
function inferPolarity(flowAnalysis, connective) {
  // Special cases: modalities semantically positive despite context-preserving rules
  const semanticallyPositive = ['Formula_Lax', 'Formula_Monad'];
  if (semanticallyPositive.includes(connective)) {
    return 'positive';
  }

  switch (flowAnalysis.type) {
    case 'PRESERVED':
    case 'COPIED':
      return 'negative'; // Invertible
    case 'SPLIT':
    case 'REQUIRES_EMPTY':
      return 'positive'; // Not invertible
    default:
      return 'unknown';
  }
}

/**
 * Infer context mode for rules with multiple premises
 * @param {Object} flowAnalysis - Result from analyzeContextFlow
 * @returns {'split' | 'copy' | 'unknown'}
 */
function inferContextMode(flowAnalysis) {
  if (flowAnalysis.type === 'SPLIT') return 'split';
  if (flowAnalysis.type === 'COPIED') return 'copy';
  return 'unknown';
}

/**
 * Map connective names to their right-introduction rules
 */
const CONNECTIVE_TO_RIGHT_RULE = {
  'Formula_Tensor': 'Tensor_R',
  'Formula_Loli': 'Loli_R',
  'Formula_With': 'With_R',
  'Formula_Lax': 'Monad_R',
  'Formula_Bang': 'Bang_R',
  'Formula_Forall': 'Forall_R',
};

/**
 * Infer all polarities from rule definitions
 * @param {Object} rules - Rules object from ll.json
 * @returns {Object} Map of connective name to polarity
 */
function inferAllPolarities(rules) {
  const polarities = {};

  for (const [connective, ruleName] of Object.entries(CONNECTIVE_TO_RIGHT_RULE)) {
    // Find the rule in any category
    let ruleArray = null;
    for (const category of Object.keys(rules)) {
      if (rules[category][ruleName]) {
        ruleArray = rules[category][ruleName];
        break;
      }
    }

    if (!ruleArray) {
      console.warn(`Polarity inference: No rule found for ${connective} (${ruleName})`);
      continue;
    }

    const conclusion = ruleArray[0];
    const premises = ruleArray.slice(1).filter(s => s && s.trim() !== '');

    const flowAnalysis = analyzeContextFlow(conclusion, premises);
    polarities[connective] = inferPolarity(flowAnalysis, connective);
  }

  return polarities;
}

/**
 * Infer context modes for all binary rules
 * @param {Object} rules - Rules object from ll.json
 * @returns {Object} Map of rule name to context mode
 */
function inferAllContextModes(rules) {
  const contextModes = {};

  for (const category of Object.keys(rules)) {
    for (const [ruleName, ruleArray] of Object.entries(rules[category])) {
      if (!Array.isArray(ruleArray) || ruleArray.length < 3) continue;

      const conclusion = ruleArray[0];
      const premises = ruleArray.slice(1).filter(s => s && s.trim() !== '');

      if (premises.length >= 2) {
        const flowAnalysis = analyzeContextFlow(conclusion, premises);
        contextModes[ruleName] = inferContextMode(flowAnalysis);
      }
    }
  }

  return contextModes;
}

module.exports = {
  extractContextVars,
  analyzeContextFlow,
  inferPolarity,
  inferContextMode,
  inferAllPolarities,
  inferAllContextModes,
  CONNECTIVE_TO_RIGHT_RULE,
};
