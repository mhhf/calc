/**
 * Browser-compatible proof logic for the interactive prover.
 * Provides rule matching, application, and proof tree manipulation.
 */

// @ts-ignore - CommonJS module
import * as CalcModule from '../../../lib/calc.js';
// @ts-ignore - CommonJS module
import * as SequentModule from '../../../lib/sequent.js';
// @ts-ignore - CommonJS module
import * as PTModule from '../../../lib/pt.js';
// @ts-ignore - CommonJS module
import * as ProofstateModule from '../../../lib/proofstate.js';
// @ts-ignore - CommonJS module
import * as NodeModule from '../../../lib/node.js';
// @ts-ignore - CommonJS module
import * as mguModule from '../../../lib/mgu.js';
// @ts-ignore - Generated parser
import * as parserMod from '../../../out/parser.js';

const Calc = (CalcModule as any).default || CalcModule;
const Sequent = (SequentModule as any).default || SequentModule;
const PT = (PTModule as any).default || PTModule;
const Proofstate = (ProofstateModule as any).default || ProofstateModule;
const Node = (NodeModule as any).default || NodeModule;
const mgu = (mguModule as any).default || mguModule;
const parserModule = (parserMod as any).default || parserMod;

// Set up parser
parserModule.parser.yy.Node = Node;

// Types
export interface ApplicableRule {
  name: string;
  category: string;
  ruleStrings: string[];  // Original rule strings for display
  premises: any[];        // Sequent objects after applying to current
  position: string;       // 'L' or 'R' or specific id
  principalFormula?: string;       // The formula being decomposed (ASCII)
  principalFormulaLatex?: string;  // The formula being decomposed (LaTeX)
  splitContext?: boolean; // True if this rule splits context (e.g., Tensor_R)
}

export interface ProofTreeNode {
  conclusion: any;        // Sequent
  premisses: ProofTreeNode[];
  type: string;           // Rule name or '???'
  proven: boolean;
  delta_in: Record<string, any>;
  delta_out: Record<string, any>;
}

export interface Ruleset {
  rules: Record<string, any[]>;
  getRule: (name: string) => any[];
  bwd: string[];
}

// Global ruleset cache
let cachedRuleset: Ruleset | null = null;

/**
 * Initialize the ruleset for browser use.
 * This version doesn't read .llt files - it only uses rules from ll.json
 */
export function initBrowserRuleset(): Ruleset {
  if (cachedRuleset) return cachedRuleset;

  const calc = Calc.calc;
  const parser = parserModule.parser;

  const allRules: Record<string, any[]> = {};
  const bwd: string[] = [];

  // Load rules from ll.json (skip structural rules for now)
  Object.keys(calc.rules).forEach((ctxName: string) => {
    if (ctxName === 'RuleStruct') return;
    const ctx = calc.rules[ctxName];
    Object.keys(ctx).forEach((ruleName: string) => {
      allRules[ruleName] = ctx[ruleName];
    });
  });

  // Parse rule strings into Sequent objects
  Object.keys(allRules).forEach((ruleName: string) => {
    const rule = allRules[ruleName];
    const parsed = rule
      .filter((f: string) => f !== '')
      .map((f: string) => parser.parse(f))
      .map((f: any) => Sequent.fromTree(f));
    allRules[ruleName] = parsed;
  });

  const getRule = (name: string): any[] => {
    const rule = allRules[name];
    if (!rule) return [];
    const unique = Sequent.renameUniqueArray(rule);
    return unique.seqs;
  };

  cachedRuleset = { rules: allRules, getRule, bwd };
  return cachedRuleset;
}

/**
 * Parse a sequent string into a Sequent object
 */
export function parseSequent(input: string): any {
  const parser = parserModule.parser;
  const node = parser.parse(input);
  return Sequent.fromTree(node);
}

/**
 * Create a new proof tree from a sequent
 */
export function createProofTree(sequent: any): ProofTreeNode {
  return new PT({ conclusion: sequent });
}

/**
 * Check if a proof tree is complete (all leaves are proven)
 */
export function isProofComplete(pt: ProofTreeNode): boolean {
  if (pt.type === '???') return false;
  if (pt.premisses.length === 0) return true;
  return pt.premisses.every((p: ProofTreeNode) => isProofComplete(p));
}

/**
 * Count proven and unproven nodes
 */
export function countNodes(pt: ProofTreeNode): { proven: number; unproven: number } {
  let proven = 0;
  let unproven = 0;

  function traverse(node: ProofTreeNode) {
    if (node.type === '???') {
      unproven++;
    } else if (node.premisses.length === 0) {
      proven++;
    }
    node.premisses.forEach(traverse);
  }

  traverse(pt);
  return { proven, unproven };
}

/**
 * Get a node at a specific path in the proof tree
 * Path is an array of indices: [0, 1] means first child, then second child
 */
export function getNodeAtPath(pt: ProofTreeNode, path: number[]): ProofTreeNode | null {
  if (path.length === 0) return pt;
  const [head, ...tail] = path;
  if (head >= pt.premisses.length) return null;
  return getNodeAtPath(pt.premisses[head], tail);
}

/**
 * Create a new tree with a node replaced at a specific path
 * Returns a new tree (immutable update)
 */
export function setNodeAtPath(
  root: ProofTreeNode,
  path: number[],
  newNode: ProofTreeNode
): ProofTreeNode {
  if (path.length === 0) return newNode;

  const [head, ...tail] = path;
  const newPremisses = root.premisses.map((p: ProofTreeNode, i: number) =>
    i === head ? setNodeAtPath(p, tail, newNode) : p
  );

  // Create new PT with updated premisses
  const updated = new PT({
    conclusion: root.conclusion,
    premisses: newPremisses,
    type: root.type,
  });
  updated.delta_in = root.delta_in;
  updated.delta_out = root.delta_out;
  updated.proven = root.proven;
  // Preserve proverState (focus info)
  if ((root as any).proverState) {
    updated.proverState = (root as any).proverState;
  }

  return updated;
}

/**
 * Deep clone a proof tree
 */
export function cloneProofTree(pt: ProofTreeNode): ProofTreeNode {
  const cloned = new PT({
    conclusion: Sequent.copy(pt.conclusion),
    premisses: pt.premisses.map((p: ProofTreeNode) => cloneProofTree(p)),
    type: pt.type,
  });
  cloned.delta_in = { ...pt.delta_in };
  cloned.delta_out = { ...pt.delta_out };
  cloned.proven = pt.proven;
  // Preserve proverState (focus info) - copy to ensure independence
  if ((pt as any).proverState) {
    cloned.proverState = (pt as any).proverState.copy();
  }
  return cloned;
}

/**
 * Get the category of a rule based on its name
 */
function getRuleCategory(ruleName: string): string {
  const calc = Calc.calc;
  for (const ctxName of Object.keys(calc.rules)) {
    if (ruleName in calc.rules[ctxName]) {
      return ctxName;
    }
  }
  return 'Unknown';
}

/**
 * Get the original rule strings for display
 */
function getRuleStrings(ruleName: string): string[] {
  const calc = Calc.calc;
  for (const ctxName of Object.keys(calc.rules)) {
    if (ruleName in calc.rules[ctxName]) {
      return calc.rules[ctxName][ruleName];
    }
  }
  return [];
}

/**
 * Focus propagation patterns for connectives.
 * Maps rule name to focus info for conclusion and each premise.
 *
 * In focused proof search:
 * - Synchronous rules (positive on R, negative on L) propagate focus
 * - Each premise indicates where focus goes: 'principal' (the sub-formula),
 *   'result' (e.g., B in Loli_L premise 2), or null (no focus)
 */
const FOCUS_PATTERNS: Record<string, {
  conclusionFocus: 'principal';  // The principal formula is focused
  premiseFocus: Array<{ position: 'L' | 'R'; formula: string } | null>;
}> = {
  // Loli_L: Γ, Δ, [A -o B] ⊢ C  →  Γ ⊢ [A]  and  Δ, [B] ⊢ C
  'Loli_L': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'A' },  // Premise 1: focus on A (right)
      { position: 'L', formula: 'B' },  // Premise 2: focus on B (left)
    ]
  },
  // Tensor_R: Γ, Δ ⊢ [A * B]  →  Γ ⊢ [A]  and  Δ ⊢ [B]
  'Tensor_R': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'A' },  // Premise 1: focus on A (right)
      { position: 'R', formula: 'B' },  // Premise 2: focus on B (right)
    ]
  },
  // Loli_R: Γ ⊢ [A -o B]  →  Γ, A ⊢ [B] (focus stays on right)
  'Loli_R': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'B' },  // Focus continues on B
    ]
  },
  // Tensor_L: [A * B], Γ ⊢ C  →  A, B, Γ ⊢ C (async - focus blurs)
  // No entry means no focus propagation (async rule)

  // With_L: [A & B], Γ ⊢ C  →  [A], Γ ⊢ C (or B)
  'With_L': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'L', formula: 'A' },  // Focus on A
    ]
  },
  'With_L2': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'L', formula: 'B' },  // Focus on B
    ]
  },
  // Plus_R: Γ ⊢ [A + B]  →  Γ ⊢ [A] (or B)
  'Plus_R': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'A' },
    ]
  },
  'Plus_R2': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'B' },
    ]
  },
  // Bang_L: [!A], Γ ⊢ C  →  !A; Γ ⊢ C (moves to persistent, focus blurs)
  // No focus propagation

  // Bang_R: ⊢ [!A]  →  ⊢ [A] (focus continues)
  'Bang_R': {
    conclusionFocus: 'principal',
    premiseFocus: [
      { position: 'R', formula: 'A' },
    ]
  },
};

/**
 * Generate focused rule strings with bracket notation.
 * Takes the original rule strings and adds [brackets] around focused formulas.
 *
 * @param ruleName - The rule name (e.g., 'Loli_L')
 * @param position - 'L' or 'R' indicating which side the principal is on
 * @returns Array of rule strings with focus brackets, or original strings if no pattern
 */
function getFocusedRuleStrings(ruleName: string, position: 'L' | 'R'): string[] {
  const originalStrings = getRuleStrings(ruleName);
  if (originalStrings.length === 0) return originalStrings;

  const pattern = FOCUS_PATTERNS[ruleName];
  if (!pattern) {
    // No focus pattern defined - return original (async rules)
    return originalStrings;
  }

  const [conclusion, ...premises] = originalStrings;

  // Add focus to conclusion's principal formula
  let focusedConclusion = conclusion;
  if (position === 'R') {
    // Focus on right: wrap the succedent formula
    // Pattern: ... |- -- : F?A * F?B  →  ... |- -- : [F?A * F?B]
    focusedConclusion = conclusion.replace(
      /\|-\s*--\s*:\s*(.+)$/,
      (_, formula) => `|- -- : [${formula.trim()}]`
    );
  } else {
    // Focus on left: wrap the principal connective formula
    // This is trickier - need to identify the principal
    // For now, wrap the main connective pattern
    // Pattern: ?X, ?Y, -- : F?A -o F?B |- ...  →  ?X, ?Y, [-- : F?A -o F?B] |- ...

    // Find the principal formula pattern based on rule name
    const connectivePatterns: Record<string, RegExp> = {
      'Loli_L': /(--\s*:\s*F\?[A-Z]\s*-o\s*F\?[A-Z])/,
      'Tensor_L': /(--\s*:\s*F\?[A-Z]\s*\*\s*F\?[A-Z])/,
      'With_L': /(--\s*:\s*F\?[A-Z]\s*&\s*F\?[A-Z])/,
      'With_L2': /(--\s*:\s*F\?[A-Z]\s*&\s*F\?[A-Z])/,
      'Plus_L': /(--\s*:\s*F\?[A-Z]\s*\+\s*F\?[A-Z])/,
      'Bang_L': /(--\s*:\s*!\s*F\?[A-Z])/,
    };

    const connPattern = connectivePatterns[ruleName];
    if (connPattern) {
      focusedConclusion = conclusion.replace(connPattern, '[$1]');
    }
  }

  // Add focus to premises
  const focusedPremises = premises.map((premise, i) => {
    const premiseFocus = pattern.premiseFocus[i];
    if (!premiseFocus) return premise;

    if (premiseFocus.position === 'R') {
      // Focus on right succedent
      return premise.replace(
        /\|-\s*--\s*:\s*(.+)$/,
        (_, formula) => `|- -- : [${formula.trim()}]`
      );
    } else {
      // Focus on left - find the specific formula
      // Map formula letter to pattern
      const formulaVar = premiseFocus.formula;
      const pattern = new RegExp(`(--\\s*:\\s*F\\?${formulaVar})(?![A-Z])`);
      return premise.replace(pattern, '[$1]');
    }
  });

  return [focusedConclusion, ...focusedPremises];
}

/**
 * Get the connective name from a formula node.
 * For example, returns "Lolli" for A -o B, "Tensor" for A * B, etc.
 */
function getConnectiveName(formula: any): string | null {
  if (!formula || !formula.id) return null;
  const rule = Calc.db.rules[formula.id];
  if (!rule) return null;

  const ruleName = rule.ruleName;

  // Handle focused formulas - get the inner formula
  if (ruleName === 'Focused_Formula' && formula.vals) {
    return getConnectiveName(formula.vals[0]);
  }

  // Extract connective name from "Formula_X" pattern
  const match = ruleName.match(/^Formula_(.+)$/);
  if (match) {
    return match[1]; // "Lolli", "Tensor", "Plus", "With", "Bang", "Atprop", "Freevar"
  }

  return null;
}

/**
 * Check if a formula is atomic (not a complex connective that can be decomposed)
 */
function isAtomicFormula(formula: any): boolean {
  const name = getConnectiveName(formula);
  return name === 'Atprop' || name === 'Freevar';
}

/**
 * Get the formula from a term structure like "-- : A"
 * The term has structure: vals[0] = term marker, vals[1] = the actual formula
 */
function extractFormula(term: any): any {
  if (!term || !term.vals) return null;

  const rule = Calc.db.rules[term.id];
  if (!rule) return term;

  // Structure_Term_Formula or Structure_Focused_Term_Formula
  if (rule.ruleName.includes('Term_Formula') || rule.ruleName.includes('Focused_Term')) {
    return term.vals[1];
  }

  return term;
}

/**
 * Get the principal formula for a rule application.
 * This is the formula being decomposed (e.g., A * B for Tensor_R).
 */
function getPrincipalFormula(seq: any, position: string): { ascii: string; latex: string } | null {
  try {
    let formula: any;
    if (position === 'R') {
      formula = extractFormula(seq.succedent);
    } else {
      const entry = seq.linear_ctx[position];
      if (entry && entry.val) {
        formula = extractFormula(entry.val);
      }
    }

    if (formula) {
      return {
        ascii: formula.toString(),
        latex: formula.toString({ style: 'latex' }),
      };
    }
  } catch (e) {
    // Ignore errors
  }
  return null;
}

/**
 * Clean premises by removing structural metavariables from display.
 * The context vars like ?X, ?Y are distributed during proof search,
 * so for preview purposes we show them as empty or simplified.
 */
function cleanPremisesForDisplay(premises: any[]): any[] {
  return premises.map(premise => {
    // For display, we remove entries that are just structural metavars
    // The actual premise still has them for proof search
    return premise;
  });
}

/**
 * Check if a rule splits the context (has multiple context metavars like ?X, ?Y).
 * These rules need special handling in the UI.
 */
function isContextSplittingRule(ruleName: string): boolean {
  // Rules known to split context: Tensor_R, Loli_L
  // These have ?X, ?Y in conclusion with ?X going to one premise and ?Y to another
  const splittingRules = ['Tensor_R', 'Loli_L'];
  return splittingRules.includes(ruleName);
}

/**
 * Options for getting applicable rules
 */
export interface GetRulesOptions {
  /** 'unfocused' = direct rule application, 'focused' = show focus choices */
  mode?: 'unfocused' | 'focused';
  /** Current focus state (for focused mode) */
  focusState?: { position: string | null; id: string | null };
}

/**
 * Find all rules that apply to a sequent.
 *
 * In UNFOCUSED mode (default for manual proofs):
 * - Rules are determined by the connective type at each position
 * - No focusing discipline - any rule matching a connective applies
 * - Identity rule applies when atom on right matches atom on left
 *
 * In FOCUSED mode:
 * - If not focused: show "Focus on X" choices
 * - If focused: show rules that apply to the focused formula
 *
 * This gives the user full control over proof construction.
 */
export function getApplicableRules(seq: any, options: GetRulesOptions = {}): ApplicableRule[] {
  const { mode = 'unfocused', focusState } = options;

  // In focused mode with no current focus, show focus choices
  if (mode === 'focused' && (!focusState || !focusState.position)) {
    return getFocusChoices(seq);
  }

  // In focused mode with active focus, get rules for focused formula
  if (mode === 'focused' && focusState?.position) {
    return getFocusedRules(seq, focusState);
  }

  // Unfocused mode - direct rule matching
  return getUnfocusedRules(seq);
}

/**
 * Generate a focus rule string using bracket notation.
 * In focused linear logic literature, focus is shown as [A] brackets.
 *
 * Format: [conclusion, premise] where:
 * - Conclusion: unfocused (before focusing)
 * - Premise: focused (after focusing, formula in brackets)
 *
 * Example Focus_R:
 *        Γ ⊢ [A]        (premise - focused)
 *   ─────────────────── Focus_R
 *        Γ ⊢ A          (conclusion - unfocused)
 */
function generateFocusRuleString(
  seq: any,
  position: string,
  focusFormula: any
): string[] {
  const formulaLatex = focusFormula.toString({ style: 'latex' });

  if (position === 'R') {
    // Right focus: conclusion has A, premise has [A]
    return [
      `\\Gamma \\vdash ${simplifyLatex(formulaLatex)}`,        // conclusion (unfocused)
      `\\Gamma \\vdash [${simplifyLatex(formulaLatex)}]`,      // premise (focused)
    ];
  } else {
    // Left focus: conclusion has A, premise has [A]
    return [
      `\\Gamma, ${simplifyLatex(formulaLatex)}, \\Delta \\vdash C`,   // conclusion (unfocused)
      `\\Gamma, [${simplifyLatex(formulaLatex)}], \\Delta \\vdash C`, // premise (focused)
    ];
  }
}

/**
 * Get focus choices for a sequent (focused mode, not yet focused)
 */
function getFocusChoices(seq: any): ApplicableRule[] {
  const choices: ApplicableRule[] = [];

  // Can focus on right if there's a complex formula on right
  const succFormula = extractFormula(seq.succedent);
  if (succFormula && !isAtomicFormula(succFormula)) {
    const formulaLatex = succFormula.toString({ style: 'latex' });
    choices.push({
      name: `Focus_R`,
      category: 'Focus',
      ruleStrings: generateFocusRuleString(seq, 'R', succFormula),
      premises: [],
      position: 'R',
      principalFormula: succFormula.toString(),
      principalFormulaLatex: formulaLatex,
    });
  }

  // Can focus on left formulas (only non-atomic - can't decompose atoms)
  for (const id of Object.keys(seq.linear_ctx)) {
    const entry = seq.linear_ctx[id];
    if (!entry || !entry.val) continue;

    const formula = extractFormula(entry.val);
    if (!formula) continue;

    // Skip atomic formulas - can't focus on atoms (nothing to decompose)
    if (isAtomicFormula(formula)) continue;

    const formulaLatex = formula.toString({ style: 'latex' });
    choices.push({
      name: `Focus_L`,
      category: 'Focus',
      ruleStrings: generateFocusRuleString(seq, id, formula),
      premises: [],
      position: id,
      principalFormula: formula.toString(),
      principalFormulaLatex: formulaLatex,
    });
  }

  return choices;
}

/**
 * Get rules applicable to a focused formula
 */
function getFocusedRules(seq: any, focusState: { position: string | null; id: string | null }): ApplicableRule[] {
  const applicable: ApplicableRule[] = [];
  const ruleset = initBrowserRuleset();
  const position = focusState.position === 'R' ? 'R' : focusState.id;
  if (!position) return [];

  const formula = position === 'R'
    ? extractFormula(seq.succedent)
    : extractFormula(seq.linear_ctx[position]?.val);

  if (!formula) return [];

  const connective = getConnectiveName(formula);
  const isAtomic = isAtomicFormula(formula);

  // Get the principal formula for display
  const principal = getPrincipalFormula(seq, position);

  if (isAtomic) {
    // Try identity
    if (position === 'R') {
      // Positive identity: match right atom with left context
      for (const id of Object.keys(seq.linear_ctx)) {
        const ctxFormula = extractFormula(seq.linear_ctx[id]?.val);
        if (ctxFormula && isAtomicFormula(ctxFormula)) {
          const theta = mgu([[ctxFormula, formula]]);
          if (theta !== false) {
            applicable.push({
              name: 'Id+',
              category: 'RuleZer',
              ruleStrings: ['Identity (positive)'],
              premises: [],
              position: id,
              principalFormula: formula.toString(),
              principalFormulaLatex: formula.toString({ style: 'latex' }),
              splitContext: false,
            });
            break;
          }
        }
      }
    } else {
      // Negative identity: match left atom with right succedent
      const succFormula = extractFormula(seq.succedent);
      if (succFormula && isAtomicFormula(succFormula)) {
        const theta = mgu([[formula, succFormula]]);
        if (theta !== false) {
          applicable.push({
            name: 'Id-',
            category: 'RuleZer',
            ruleStrings: ['Identity (negative)'],
            premises: [],
            position,
            principalFormula: formula.toString(),
            principalFormulaLatex: formula.toString({ style: 'latex' }),
            splitContext: false,
          });
        }
      }
    }

    // Add blur option
    applicable.push({
      name: 'Blur',
      category: 'Focus',
      ruleStrings: ['Unfocus (blur)'],
      premises: [],
      position,
    });
  } else if (connective) {
    // Rule for this connective
    const side = position === 'R' ? 'R' : 'L';
    const ruleName = connective + '_' + side;
    const rule = ruleset.getRule(ruleName);

    if (rule && rule.length > 0) {
      const testPt = new PT({ conclusion: Sequent.copy(seq) });
      const result = Proofstate.apply(testPt, ruleName, position, rule);
      if (result?.success) {
        // Use focused rule strings with brackets in focused mode
        const focusSide = position === 'R' ? 'R' : 'L';
        applicable.push({
          name: ruleName,
          category: getRuleCategory(ruleName),
          ruleStrings: getFocusedRuleStrings(ruleName, focusSide as 'L' | 'R'),
          premises: testPt.premisses.map((p: any) => p.conclusion),
          position,
          principalFormula: principal?.ascii,
          principalFormulaLatex: principal?.latex,
          splitContext: isContextSplittingRule(ruleName),
        });
      }
    }

    // Check for alternative rules
    const ruleName2 = connective + '_' + side + '2';
    if (ruleset.rules[ruleName2]) {
      const rule2 = ruleset.getRule(ruleName2);
      if (rule2 && rule2.length > 0) {
        const testPt2 = new PT({ conclusion: Sequent.copy(seq) });
        const result2 = Proofstate.apply(testPt2, ruleName2, position, rule2);
        if (result2?.success) {
          // Use focused rule strings with brackets
          applicable.push({
            name: ruleName2,
            category: getRuleCategory(ruleName2),
            ruleStrings: getFocusedRuleStrings(ruleName2, focusSide as 'L' | 'R'),
            premises: testPt2.premisses.map((p: any) => p.conclusion),
            position,
            principalFormula: principal?.ascii,
            principalFormulaLatex: principal?.latex,
            splitContext: isContextSplittingRule(ruleName2),
          });
        }
      }
    }
  }

  return applicable;
}

/**
 * Get rules in unfocused mode (direct rule application)
 */
function getUnfocusedRules(seq: any): ApplicableRule[] {
  const ruleset = initBrowserRuleset();
  const applicable: ApplicableRule[] = [];

  // Helper to try applying a rule directly (unfocused)
  const tryRuleUnfocused = (ruleName: string, position: string): ApplicableRule | null => {
    const rule = ruleset.getRule(ruleName);
    if (!rule || rule.length === 0) return null;

    // Create a test PT
    const testPt = new PT({ conclusion: Sequent.copy(seq) });

    // Get the principal formula BEFORE applying the rule
    const principal = getPrincipalFormula(seq, position);

    // Try to apply the rule directly without focusing
    const result = Proofstate.apply(testPt, ruleName, position, rule);

    if (result && result.success) {
      const premises = testPt.premisses.map((p: any) => p.conclusion);
      return {
        name: ruleName,
        category: getRuleCategory(ruleName),
        ruleStrings: getRuleStrings(ruleName),
        premises,
        position,
        principalFormula: principal?.ascii,
        principalFormulaLatex: principal?.latex,
        splitContext: isContextSplittingRule(ruleName),
      };
    }
    return null;
  };

  // Check succedent (R position) - right rules
  const succFormula = extractFormula(seq.succedent);
  if (succFormula) {
    const connective = getConnectiveName(succFormula);
    if (connective && !isAtomicFormula(succFormula)) {
      // The rule name is ConnectiveName_R
      const ruleName = connective + '_R';
      const result = tryRuleUnfocused(ruleName, 'R');
      if (result) applicable.push(result);

      // Some connectives have multiple right rules (e.g., Plus_R, Plus_R2)
      const ruleName2 = connective + '_R2';
      if (ruleset.rules[ruleName2]) {
        const result2 = tryRuleUnfocused(ruleName2, 'R');
        if (result2) applicable.push(result2);
      }
    }
  }

  // Check linear context entries - left rules
  for (const id of Object.keys(seq.linear_ctx)) {
    const entry = seq.linear_ctx[id];
    if (!entry || !entry.val) continue;

    const formula = extractFormula(entry.val);
    if (!formula) continue;

    const connective = getConnectiveName(formula);
    if (connective && !isAtomicFormula(formula)) {
      // The rule name is ConnectiveName_L
      const ruleName = connective + '_L';
      const result = tryRuleUnfocused(ruleName, id);
      if (result) applicable.push(result);

      // Some connectives have multiple left rules
      const ruleName2 = connective + '_L2';
      if (ruleset.rules[ruleName2]) {
        const result2 = tryRuleUnfocused(ruleName2, id);
        if (result2) applicable.push(result2);
      }
    }
  }

  // Check for Identity rule on atomic formulas
  const succAtom = extractFormula(seq.succedent);
  if (succAtom && isAtomicFormula(succAtom)) {
    for (const id of Object.keys(seq.linear_ctx)) {
      const entry = seq.linear_ctx[id];
      if (!entry || !entry.val) continue;

      const ctxFormula = extractFormula(entry.val);
      if (!ctxFormula || !isAtomicFormula(ctxFormula)) continue;

      // Try to unify - if they match, Identity can apply
      const theta = mgu([[ctxFormula, succAtom]]);
      if (theta !== false) {
        applicable.push({
          name: 'Id',
          category: 'RuleZer',
          ruleStrings: ['-- : ?X |- -- : ?X'],
          premises: [],
          position: id,
          principalFormula: succAtom.toString(),
          principalFormulaLatex: succAtom.toString({ style: 'latex' }),
          splitContext: false,
        });
        break;
      }
    }
  }

  // Sort by category
  const categoryOrder = ['RuleZer', 'RuleCut', 'RuleU', 'RuleBin'];
  applicable.sort((a, b) => {
    const aIdx = categoryOrder.indexOf(a.category);
    const bIdx = categoryOrder.indexOf(b.category);
    if (aIdx === -1 && bIdx === -1) return a.name.localeCompare(b.name);
    if (aIdx === -1) return 1;
    if (bIdx === -1) return -1;
    return aIdx - bIdx;
  });

  return applicable;
}


/**
 * Apply a rule to a proof tree node.
 * Returns a new PT with the rule applied directly.
 *
 * In focused mode, focus state is propagated to premises based on FOCUS_PATTERNS.
 * In unfocused mode, no focus state is set.
 */
export function applyRule(
  pt: ProofTreeNode,
  ruleName: string,
  position: string
): ProofTreeNode | null {
  const ruleset = initBrowserRuleset();

  // Validate position exists for left rules
  if (position !== 'R') {
    if (!pt.conclusion.linear_ctx[position]) {
      console.error(`applyRule: position '${position}' not found in linear_ctx`);
      console.error('Available ids:', Object.keys(pt.conclusion.linear_ctx || {}));
      return null;
    }
  }

  // Handle Identity rule specially
  if (ruleName === 'Id') {
    const ptCopy = cloneProofTree(pt);
    const seq = ptCopy.conclusion;

    // Get the formula from succedent and the matching context entry
    const succFormula = extractFormula(seq.succedent);
    const ctxEntry = seq.linear_ctx[position];

    if (!ctxEntry || !succFormula) return null;

    const ctxFormula = extractFormula(ctxEntry.val);
    if (!ctxFormula) return null;

    // Verify they actually match
    const theta = mgu([[ctxFormula, succFormula]]);
    if (theta === false) return null;

    // Apply substitution if needed
    if (theta && theta.length > 0) {
      seq.substitute(theta);
    }

    // Mark as proven - Identity has no premises
    ptCopy.type = 'Id';
    ptCopy.premisses = [];
    ptCopy.proven = true;

    return ptCopy;
  }

  // Standard rule application
  const rule = ruleset.getRule(ruleName);
  if (!rule || rule.length === 0) return null;

  const ptCopy = cloneProofTree(pt);

  // Apply the rule
  const result = Proofstate.apply(ptCopy, ruleName, position, rule);

  if (result && result.success) {
    // Post-process premises: remove structural variables and distribute context
    // This mirrors what Proofstate.auto does after calling Proofstate.apply
    const isSplitting = isContextSplittingRule(ruleName);
    const delta = ptCopy.delta_in || {};

    for (const premise of ptCopy.premisses) {
      // For non-splitting rules, add all remaining context to each premise
      // (like With_R which copies context to all premises)
      if (!isSplitting) {
        Sequent.add_to_antecedent_bulk(premise.conclusion, delta);
      }
      // Remove structural metavariables (?X, ?Y become empty when no context)
      Sequent.remove_structural_variables(premise.conclusion);
    }

    // Propagate focus state to premises if applicable
    propagateFocusToPremises(ptCopy, ruleName, pt.conclusion);
    return ptCopy;
  }

  return null;
}

/**
 * Propagate focus state to premises after rule application.
 * Uses FOCUS_PATTERNS to determine where focus goes in each premise.
 */
function propagateFocusToPremises(pt: ProofTreeNode, ruleName: string, parentConclusion: any): void {
  const pattern = FOCUS_PATTERNS[ruleName];

  // Import ProofSearchState
  const { ProofSearchState } = require('../../../lib/prover.js');

  if (!pattern) {
    // No focus pattern - blur focus on all premises (async rule)
    for (const premise of pt.premisses) {
      (premise as any).proverState = null;
    }
    return;
  }

  // Apply focus to each premise based on pattern
  for (let i = 0; i < pt.premisses.length && i < pattern.premiseFocus.length; i++) {
    const premise = pt.premisses[i];
    const focusPattern = pattern.premiseFocus[i];

    if (!focusPattern) {
      // No focus for this premise
      (premise as any).proverState = null;
      continue;
    }

    const state = new ProofSearchState();

    if (focusPattern.position === 'R') {
      // Focus on succedent
      state.focus('R', null);
    } else {
      // Focus on left - need to find the id of the focused formula
      // The focused formula is a new entry added by the rule (not from parent)
      // Skip structural metavars (like ?X, ?Y) which are context placeholders
      const parentCtxIds = new Set(Object.keys(parentConclusion.linear_ctx || {}));
      const premiseCtx = premise.conclusion.linear_ctx || {};
      const premiseCtxIds = Object.keys(premiseCtx);

      // Find new entries that are NOT structural metavars
      const newIds = premiseCtxIds.filter(id => {
        if (parentCtxIds.has(id)) return false;
        // Check if it's a structural metavar
        const entry = premiseCtx[id];
        if (isStructuralMetavar(entry)) return false;
        return true;
      });

      if (newIds.length > 0) {
        // Use the first new non-metavar id as the focused formula
        state.focus('L', newIds[0]);
      } else {
        // Fallback: no new formula found, blur
        (premise as any).proverState = null;
        continue;
      }
    }

    (premise as any).proverState = state;
  }
}

/**
 * Context entry for display in split dialog
 */
export interface ContextEntry {
  id: string;
  formula: string;
  formulaLatex: string;
}

/**
 * Get the linear context entries from a sequent for display.
 *
 * @param seq - The sequent
 * @param excludeId - Optional id to exclude (e.g., the principal formula being decomposed)
 */
export function getContextEntries(seq: any, excludeId?: string): ContextEntry[] {
  const entries: ContextEntry[] = [];

  if (!seq || !seq.linear_ctx) return entries;

  for (const id of Object.keys(seq.linear_ctx)) {
    // Skip the excluded id (principal formula)
    if (excludeId && id === excludeId) continue;

    const entry = seq.linear_ctx[id];
    if (!entry || !entry.val) continue;

    const formula = extractFormula(entry.val);
    if (!formula) continue;

    entries.push({
      id,
      formula: entry.val.toString(),
      formulaLatex: entry.val.toString({ style: 'latex' }),
    });
  }

  return entries;
}

/**
 * Check if a context entry is a structural metavariable (like ?X, ?Y).
 * These are placeholders in rules that get substituted with actual formulas.
 */
function isStructuralMetavar(entry: any): boolean {
  if (!entry || !entry.val || !entry.val.id) return false;
  const rule = Calc.db.rules[entry.val.id];
  if (!rule) return false;
  return rule.ruleName === 'Structure_Freevar' || rule.ruleName === 'Structure_Neutral';
}

/**
 * Preview what the subgoals would look like with a given context split.
 *
 * Context-splitting rules (like Tensor_R, Loli_L) have structural metavariables
 * ?X (Γ) and ?Y (Δ) that represent portions of the context. The user is building
 * a SUBSTITUTION: Γ → selected formulas for premise 1, Δ → selected for premise 2.
 *
 * After rule application:
 * - Premises have structural metavar entries (?X, ?Y) as placeholders
 * - We remove these placeholders
 * - We add the user's selected formulas (the substitution)
 * - We keep any rule-specific additions (like B in Loli_L premise 2)
 *
 * @param seq - The current sequent
 * @param ruleName - The rule name (e.g., 'Tensor_R')
 * @param position - Position identifier (principal formula location)
 * @param split - Object with premise1 and premise2 arrays of context entry ids
 * @returns Array of premise sequents with the substitution applied, or null if invalid
 */
export function previewSplitSubgoals(
  seq: any,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] }
): any[] | null {
  try {
    const ruleset = initBrowserRuleset();
    const rule = ruleset.getRule(ruleName);
    if (!rule || rule.length === 0) return null;

    // Create a test PT
    const testPt = new PT({ conclusion: Sequent.copy(seq) });

    // Verify the position exists in the sequent (for left rules)
    if (position !== 'R' && !testPt.conclusion.linear_ctx[position]) {
      console.warn(`previewSplitSubgoals: position ${position} not found in sequent`);
      return null;
    }

    // Apply the rule to get the basic structure
    const result = Proofstate.apply(testPt, ruleName, position, rule);
    if (!result || !result.success) return null;

    // If not a binary rule, return as-is
    if (testPt.premisses.length !== 2) {
      return testPt.premisses.map((p: any) => p.conclusion);
    }

    const premise1 = testPt.premisses[0];
    const premise2 = testPt.premisses[1];
    const parentCtx = seq.linear_ctx;

    // Create new sequent copies
    const seq1 = Sequent.copy(premise1.conclusion);
    const seq2 = Sequent.copy(premise2.conclusion);

    // Step 1: Identify entries that came from the rule (not structural metavars, not from parent)
    // These are rule-specific additions like B in Loli_L premise 2
    const ruleAdditions1: Record<string, any> = {};
    const ruleAdditions2: Record<string, any> = {};

    for (const id of Object.keys(premise1.conclusion.linear_ctx || {})) {
      const entry = premise1.conclusion.linear_ctx[id];
      // Keep if: not a structural metavar AND not from parent context
      if (!isStructuralMetavar(entry) && !parentCtx[id]) {
        ruleAdditions1[id] = { num: entry.num, val: entry.val.copy() };
      }
    }

    for (const id of Object.keys(premise2.conclusion.linear_ctx || {})) {
      const entry = premise2.conclusion.linear_ctx[id];
      if (!isStructuralMetavar(entry) && !parentCtx[id]) {
        ruleAdditions2[id] = { num: entry.num, val: entry.val.copy() };
      }
    }

    // Step 2: Build the substitution - user's selected formulas for each premise
    const userCtx1: Record<string, any> = {};
    const userCtx2: Record<string, any> = {};

    for (const id of split.premise1) {
      if (parentCtx[id]) {
        userCtx1[id] = { num: parentCtx[id].num, val: parentCtx[id].val.copy() };
      }
    }

    for (const id of split.premise2) {
      if (parentCtx[id]) {
        userCtx2[id] = { num: parentCtx[id].num, val: parentCtx[id].val.copy() };
      }
    }

    // Step 3: Combine - user's selection + rule additions (NO structural metavars)
    seq1.linear_ctx = { ...userCtx1, ...ruleAdditions1 };
    seq2.linear_ctx = { ...userCtx2, ...ruleAdditions2 };

    // Explicitly remove any remaining structural variables for consistency
    Sequent.remove_structural_variables(seq1);
    Sequent.remove_structural_variables(seq2);

    return [seq1, seq2];
  } catch (e) {
    console.error('previewSplitSubgoals error:', e);
    return null;
  }
}

/**
 * Apply a context-splitting rule with a custom resource distribution.
 *
 * Context-splitting rules have structural metavariables ?X (Γ) and ?Y (Δ).
 * The user builds a SUBSTITUTION: Γ → formulas for premise 1, Δ → formulas for premise 2.
 *
 * We apply the rule, then replace the structural metavar placeholders with
 * the user's actual selections, keeping any rule-specific additions.
 *
 * @param pt - The proof tree node to apply the rule to
 * @param ruleName - The rule name (e.g., 'Tensor_R')
 * @param position - Position identifier (e.g., 'R' for right, or context id for left)
 * @param split - Object with premise1 and premise2 arrays of context entry ids
 */
export function applyRuleWithSplit(
  pt: ProofTreeNode,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] }
): ProofTreeNode | null {
  const ruleset = initBrowserRuleset();
  const rule = ruleset.getRule(ruleName);
  if (!rule || rule.length === 0) return null;

  // Validate position exists for left rules
  if (position !== 'R') {
    if (!pt.conclusion.linear_ctx[position]) {
      console.error(`applyRuleWithSplit: position '${position}' not found in linear_ctx`);
      console.error('Available ids:', Object.keys(pt.conclusion.linear_ctx || {}));
      return null;
    }
  }

  const ptCopy = cloneProofTree(pt);

  // Apply the rule to get the basic structure
  const result = Proofstate.apply(ptCopy, ruleName, position, rule);
  if (!result || !result.success) return null;

  if (ptCopy.premisses.length !== 2) {
    // Not a binary splitting rule, just return normal result
    return ptCopy;
  }

  const premise1 = ptCopy.premisses[0];
  const premise2 = ptCopy.premisses[1];
  const parentCtx = ptCopy.conclusion.linear_ctx;

  // Step 1: Identify rule-specific additions (not structural metavars, not from parent)
  // These are entries like B in Loli_L premise 2
  const ruleAdditions1: Record<string, any> = {};
  const ruleAdditions2: Record<string, any> = {};

  for (const id of Object.keys(premise1.conclusion.linear_ctx || {})) {
    const entry = premise1.conclusion.linear_ctx[id];
    if (!isStructuralMetavar(entry) && !parentCtx[id]) {
      ruleAdditions1[id] = { num: entry.num, val: entry.val.copy() };
    }
  }

  for (const id of Object.keys(premise2.conclusion.linear_ctx || {})) {
    const entry = premise2.conclusion.linear_ctx[id];
    if (!isStructuralMetavar(entry) && !parentCtx[id]) {
      ruleAdditions2[id] = { num: entry.num, val: entry.val.copy() };
    }
  }

  // Step 2: Build user's substitution
  const userCtx1: Record<string, any> = {};
  const userCtx2: Record<string, any> = {};

  for (const id of split.premise1) {
    if (parentCtx[id]) {
      userCtx1[id] = { num: parentCtx[id].num, val: parentCtx[id].val.copy() };
    }
  }

  for (const id of split.premise2) {
    if (parentCtx[id]) {
      userCtx2[id] = { num: parentCtx[id].num, val: parentCtx[id].val.copy() };
    }
  }

  // Step 3: Combine - user's selection + rule additions (NO structural metavars)
  premise1.conclusion.linear_ctx = { ...userCtx1, ...ruleAdditions1 };
  premise2.conclusion.linear_ctx = { ...userCtx2, ...ruleAdditions2 };

  // Explicitly remove any remaining structural variables for consistency
  // (The manual construction above should already exclude them, but this is defensive)
  Sequent.remove_structural_variables(premise1.conclusion);
  Sequent.remove_structural_variables(premise2.conclusion);

  // Propagate focus state to premises if applicable
  propagateFocusToPremises(ptCopy, ruleName, pt.conclusion);

  return ptCopy;
}

/**
 * Proof search options
 */
export interface AutoProveOptions {
  /** If true, collapse Focus_L/Focus_R steps in the result */
  hideFocusSteps?: boolean;
}

/**
 * Run automatic proof search on a node
 */
export function autoProve(
  pt: ProofTreeNode,
  options: AutoProveOptions = {}
): { success: boolean; pt: ProofTreeNode } {
  const ruleset = initBrowserRuleset();
  const ptCopy = cloneProofTree(pt);

  const atoms = Sequent.getAtoms(ptCopy.conclusion, { rules: Calc.db.rules });

  const result = Proofstate.auto(ptCopy, {
    positive: atoms,
    negative: [],
    debug: false,
    mode: 'proof',
    rules: ruleset.rules,
    bwd: ruleset.bwd,
    getRule: ruleset.getRule,
    calc: Calc.calc,
  });

  let finalPt = ptCopy;

  // Optionally collapse focus steps
  if (options.hideFocusSteps && result?.success) {
    finalPt = collapseFocusSteps(ptCopy);
  }

  return {
    success: result?.success || false,
    pt: finalPt,
  };
}

/**
 * Collapse Focus_L and Focus_R steps in a proof tree.
 * These are administrative steps from focused proof search, not logical rules.
 *
 * Example: Focus_L -> Loli_L -> [premises] becomes Loli_L -> [premises]
 */
export function collapseFocusSteps(pt: ProofTreeNode): ProofTreeNode {
  // If this is a Focus step, skip it and return the collapsed child
  if (pt.type === 'Focus_L' || pt.type === 'Focus_R') {
    if (pt.premisses.length === 1) {
      // Recursively collapse the child
      const child = collapseFocusSteps(pt.premisses[0]);
      // Preserve the original conclusion (unfocused sequent)
      const result = new PT({
        conclusion: pt.conclusion,
        premisses: child.premisses.map(collapseFocusSteps),
        type: child.type,
      });
      result.proven = child.proven;
      result.delta_in = child.delta_in;
      result.delta_out = child.delta_out;
      return result;
    }
  }

  // Not a focus step - just recursively process children
  if (pt.premisses.length === 0) {
    return pt;
  }

  const collapsedPremises = pt.premisses.map(collapseFocusSteps);

  const result = new PT({
    conclusion: pt.conclusion,
    premisses: collapsedPremises,
    type: pt.type,
  });
  result.proven = pt.proven;
  result.delta_in = pt.delta_in;
  result.delta_out = pt.delta_out;

  return result;
}

/**
 * Convert metavariables to paper-style notation for cleaner display.
 * Matches the simplification used in SequentRule.tsx for abstract rules.
 */
function simplifyLatex(latex: string): string {
  return latex
    // Context metavariables
    .replace(/\?\s*X/g, '\\Gamma')
    .replace(/\?\s*Y/g, '\\Delta')
    .replace(/\?\s*Z/g, '\\Sigma')
    .replace(/\?\s*W/g, '\\Pi')
    // Formula metavariables - remove F? prefix
    .replace(/F\?\s*([A-Z])/g, '$1')
    // Structure metavariables
    .replace(/S\?\s*([A-Z])/g, '$1')
    // Term placeholder
    .replace(/\\cdot\s*:/g, '')
    .replace(/--\s*:/g, '')
    // Clean up extra spaces
    .replace(/\s+/g, ' ')
    .replace(/\(\s+/g, '(')
    .replace(/\s+\)/g, ')')
    .trim();
}

/**
 * Focus state information for display
 */
export interface FocusInfo {
  position: 'L' | 'R' | null;
  id: string | null;
}

/**
 * Convert a sequent to LaTeX string with optional focus brackets.
 * When focusInfo is provided, the focused formula is wrapped in [brackets].
 *
 * In focused mode, after Focus_L/Focus_R:
 * - Left focus: the focused formula (identified by focusInfo.id) is bracketed
 * - Right focus: the succedent is bracketed
 *
 * All context formulas are preserved in the display.
 */
export function sequentToLatex(seq: any, simplify = true, focusInfo?: FocusInfo): string {
  try {
    const raw = seq.toString({ style: 'latex' });
    let result = simplify ? simplifyLatex(raw) : raw;

    // If we have focus info, wrap the focused formula in brackets
    if (focusInfo?.position) {
      if (focusInfo.position === 'L' && focusInfo.id) {
        // Left focus: wrap the specific focused formula (by id)
        const focusedEntry = seq.linear_ctx?.[focusInfo.id];
        if (focusedEntry?.val) {
          const focusedLatex = simplify
            ? simplifyLatex(focusedEntry.val.toString({ style: 'latex' }))
            : focusedEntry.val.toString({ style: 'latex' });
          // Wrap the focused formula in brackets
          const bracketedLatex = `[${focusedLatex}]`;
          // Replace the formula with its bracketed version
          result = result.replace(focusedLatex, bracketedLatex);
        }
      } else if (focusInfo.position === 'R') {
        // Right focus: wrap the succedent
        if (seq.succedent) {
          const succFormula = extractFormula(seq.succedent);
          if (succFormula) {
            const succLatex = simplify
              ? simplifyLatex(succFormula.toString({ style: 'latex' }))
              : succFormula.toString({ style: 'latex' });
            const bracketedLatex = `[${succLatex}]`;
            // Replace succedent in result
            result = result.replace(succLatex, bracketedLatex);
          }
        }
      }
    }

    return result;
  } catch {
    return seq.toString();
  }
}

/**
 * Convert a sequent to ASCII string
 */
export function sequentToAscii(seq: any): string {
  try {
    return seq.toString({ style: 'ascii' });
  } catch {
    return seq.toString();
  }
}

/**
 * Convert proof tree to structured proof format (Lamport-style)
 */
export interface StructuredStep {
  level: number;
  step: number;
  sequent: any;
  sequentLatex: string;
  ruleName: string;
  isProven: boolean;
  isLeaf: boolean;
  children: StructuredStep[];
  path: number[];
}

export function ptToStructuredProof(pt: ProofTreeNode, level = 1, step = 1, path: number[] = []): StructuredStep {
  const children: StructuredStep[] = pt.premisses.map((p: ProofTreeNode, i: number) =>
    ptToStructuredProof(p, level + 1, i + 1, [...path, i])
  );

  const isLeaf = pt.premisses.length === 0;
  const isProven = pt.type !== '???' && (isLeaf || children.every(c => c.isProven));

  return {
    level,
    step,
    sequent: pt.conclusion,
    sequentLatex: sequentToLatex(pt.conclusion),
    ruleName: pt.type,
    isProven,
    isLeaf,
    children,
    path,
  };
}

/**
 * Apply a focus action in focused mode.
 * Creates a Focus_L or Focus_R node with the focus state set.
 *
 * Unlike Proofstate.focus (which strips context for auto-prover resource tracking),
 * this preserves all context formulas for UI display. The focus is tracked via
 * ProofSearchState on the premise node.
 */
export function applyFocusAction(pt: ProofTreeNode, position: string): ProofTreeNode | null {
  const ptCopy = cloneProofTree(pt);

  // Import ProofSearchState dynamically
  const { ProofSearchState } = require('../../../lib/prover.js');

  // Create the premise sequent - PRESERVE all context formulas
  const premiseSeq = Sequent.copy(ptCopy.conclusion);

  // Set up prover state to track focus
  const state = new ProofSearchState();
  if (position === 'R') {
    state.focus('R', null);
  } else {
    state.focus('L', position);
  }

  // Create the premise node with ALL context preserved
  const premiseNode = new PT({
    conclusion: premiseSeq,
    proverState: state
  });

  // Set up the parent node
  ptCopy.premisses = [premiseNode];
  ptCopy.type = position === 'R' ? 'Focus_R' : 'Focus_L';
  // Store delta_in for resource tracking (but don't strip from sequent)
  ptCopy.delta_in = {};

  return ptCopy;
}

/**
 * Apply a blur action in focused mode.
 * Clears the focus state and continues with unfocused search.
 */
export function applyBlurAction(pt: ProofTreeNode): ProofTreeNode | null {
  // For blur, we just need to clear the focus state
  // The proof tree structure stays the same, but focus is removed
  const ptCopy = cloneProofTree(pt);

  // Clear prover state
  if (ptCopy.proverState) {
    ptCopy.proverState.blur();
  }

  return ptCopy;
}

// ============================================================================
// Proof Tree Serialization
// ============================================================================

/**
 * Serialized focus state
 */
export interface SerializedFocusState {
  phase: 'inversion' | 'focus';
  position: 'L' | 'R' | null;
  id: string | null;
}

/**
 * Serialized context entry (formula in antecedent)
 */
export interface SerializedContextEntry {
  id: string;
  formula: string;        // ASCII representation
  formulaLatex: string;   // LaTeX representation
}

/**
 * Serialized sequent
 */
export interface SerializedSequent {
  ascii: string;          // Full sequent as ASCII string
  latex: string;          // Full sequent as LaTeX string
  persistent: SerializedContextEntry[];  // Persistent context (!A formulas)
  linear: SerializedContextEntry[];      // Linear context
  succedent: string;      // Right-hand side formula (ASCII)
  succedentLatex: string; // Right-hand side formula (LaTeX)
}

/**
 * Serialized proof tree node
 */
export interface SerializedProofNode {
  // Rule application info
  rule: string;           // Rule name (e.g., "Loli_L", "Focus_R", "???")
  position: string | null; // Position where rule was applied ('R' or context id)

  // Sequent info
  conclusion: SerializedSequent;

  // Focus state (if in focused mode)
  focus?: SerializedFocusState;

  // Resource tracking
  resourcesConsumed?: string[];   // IDs of formulas consumed by this rule
  resourcesRemaining?: string[];  // IDs of formulas passed to premises

  // Status
  proven: boolean;

  // Child nodes (premises)
  premises: SerializedProofNode[];
}

/**
 * Complete serialized proof
 */
export interface SerializedProof {
  // Metadata
  version: string;
  timestamp: string;

  // Proof info
  goal: string;           // Original goal as ASCII string
  goalLatex: string;      // Original goal as LaTeX string
  complete: boolean;      // Whether proof is complete

  // Proof mode
  mode: 'unfocused' | 'focused';

  // Statistics
  stats: {
    totalNodes: number;
    provenNodes: number;
    unprovenNodes: number;
    maxDepth: number;
  };

  // The proof tree
  tree: SerializedProofNode;
}

/**
 * Serialize a sequent to JSON-friendly format.
 * If focusInfo is provided, the focused formula is wrapped in [brackets].
 */
function serializeSequent(seq: any, focusInfo?: FocusInfo): SerializedSequent {
  const persistent: SerializedContextEntry[] = [];
  const linear: SerializedContextEntry[] = [];

  // Serialize persistent context
  if (seq.persistent_ctx) {
    for (const id of Object.keys(seq.persistent_ctx)) {
      const entry = seq.persistent_ctx[id];
      if (entry) {
        persistent.push({
          id,
          formula: entry.toString?.() || String(entry),
          formulaLatex: entry.toString?.({ style: 'latex' }) || String(entry),
        });
      }
    }
  }

  // Serialize linear context (with focus brackets if applicable)
  if (seq.linear_ctx) {
    for (const id of Object.keys(seq.linear_ctx)) {
      const entry = seq.linear_ctx[id];
      if (entry?.val) {
        const isFocused = focusInfo?.position === 'L' && focusInfo?.id === id;
        const formulaStr = entry.val.toString?.() || String(entry.val);
        const formulaLatexStr = entry.val.toString?.({ style: 'latex' }) || String(entry.val);
        linear.push({
          id,
          formula: isFocused ? `[${formulaStr}]` : formulaStr,
          formulaLatex: isFocused ? `[${formulaLatexStr}]` : formulaLatexStr,
        });
      }
    }
  }

  // Serialize succedent (with focus brackets if applicable)
  let succedent = '';
  let succedentLatex = '';
  if (seq.succedent) {
    const formula = extractFormula(seq.succedent);
    if (formula) {
      const isFocused = focusInfo?.position === 'R';
      const formulaStr = formula.toString?.() || String(formula);
      const formulaLatexStr = formula.toString?.({ style: 'latex' }) || String(formula);
      succedent = isFocused ? `[${formulaStr}]` : formulaStr;
      succedentLatex = isFocused ? `[${formulaLatexStr}]` : formulaLatexStr;
    }
  }

  // Build full ascii/latex with focus brackets
  let ascii = seq.toString?.() || String(seq);
  let latex = seq.toString?.({ style: 'latex' }) || String(seq);

  // If focused, update the full sequent string to show brackets
  if (focusInfo?.position === 'L' && focusInfo?.id) {
    const focusedEntry = seq.linear_ctx?.[focusInfo.id];
    if (focusedEntry?.val) {
      const focusedAscii = focusedEntry.val.toString?.() || String(focusedEntry.val);
      const focusedLatex = focusedEntry.val.toString?.({ style: 'latex' }) || String(focusedEntry.val);
      ascii = ascii.replace(focusedAscii, `[${focusedAscii}]`);
      latex = latex.replace(focusedLatex, `[${focusedLatex}]`);
    }
  } else if (focusInfo?.position === 'R' && seq.succedent) {
    const formula = extractFormula(seq.succedent);
    if (formula) {
      const succAscii = formula.toString?.() || String(formula);
      const succLatex = formula.toString?.({ style: 'latex' }) || String(formula);
      // Replace in the part after |-
      ascii = ascii.replace(new RegExp(`\\|-(\\s*)${escapeRegExp(succAscii)}`), `|-$1[${succAscii}]`);
      latex = latex.replace(new RegExp(`\\\\vdash(\\s*)${escapeRegExp(succLatex)}`), `\\vdash$1[${succLatex}]`);
    }
  }

  return {
    ascii,
    latex,
    persistent,
    linear,
    succedent,
    succedentLatex,
  };
}

/**
 * Escape special regex characters in a string
 */
function escapeRegExp(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/**
 * Serialize focus state
 */
function serializeFocusState(proverState: any): SerializedFocusState | undefined {
  if (!proverState) return undefined;

  return {
    phase: proverState.phase || 'inversion',
    position: proverState.focusPosition || null,
    id: proverState.focusId || null,
  };
}

/**
 * Calculate the depth of a proof tree
 */
function calculateDepth(pt: ProofTreeNode): number {
  if (pt.premisses.length === 0) return 1;
  return 1 + Math.max(...pt.premisses.map(p => calculateDepth(p)));
}

/**
 * Serialize a proof tree node recursively
 */
function serializeProofNode(pt: ProofTreeNode, position: string | null = null): SerializedProofNode {
  // Determine position from the node's context if not provided
  // For leaf nodes (???), position is where the next rule would be applied
  let nodePosition = position;

  // Serialize consumed resources (delta_in)
  const resourcesConsumed: string[] = [];
  if (pt.delta_in) {
    for (const id of Object.keys(pt.delta_in)) {
      resourcesConsumed.push(id);
    }
  }

  // Serialize remaining resources (delta_out)
  const resourcesRemaining: string[] = [];
  if (pt.delta_out) {
    for (const id of Object.keys(pt.delta_out)) {
      resourcesRemaining.push(id);
    }
  }

  const isLeaf = pt.premisses.length === 0;
  const isProven = pt.type !== '???' && (isLeaf || pt.proven);

  // Get focus info for this node
  const proverState = (pt as any).proverState;
  const focusInfo: FocusInfo | undefined = proverState?.focusPosition
    ? { position: proverState.focusPosition as 'L' | 'R', id: proverState.focusId }
    : undefined;

  return {
    rule: pt.type,
    position: nodePosition,
    conclusion: serializeSequent(pt.conclusion, focusInfo),
    focus: serializeFocusState(proverState),
    resourcesConsumed: resourcesConsumed.length > 0 ? resourcesConsumed : undefined,
    resourcesRemaining: resourcesRemaining.length > 0 ? resourcesRemaining : undefined,
    proven: isProven,
    premises: pt.premisses.map((p, i) => serializeProofNode(p, null)),
  };
}

/**
 * Serialize a complete proof tree to JSON format.
 *
 * The serialization captures:
 * - The goal sequent
 * - The proof tree structure with all rule applications
 * - Focus states for focused proof mode
 * - Resource tracking (consumed/remaining formulas)
 * - Proof statistics
 *
 * @param pt - The proof tree to serialize
 * @param mode - The proof mode ('unfocused' or 'focused')
 * @returns A JSON-serializable proof object
 */
export function serializeProofTree(
  pt: ProofTreeNode,
  mode: 'unfocused' | 'focused' = 'unfocused'
): SerializedProof {
  const counts = countNodes(pt);
  const depth = calculateDepth(pt);
  const complete = isProofComplete(pt);

  // Get the root goal
  let goal = '';
  let goalLatex = '';
  try {
    goal = pt.conclusion.toString?.() || String(pt.conclusion);
    goalLatex = pt.conclusion.toString?.({ style: 'latex' }) || String(pt.conclusion);
  } catch {
    goal = String(pt.conclusion);
    goalLatex = goal;
  }

  return {
    version: '1.0',
    timestamp: new Date().toISOString(),
    goal,
    goalLatex,
    complete,
    mode,
    stats: {
      totalNodes: counts.proven + counts.unproven,
      provenNodes: counts.proven,
      unprovenNodes: counts.unproven,
      maxDepth: depth,
    },
    tree: serializeProofNode(pt),
  };
}

/**
 * Convert a serialized proof to a pretty-printed JSON string
 */
export function proofToJsonString(proof: SerializedProof, indent = 2): string {
  return JSON.stringify(proof, null, indent);
}
