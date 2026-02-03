/**
 * Browser-compatible proof logic for the interactive prover (v2).
 * Uses the v2 focused prover API.
 */

// v2 API
import {
  parseSequent as v2ParseSequent,
  parseFormula as v2ParseFormula,
  renderFormula,
  renderSequent,
  getCalculus,
  getBrowserModule,
  getSeqModule,
  autoProveV2,
} from './calcV2';

// Re-export types
export type Formula = {
  tag: string;
  children: (Formula | string)[];
};

export type Sequent = {
  linear: Formula[];
  cartesian: Formula[];
  succedent: Formula;
};

export type V2Sequent = Sequent;

export type V2ProofNode = {
  conclusion: V2Sequent;
  premisses: V2ProofNode[];
  rule: string | null;
  proven: boolean;
};

// =============================================================================
// Types
// =============================================================================

export interface ApplicableRule {
  name: string;
  category: string;
  ruleStrings: string[];
  premises: V2Sequent[];
  position: string;  // 'R' or index for L
  principalFormula?: string;
  principalFormulaLatex?: string;
  splitContext?: boolean;
}

export interface ProofTreeNode {
  conclusion: V2Sequent;
  premisses: ProofTreeNode[];
  type: string;  // Rule name or '???'
  proven: boolean;
  delta_in: Record<string, any>;
  delta_out: Record<string, any>;
}

export interface ContextEntry {
  id: string;
  formula: string;
  formulaLatex: string;
}

export interface GetRulesOptions {
  mode?: 'unfocused' | 'focused';
  focusState?: { position: string | null; id: string | null };
}

export interface AutoProveOptions {
  hideFocusSteps?: boolean;
}

export interface FocusInfo {
  position: 'L' | 'R' | null;
  id: string | null;
}

// =============================================================================
// Initialization
// =============================================================================

let initialized = false;

export function initBrowserRuleset(): void {
  // v2 API auto-initializes on first use
  getCalculus();
  initialized = true;
}

// =============================================================================
// Parsing
// =============================================================================

/**
 * Parse a sequent string into a v2 Sequent object
 */
export function parseSequent(input: string): V2Sequent {
  return v2ParseSequent(input) as V2Sequent;
}

/**
 * Parse a formula string
 */
export function parseFormula(input: string): Formula {
  return v2ParseFormula(input);
}

// =============================================================================
// Proof Tree Operations
// =============================================================================

/**
 * Create a new proof tree from a sequent
 */
export function createProofTree(sequent: V2Sequent): ProofTreeNode {
  return {
    conclusion: sequent,
    premisses: [],
    type: '???',
    proven: false,
    delta_in: {},
    delta_out: {},
  };
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
 */
export function getNodeAtPath(pt: ProofTreeNode, path: number[]): ProofTreeNode | null {
  if (path.length === 0) return pt;
  const [head, ...tail] = path;
  if (head >= pt.premisses.length) return null;
  return getNodeAtPath(pt.premisses[head], tail);
}

/**
 * Create a new tree with a node replaced at a specific path
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

  return {
    ...root,
    premisses: newPremisses,
  };
}

/**
 * Deep clone a proof tree
 */
export function cloneProofTree(pt: ProofTreeNode): ProofTreeNode {
  const Seq = getSeqModule();
  return {
    conclusion: Seq.copy(pt.conclusion),
    premisses: pt.premisses.map((p: ProofTreeNode) => cloneProofTree(p)),
    type: pt.type,
    proven: pt.proven,
    delta_in: { ...pt.delta_in },
    delta_out: { ...pt.delta_out },
  };
}

// =============================================================================
// Formula Helpers
// =============================================================================

/**
 * Get the connective name from a formula node
 */
function getConnectiveName(formula: Formula | null): string | null {
  if (!formula?.tag) return null;
  if (formula.tag === 'atom' || formula.tag === 'freevar') return null;
  return formula.tag;
}

/**
 * Check if a formula is atomic
 */
function isAtomicFormula(formula: Formula | null): boolean {
  if (!formula?.tag) return true;
  return formula.tag === 'atom' || formula.tag === 'freevar';
}

/**
 * Check if a rule splits the context
 */
function isContextSplittingRule(ruleName: string): boolean {
  const splittingRules = ['tensor_r', 'loli_l', 'Tensor_R', 'Loli_L'];
  return splittingRules.includes(ruleName);
}

/**
 * Get rule category
 */
function getRuleCategory(ruleName: string): string {
  const lower = ruleName.toLowerCase();
  if (lower === 'id' || lower.startsWith('id_')) return 'Identity';
  if (lower.includes('tensor') || lower.includes('loli') || lower.includes('one')) return 'Multiplicatives';
  if (lower.includes('with') || lower.includes('plus')) return 'Additives';
  if (lower.includes('bang') || lower.includes('promotion') || lower.includes('absorption') || lower.includes('copy')) return 'Exponentials';
  return 'Other';
}

// =============================================================================
// Rule Application
// =============================================================================

/**
 * Get applicable rules for a sequent
 */
export function getApplicableRules(seq: V2Sequent, options: GetRulesOptions = {}): ApplicableRule[] {
  const { mode = 'unfocused' } = options;
  const calc = getCalculus();
  const applicable: ApplicableRule[] = [];

  // Check succedent (R position) - right rules
  if (seq.succedent && !isAtomicFormula(seq.succedent)) {
    const connective = getConnectiveName(seq.succedent);
    if (connective) {
      const ruleName = `${connective}_r`;
      if (calc.rules[ruleName]) {
        applicable.push({
          name: ruleName,
          category: getRuleCategory(ruleName),
          ruleStrings: [calc.rules[ruleName].pretty || ruleName],
          premises: [],
          position: 'R',
          principalFormula: renderFormula(seq.succedent, 'ascii'),
          principalFormulaLatex: renderFormula(seq.succedent, 'latex'),
          splitContext: isContextSplittingRule(ruleName),
        });
      }

      // Check for alternatives (plus_r2, with_r, etc.)
      const altName = `${connective}_r2`;
      if (calc.rules[altName]) {
        applicable.push({
          name: altName,
          category: getRuleCategory(altName),
          ruleStrings: [calc.rules[altName].pretty || altName],
          premises: [],
          position: 'R',
          principalFormula: renderFormula(seq.succedent, 'ascii'),
          principalFormulaLatex: renderFormula(seq.succedent, 'latex'),
          splitContext: false,
        });
      }
    }
  }

  // Check linear context - left rules
  const linear = seq.linear || [];
  for (let i = 0; i < linear.length; i++) {
    const formula = linear[i];
    if (!isAtomicFormula(formula)) {
      const connective = getConnectiveName(formula);
      if (connective) {
        const ruleName = `${connective}_l`;
        if (calc.rules[ruleName]) {
          applicable.push({
            name: ruleName,
            category: getRuleCategory(ruleName),
            ruleStrings: [calc.rules[ruleName].pretty || ruleName],
            premises: [],
            position: String(i),
            principalFormula: renderFormula(formula, 'ascii'),
            principalFormulaLatex: renderFormula(formula, 'latex'),
            splitContext: isContextSplittingRule(ruleName),
          });
        }

        // Check alternatives (with_l1, with_l2)
        for (const suffix of ['1', '2']) {
          const altName = `${connective}_l${suffix}`;
          if (calc.rules[altName]) {
            applicable.push({
              name: altName,
              category: getRuleCategory(altName),
              ruleStrings: [calc.rules[altName].pretty || altName],
              premises: [],
              position: String(i),
              principalFormula: renderFormula(formula, 'ascii'),
              principalFormulaLatex: renderFormula(formula, 'latex'),
              splitContext: false,
            });
          }
        }
      }
    }
  }

  // Check for Identity rule
  if (seq.succedent && isAtomicFormula(seq.succedent)) {
    for (let i = 0; i < linear.length; i++) {
      const formula = linear[i];
      if (isAtomicFormula(formula)) {
        // Simple equality check for atoms
        if (formulasMatch(formula, seq.succedent)) {
          applicable.push({
            name: 'id',
            category: 'Identity',
            ruleStrings: ['A ⊢ A'],
            premises: [],
            position: String(i),
            principalFormula: renderFormula(seq.succedent, 'ascii'),
            principalFormulaLatex: renderFormula(seq.succedent, 'latex'),
            splitContext: false,
          });
          break;
        }
      }
    }
  }

  return applicable;
}

/**
 * Simple formula equality check
 */
function formulasMatch(a: Formula, b: Formula): boolean {
  if (a.tag !== b.tag) return false;
  if (a.children.length !== b.children.length) return false;
  for (let i = 0; i < a.children.length; i++) {
    const ac = a.children[i];
    const bc = b.children[i];
    if (typeof ac === 'string' && typeof bc === 'string') {
      if (ac !== bc) return false;
    } else if (typeof ac === 'object' && typeof bc === 'object') {
      if (!formulasMatch(ac as Formula, bc as Formula)) return false;
    } else {
      return false;
    }
  }
  return true;
}

/**
 * Apply a rule to a proof tree node
 */
export function applyRule(
  pt: ProofTreeNode,
  ruleName: string,
  position: string
): ProofTreeNode | null {
  const Seq = getSeqModule();
  const calc = getCalculus();
  const browser = getBrowserModule();

  // Clone the proof tree
  const ptCopy = cloneProofTree(pt);
  const seq = ptCopy.conclusion;

  // Handle Identity rule
  if (ruleName === 'id' || ruleName === 'Id') {
    const idx = parseInt(position, 10);
    const linear = seq.linear || [];

    if (idx >= 0 && idx < linear.length && seq.succedent) {
      if (formulasMatch(linear[idx], seq.succedent)) {
        ptCopy.type = 'id';
        ptCopy.premisses = [];
        ptCopy.proven = true;
        return ptCopy;
      }
    }
    return null;
  }

  // Get rule spec
  const prover = browser.createProver(calc);
  const ruleSpecs = prover.ruleSpecs;
  const spec = ruleSpecs[ruleName];

  if (!spec) {
    console.error(`Rule ${ruleName} not found`);
    return null;
  }

  // Determine formula and index
  let formula: Formula;
  let idx = -1;

  if (position === 'R') {
    formula = seq.succedent;
  } else {
    idx = parseInt(position, 10);
    const linear = seq.linear || [];
    if (idx < 0 || idx >= linear.length) return null;
    formula = linear[idx];
  }

  // Create premises using rule spec
  const premises = spec.makePremises(formula, seq, idx);
  if (!premises) return null;

  // Update proof tree
  ptCopy.type = ruleName;
  ptCopy.premisses = premises.map((premise: V2Sequent) => createProofTree(premise));
  ptCopy.proven = premises.length === 0;

  return ptCopy;
}

/**
 * Apply a context-splitting rule with a custom split
 */
export function applyRuleWithSplit(
  pt: ProofTreeNode,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] }
): ProofTreeNode | null {
  const Seq = getSeqModule();
  const ptCopy = cloneProofTree(pt);
  const seq = ptCopy.conclusion;
  const linear = seq.linear || [];
  const cart = seq.cartesian || [];

  // Determine formula
  let formula: Formula;
  let idx = -1;

  if (position === 'R') {
    formula = seq.succedent;
  } else {
    idx = parseInt(position, 10);
    if (idx < 0 || idx >= linear.length) return null;
    formula = linear[idx];
  }

  // Build premises with user's split
  const [A, B] = formula.children as Formula[];

  // Convert string indices to formula arrays
  const p1Formulas = split.premise1.map(i => linear[parseInt(i, 10)]).filter(Boolean);
  const p2Formulas = split.premise2.map(i => linear[parseInt(i, 10)]).filter(Boolean);

  let premise1: V2Sequent;
  let premise2: V2Sequent;

  if (ruleName === 'tensor_r' || ruleName === 'Tensor_R') {
    premise1 = Seq.fromArrays(p1Formulas, cart, A);
    premise2 = Seq.fromArrays(p2Formulas, cart, B);
  } else if (ruleName === 'loli_l' || ruleName === 'Loli_L') {
    premise1 = Seq.fromArrays(p1Formulas, cart, A);
    premise2 = Seq.fromArrays([...p2Formulas, B], cart, seq.succedent);
  } else {
    return null;
  }

  ptCopy.type = ruleName;
  ptCopy.premisses = [createProofTree(premise1), createProofTree(premise2)];

  return ptCopy;
}

/**
 * Get context entries for split dialog
 */
export function getContextEntries(seq: V2Sequent, excludeId?: string): ContextEntry[] {
  const entries: ContextEntry[] = [];
  const linear = seq.linear || [];

  for (let i = 0; i < linear.length; i++) {
    if (excludeId && String(i) === excludeId) continue;

    const formula = linear[i];
    entries.push({
      id: String(i),
      formula: renderFormula(formula, 'ascii'),
      formulaLatex: renderFormula(formula, 'latex'),
    });
  }

  return entries;
}

/**
 * Preview split subgoals
 */
export function previewSplitSubgoals(
  seq: V2Sequent,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] }
): V2Sequent[] | null {
  const testPt = createProofTree(seq);
  const result = applyRuleWithSplit(testPt, ruleName, position, split);
  if (!result) return null;
  return result.premisses.map(p => p.conclusion);
}

// =============================================================================
// Auto-prove
// =============================================================================

/**
 * Run automatic proof search
 */
export async function autoProve(
  pt: ProofTreeNode,
  options: AutoProveOptions = {}
): Promise<{ success: boolean; pt: ProofTreeNode }> {
  const result = await autoProveV2(pt.conclusion);

  if (!result.success || !result.proofTree) {
    return { success: false, pt };
  }

  // Convert v2 proof tree to our format
  const convertTree = (v2pt: V2ProofNode): ProofTreeNode => ({
    conclusion: v2pt.conclusion,
    premisses: v2pt.premisses.map(convertTree),
    type: v2pt.rule || '???',
    proven: v2pt.proven,
    delta_in: {},
    delta_out: {},
  });

  return {
    success: true,
    pt: convertTree(result.proofTree),
  };
}

// =============================================================================
// Focus Actions (for focused mode)
// =============================================================================

/**
 * Apply a focus action
 */
export function applyFocusAction(pt: ProofTreeNode, position: string): ProofTreeNode | null {
  const ptCopy = cloneProofTree(pt);

  // Create premise with same sequent
  const premiseNode = createProofTree(ptCopy.conclusion);

  ptCopy.premisses = [premiseNode];
  ptCopy.type = position === 'R' ? 'Focus_R' : 'Focus_L';

  return ptCopy;
}

/**
 * Apply blur action
 */
export function applyBlurAction(pt: ProofTreeNode): ProofTreeNode | null {
  return cloneProofTree(pt);
}

/**
 * Collapse focus steps
 */
export function collapseFocusSteps(pt: ProofTreeNode): ProofTreeNode {
  if (pt.type === 'Focus_L' || pt.type === 'Focus_R') {
    if (pt.premisses.length === 1) {
      const child = collapseFocusSteps(pt.premisses[0]);
      return {
        ...child,
        conclusion: pt.conclusion,
        premisses: child.premisses.map(collapseFocusSteps),
      };
    }
  }

  if (pt.premisses.length === 0) return pt;

  return {
    ...pt,
    premisses: pt.premisses.map(collapseFocusSteps),
  };
}

// =============================================================================
// Rendering
// =============================================================================

/**
 * Simplify LaTeX for display
 */
function simplifyLatex(latex: string): string {
  return latex
    .replace(/\?\s*X/g, '\\Gamma')
    .replace(/\?\s*Y/g, '\\Delta')
    .replace(/\?\s*Z/g, '\\Sigma')
    .replace(/F\?\s*([A-Z])/g, '$1')
    .replace(/S\?\s*([A-Z])/g, '$1')
    .replace(/\\cdot\s*:/g, '')
    .replace(/--\s*:/g, '')
    .replace(/\s+/g, ' ')
    .trim();
}

/**
 * Convert sequent to LaTeX
 */
export function sequentToLatex(seq: V2Sequent, simplify = true, focusInfo?: FocusInfo): string {
  try {
    const raw = renderSequent(seq, 'latex');
    let result = simplify ? simplifyLatex(raw) : raw;

    // Add focus brackets if needed
    if (focusInfo?.position === 'R' && seq.succedent) {
      const succLatex = simplify
        ? simplifyLatex(renderFormula(seq.succedent, 'latex'))
        : renderFormula(seq.succedent, 'latex');
      result = result.replace(succLatex, `[${succLatex}]`);
    } else if (focusInfo?.position === 'L' && focusInfo?.id) {
      const idx = parseInt(focusInfo.id, 10);
      const linear = seq.linear || [];
      if (idx >= 0 && idx < linear.length) {
        const focusedLatex = simplify
          ? simplifyLatex(renderFormula(linear[idx], 'latex'))
          : renderFormula(linear[idx], 'latex');
        result = result.replace(focusedLatex, `[${focusedLatex}]`);
      }
    }

    return result;
  } catch {
    return String(seq);
  }
}

/**
 * Convert sequent to ASCII
 */
export function sequentToAscii(seq: V2Sequent): string {
  try {
    return renderSequent(seq, 'ascii');
  } catch {
    return String(seq);
  }
}

// =============================================================================
// Structured Proof Export
// =============================================================================

export interface StructuredStep {
  level: number;
  step: number;
  sequent: V2Sequent;
  sequentLatex: string;
  ruleName: string;
  isProven: boolean;
  isLeaf: boolean;
  children: StructuredStep[];
  path: number[];
}

export function ptToStructuredProof(
  pt: ProofTreeNode,
  level = 1,
  step = 1,
  path: number[] = []
): StructuredStep {
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

// =============================================================================
// Serialization
// =============================================================================

export interface SerializedSequent {
  ascii: string;
  latex: string;
}

export interface SerializedProofNode {
  rule: string;
  conclusion: SerializedSequent;
  proven: boolean;
  premises: SerializedProofNode[];
}

export interface SerializedProof {
  version: string;
  timestamp: string;
  goal: string;
  goalLatex: string;
  complete: boolean;
  mode: 'unfocused' | 'focused';
  stats: {
    totalNodes: number;
    provenNodes: number;
    unprovenNodes: number;
    maxDepth: number;
  };
  tree: SerializedProofNode;
}

function calculateDepth(pt: ProofTreeNode): number {
  if (pt.premisses.length === 0) return 1;
  return 1 + Math.max(...pt.premisses.map(calculateDepth));
}

export function serializeProofTree(
  pt: ProofTreeNode,
  mode: 'unfocused' | 'focused' = 'unfocused'
): SerializedProof {
  const counts = countNodes(pt);
  const depth = calculateDepth(pt);
  const complete = isProofComplete(pt);

  const goal = sequentToAscii(pt.conclusion);
  const goalLatex = sequentToLatex(pt.conclusion);

  const serializeNode = (node: ProofTreeNode): any => ({
    rule: node.type,
    conclusion: {
      ascii: sequentToAscii(node.conclusion),
      latex: sequentToLatex(node.conclusion),
    },
    proven: node.type !== '???' && (node.premisses.length === 0 || node.proven),
    premises: node.premisses.map(serializeNode),
  });

  return {
    version: '2.0',
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
    tree: serializeNode(pt),
  };
}

// =============================================================================
// Rule Details (for inspection)
// =============================================================================

export interface SubstitutionEntry {
  variable: string;
  variableLatex: string;
  value: string;
  valueLatex: string;
}

export interface RuleApplicationDetails {
  ruleName: string;
  category: string;
  abstractConclusion: string;
  abstractConclusionLatex: string;
  abstractPremises: string[];
  abstractPremisesLatex: string[];
  actualConclusion: string;
  actualConclusionLatex: string;
  substitution: SubstitutionEntry[];
  instantiatedPremises: string[];
  instantiatedPremisesLatex: string[];
}

export function getRuleApplicationDetails(pt: ProofTreeNode): RuleApplicationDetails | null {
  const ruleName = pt.type;

  if (ruleName === '???') return null;

  const calc = getCalculus();
  const rule = calc.rules[ruleName];

  return {
    ruleName,
    category: getRuleCategory(ruleName),
    abstractConclusion: rule?.pretty || ruleName,
    abstractConclusionLatex: rule?.pretty || ruleName,
    abstractPremises: [],
    abstractPremisesLatex: [],
    actualConclusion: sequentToAscii(pt.conclusion),
    actualConclusionLatex: sequentToLatex(pt.conclusion),
    substitution: [],
    instantiatedPremises: pt.premisses.map(p => sequentToAscii(p.conclusion)),
    instantiatedPremisesLatex: pt.premisses.map(p => sequentToLatex(p.conclusion)),
  };
}
