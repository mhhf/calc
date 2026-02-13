/**
 * Browser-compatible proof logic for the interactive prover.
 *
 * ARCHITECTURE: This is a thin layer over lib/browser.js
 * - All formulas/sequents use content-addressed hashes (numbers)
 * - The Store is the single source of truth
 * - Never create AST objects directly - always use Store.intern or browser APIs
 */

import {
  parseSequent as browserParseSequent,
  parseFormula as browserParseFormula,
  renderFormula as browserRenderFormula,
  renderSequent as browserRenderSequent,
  getCalculus,
  getBrowserModule,
  getSeqModule,
  autoProveV2,
  getManualProofAPI,
} from './calculus';

// =============================================================================
// Types - All formulas are hashes (numbers), not AST objects
// =============================================================================

/** A formula hash (content-addressed reference into the Store) */
export type FormulaHash = number;

/** A sequent with hash-based formulas */
export type V2Sequent = {
  contexts: {
    linear: FormulaHash[];
    cartesian: FormulaHash[];
  };
  succedent: FormulaHash;
  _hash?: number | null;
};

export type V2ProofNode = {
  conclusion: V2Sequent;
  premisses: V2ProofNode[];
  rule: string | null;
  proven: boolean;
};

export interface ApplicableRule {
  name: string;
  category: string;
  ruleStrings: string[];
  premises: V2Sequent[];
  position: string;  // 'R' or index for L
  principalFormula?: string;
  principalFormulaLatex?: string;
  splitContext?: boolean;
  _apiAction?: any; // Internal: pre-computed action from ManualProofAPI
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
// Store Access - The single source of truth
// =============================================================================

/** Look up a hash in the Store to get the AST node */
function getNode(hash: FormulaHash): { tag: string; children: any[] } | null {
  const browser = getBrowserModule();
  return browser.Store?.get?.(hash) || null;
}

/** Get the tag (connective name) of a formula hash */
function getTag(hash: FormulaHash): string | null {
  const node = getNode(hash);
  return node?.tag || null;
}

/** Check if a formula hash is atomic (atom or freevar) */
function isAtomic(hash: FormulaHash): boolean {
  const tag = getTag(hash);
  return tag === 'atom' || tag === 'freevar';
}

/** Get children hashes from a formula */
function getChildren(hash: FormulaHash): FormulaHash[] {
  const node = getNode(hash);
  return (node?.children || []).filter((c: any) => typeof c === 'number');
}

// =============================================================================
// Initialization
// =============================================================================

let initialized = false;

export function initBrowserRuleset(): void {
  getCalculus();
  initialized = true;
}

// =============================================================================
// Parsing - Delegates to browser module
// =============================================================================

export function parseSequent(input: string): V2Sequent {
  return browserParseSequent(input) as V2Sequent;
}

export function parseFormula(input: string): FormulaHash {
  return browserParseFormula(input) as FormulaHash;
}

// =============================================================================
// Rendering - Delegates to browser module (which handles hashes)
// =============================================================================

export function renderFormula(hash: FormulaHash, format: 'ascii' | 'latex' = 'ascii'): string {
  return browserRenderFormula(hash, format);
}

export function sequentToLatex(seq: V2Sequent, simplify = true, focusInfo?: FocusInfo): string {
  try {
    // Use ManualProofAPI for focus-aware rendering
    if (focusInfo?.position) {
      const api = getManualProofAPI();
      const focus = {
        position: focusInfo.position,
        index: focusInfo.id != null ? parseInt(focusInfo.id, 10) : -1,
      };
      let result = api.renderSequent(seq, 'latex', focus);

      if (simplify) {
        result = result
          .replace(/\?\s*X/g, '\\Gamma')
          .replace(/\?\s*Y/g, '\\Delta')
          .replace(/--\s*:/g, '')
          .replace(/\s+/g, ' ')
          .trim();
      }

      return result;
    }

    // Default rendering without focus
    let result = browserRenderSequent(seq, 'latex');

    if (simplify) {
      result = result
        .replace(/\?\s*X/g, '\\Gamma')
        .replace(/\?\s*Y/g, '\\Delta')
        .replace(/--\s*:/g, '')
        .replace(/\s+/g, ' ')
        .trim();
    }

    return result;
  } catch (e) {
    console.error('sequentToLatex error:', e);
    return '?';
  }
}

export function sequentToAscii(seq: V2Sequent, focusInfo?: FocusInfo): string {
  try {
    if (focusInfo?.position) {
      const api = getManualProofAPI();
      const focus = {
        position: focusInfo.position,
        index: focusInfo.id != null ? parseInt(focusInfo.id, 10) : -1,
      };
      return api.renderSequent(seq, 'ascii', focus);
    }
    return browserRenderSequent(seq, 'ascii');
  } catch {
    return '?';
  }
}

// =============================================================================
// Proof Tree Operations
// =============================================================================

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

export function isProofComplete(pt: ProofTreeNode): boolean {
  if (pt.type === '???') return false;
  if (pt.premisses.length === 0) return true;
  return pt.premisses.every(isProofComplete);
}

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

export function getNodeAtPath(pt: ProofTreeNode, path: number[]): ProofTreeNode | null {
  if (path.length === 0) return pt;
  const [head, ...tail] = path;
  if (head >= pt.premisses.length) return null;
  return getNodeAtPath(pt.premisses[head], tail);
}

export function setNodeAtPath(
  root: ProofTreeNode,
  path: number[],
  newNode: ProofTreeNode
): ProofTreeNode {
  if (path.length === 0) return newNode;

  const [head, ...tail] = path;
  const newPremisses = root.premisses.map((p, i) =>
    i === head ? setNodeAtPath(p, tail, newNode) : p
  );

  return { ...root, premisses: newPremisses };
}

export function cloneProofTree(pt: ProofTreeNode): ProofTreeNode {
  const Seq = getSeqModule();
  return {
    conclusion: Seq.copy(pt.conclusion),
    premisses: pt.premisses.map(cloneProofTree),
    type: pt.type,
    proven: pt.proven,
    delta_in: { ...pt.delta_in },
    delta_out: { ...pt.delta_out },
  };
}

// =============================================================================
// Context Helpers
// =============================================================================

export function getLinearContext(seq: V2Sequent): FormulaHash[] {
  return seq.contexts?.linear || [];
}

export function getCartesianContext(seq: V2Sequent): FormulaHash[] {
  return seq.contexts?.cartesian || [];
}

// =============================================================================
// Rule Helpers
// =============================================================================

const CONNECTIVE_CATEGORIES: Record<string, string> = {
  tensor: 'Multiplicatives', loli: 'Multiplicatives', one: 'Multiplicatives',
  with: 'Additives', plus: 'Additives',
  bang: 'Exponentials',
};

function getRuleCategory(ruleName: string): string {
  if (ruleName === 'id') return 'Identity';
  if (ruleName === 'Focus_L' || ruleName === 'Focus_R') return 'Focus';
  const calc = getCalculus();
  const rule = calc?.rules?.[ruleName];
  const connective = rule?.descriptor?.connective;
  if (connective && CONNECTIVE_CATEGORIES[connective]) return CONNECTIVE_CATEGORIES[connective];
  if (rule?.structural) return 'Structural';
  return 'Other';
}

/**
 * Get applicable rules for a proof tree node.
 *
 * SUCKLESS DESIGN: This function extracts ALL state it needs from the node.
 * The caller doesn't need to manually extract and pass focus state.
 * The node IS the source of truth - we read delta_in directly.
 */
export function getApplicableRules(
  seqOrNode: V2Sequent | ProofTreeNode,
  options: GetRulesOptions = {}
): ApplicableRule[] {
  const { mode = 'unfocused', focusState: optionsFocusState } = options;

  // Handle both sequent and node input for backward compatibility
  let seq: V2Sequent;
  let nodeFocusState: { position: string; id: string | null } | null = null;

  if ('conclusion' in seqOrNode) {
    // It's a ProofTreeNode - extract everything from it
    const node = seqOrNode as ProofTreeNode;
    seq = node.conclusion;

    // SUCKLESS: Read focus state directly from node's delta_in
    // No need for caller to extract and pass it
    if (node.delta_in?.focusPosition) {
      nodeFocusState = {
        position: node.delta_in.focusPosition,
        id: node.delta_in.focusId,
      };
    }
  } else {
    // It's a raw sequent
    seq = seqOrNode as V2Sequent;
  }

  // Use node's focus state if available, otherwise use options (for backward compat)
  const focusState = nodeFocusState || optionsFocusState;

  // Use ManualProofAPI as single source of truth
  const api = getManualProofAPI();

  // Create proof state with focus info
  const proofState = api.createProofState(seq);
  // Always propagate focus from delta_in when present (focused mode needs it)
  if (focusState?.position) {
    proofState.focus = {
      position: focusState.position,
      index: focusState.id != null ? parseInt(focusState.id, 10) : -1,
      hash: null,
    };
  }

  // Get applicable actions from the prover, passing mode
  const actions = api.getApplicableActions(proofState, { mode });

  // Convert actions to ApplicableRule format
  const applicable: ApplicableRule[] = actions.map((action: any) => {
    const displayName = action.displayName || action.name;
    const ruleSchema = api.getAbstractRule(displayName);

    return {
      name: action.name,
      category: action.type === 'focus' ? 'Focus' : getRuleCategory(action.name),
      ruleStrings: [ruleSchema.conclusion, ...(ruleSchema.premises || [])],
      premises: action.premises || [],
      position: action.position === 'R' ? 'R' : String(action.index),
      principalFormula: action.formula ? renderFormula(action.formula, 'ascii') : '',
      principalFormulaLatex: action.formula ? renderFormula(action.formula, 'latex') : '',
      splitContext: action.needsContextSplit || false,
      _apiAction: action,
    };
  });

  return applicable;
}

export function applyRule(
  pt: ProofTreeNode,
  ruleName: string,
  position: string,
  apiAction?: any // Optional pre-computed action from getApplicableRules
): ProofTreeNode | null {
  const api = getManualProofAPI();
  const seq = pt.conclusion;

  // Get the action from API if not passed
  let action = apiAction;
  if (!action) {
    // Build proof state with current focus (from delta_in if present)
    const proofState = api.createProofState(seq);
    if (pt.delta_in?.focusPosition) {
      proofState.focus = {
        position: pt.delta_in.focusPosition,
        index: pt.delta_in.focusId != null ? parseInt(pt.delta_in.focusId, 10) : -1,
        hash: null,
      };
    }

    // Find the matching action
    const actions = api.getApplicableActions(proofState);
    action = actions.find((a: any) => {
      if (a.name !== ruleName) return false;
      if (a.position === 'R') return position === 'R';
      return String(a.index) === position;
    });
  }

  if (!action) {
    console.error('[applyRule] No matching action found for', ruleName, position);
    return null;
  }

  // Check if context split is needed
  if (action.needsContextSplit) {
    // Caller should use applyRuleWithSplit instead
    console.log('[applyRule] Context split required for', ruleName);
    return null;
  }

  // Build proof state and delegate to API — single source of truth
  const proofState = api.createProofState(seq);
  if (pt.delta_in?.focusPosition) {
    proofState.focus = {
      position: pt.delta_in.focusPosition,
      index: pt.delta_in.focusId != null ? parseInt(pt.delta_in.focusId, 10) : -1,
      hash: null,
    };
  }
  const newState = api.applyAction(proofState, action);
  return proofStateToTreeNode(newState);
}

/** Convert a ProofState (from ManualProofAPI) to a ProofTreeNode (for UI) */
function proofStateToTreeNode(state: any): ProofTreeNode {
  const deltaIn: Record<string, any> = {};
  if (state.focus) {
    deltaIn.focusPosition = state.focus.position;
    deltaIn.focusId = state.focus.index >= 0 ? String(state.focus.index) : null;
  }
  return {
    conclusion: state.conclusion,
    premisses: (state.premisses || []).map(proofStateToTreeNode),
    type: state.rule || '???',
    proven: state.proven,
    delta_in: deltaIn,
    delta_out: {},
  };
}

export function applyRuleWithSplit(
  pt: ProofTreeNode,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] },
  apiAction?: any // Optional pre-computed action from getApplicableRules
): ProofTreeNode | null {
  const api = getManualProofAPI();
  const Seq = getSeqModule();
  const ptCopy = cloneProofTree(pt);
  const seq = ptCopy.conclusion;
  const linear = getLinearContext(seq);
  const cart = getCartesianContext(seq);

  // Get the action from API if not passed
  let action = apiAction;
  if (!action) {
    const proofState = api.createProofState(seq);
    if (pt.delta_in?.focusPosition) {
      proofState.focus = {
        position: pt.delta_in.focusPosition,
        index: pt.delta_in.focusId != null ? parseInt(pt.delta_in.focusId, 10) : -1,
        hash: null,
      };
    }

    const actions = api.getApplicableActions(proofState);
    action = actions.find((a: any) => {
      if (a.name !== ruleName) return false;
      if (a.position === 'R') return position === 'R';
      return String(a.index) === position;
    });
  }

  if (!action || !action.barePremises) {
    console.error('[applyRuleWithSplit] No matching action or bare premises found');
    return null;
  }

  // Map split IDs to formula hashes via contextEntries (not linear indices!)
  // split.premise1/2 contain entry IDs from contextEntries, which correspond to
  // remainingDelta (focused formula already removed), not the full linear context.
  const entryMap = new Map<string, number>();
  if (action.contextEntries) {
    action.contextEntries.forEach((entry: any, i: number) => {
      entryMap.set(String(i), entry.hash);
    });
  } else {
    // Fallback: no contextEntries means no focus, IDs map directly to linear
    linear.forEach((hash, i) => { entryMap.set(String(i), hash); });
  }
  const p1Hashes = split.premise1.map(id => entryMap.get(id)).filter((h): h is number => h !== undefined);
  const p2Hashes = split.premise2.map(id => entryMap.get(id)).filter((h): h is number => h !== undefined);

  // Build full premises with split context
  const barePremises = action.barePremises;
  const premises = barePremises.map((barePremise: V2Sequent, i: number) => {
    const premiseLinear = barePremise.contexts?.linear || [];
    const additions = i === 0 ? p1Hashes : p2Hashes;
    return Seq.fromArrays([...additions, ...premiseLinear], cart, barePremise.succedent);
  });

  ptCopy.type = action.displayName || ruleName;
  ptCopy.premisses = premises.map(createProofTree);

  return ptCopy;
}

export function getContextEntries(seq: V2Sequent, excludeId?: string, apiAction?: any): ContextEntry[] {
  // If API action has context entries (from delta tracking), use those
  if (apiAction?.contextEntries) {
    return apiAction.contextEntries.map((entry: any, i: number) => ({
      id: String(i),
      formula: entry.formula,
      formulaLatex: entry.formulaLatex,
      hash: entry.hash,
    }));
  }

  // Fallback to simple linear context
  const linear = getLinearContext(seq);
  return linear
    .map((hash, i) => ({
      id: String(i),
      formula: renderFormula(hash, 'ascii'),
      formulaLatex: renderFormula(hash, 'latex'),
    }))
    .filter(entry => !excludeId || entry.id !== excludeId);
}

export function previewSplitSubgoals(
  seq: V2Sequent,
  ruleName: string,
  position: string,
  split: { premise1: string[]; premise2: string[] },
  apiAction?: any
): V2Sequent[] | null {
  const testPt = createProofTree(seq);
  const result = applyRuleWithSplit(testPt, ruleName, position, split, apiAction);
  if (!result) return null;
  return result.premisses.map(p => p.conclusion);
}

// =============================================================================
// Auto-prove
// =============================================================================

export async function autoProve(
  pt: ProofTreeNode,
  options: AutoProveOptions = {}
): Promise<{ success: boolean; pt: ProofTreeNode }> {
  const result = await autoProveV2(pt.conclusion);

  if (!result.success || !result.proofTree) {
    return { success: false, pt };
  }

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
// Focus Actions
// =============================================================================

export function collapseFocusSteps(pt: ProofTreeNode): ProofTreeNode {
  if ((pt.type === 'Focus_L' || pt.type === 'Focus_R') && pt.premisses.length === 1) {
    const child = collapseFocusSteps(pt.premisses[0]);
    return {
      ...child,
      conclusion: pt.conclusion,
      premisses: child.premisses.map(collapseFocusSteps),
    };
  }
  if (pt.premisses.length === 0) return pt;
  return { ...pt, premisses: pt.premisses.map(collapseFocusSteps) };
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
  const children = pt.premisses.map((p, i) =>
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

  const serializeNode = (node: ProofTreeNode): SerializedProofNode => {
    const focusInfo = node.delta_in?.focusPosition
      ? { position: node.delta_in.focusPosition as 'L' | 'R', id: node.delta_in.focusId }
      : undefined;
    return {
      rule: node.type,
      conclusion: {
        ascii: sequentToAscii(node.conclusion, focusInfo),
        latex: sequentToLatex(node.conclusion, true, focusInfo),
      },
      proven: node.type !== '???' && (node.premisses.length === 0 || node.proven),
      premises: node.premisses.map(serializeNode),
    };
  };

  return {
    version: '2.0',
    timestamp: new Date().toISOString(),
    goal: sequentToAscii(pt.conclusion),
    goalLatex: sequentToLatex(pt.conclusion),
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
// Rule Details
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
  if (pt.type === '???') return null;

  const api = getManualProofAPI();
  const ruleSchema = api.getAbstractRule(pt.type);

  return {
    ruleName: pt.type,
    category: getRuleCategory(pt.type),
    abstractConclusion: ruleSchema.conclusion,
    abstractConclusionLatex: ruleSchema.conclusion,
    abstractPremises: ruleSchema.premises || [],
    abstractPremisesLatex: ruleSchema.premises || [],
    actualConclusion: sequentToAscii(pt.conclusion),
    actualConclusionLatex: sequentToLatex(pt.conclusion),
    substitution: [],
    instantiatedPremises: pt.premisses.map(p => sequentToAscii(p.conclusion)),
    instantiatedPremisesLatex: pt.premisses.map(p => sequentToLatex(p.conclusion)),
  };
}

// Legacy type aliases for backwards compatibility
export type Formula = FormulaHash;
export type Sequent = V2Sequent;

// =============================================================================
// Browser Console Debug Utility
// =============================================================================

// Expose debug utilities to window for browser console testing (dev only)
if (import.meta.env.DEV && typeof window !== 'undefined') {
  (window as any).calcDebug = {
    parseSequent,
    createProofTree,
    getApplicableRules,
    applyRule,
    getContextEntries,
    getLinearContext,
    cloneProofTree,
  };
}
