/**
 * v2 Calculus API for UI
 *
 * Provides a unified API for the v2 prover and parser that works
 * in the browser. Lazily initializes from the pre-bundled ILL spec.
 */

// @ts-ignore - CommonJS module
import * as browserModule from '../../../lib/v2/browser.js';
// @ts-ignore - Generated JSON bundle
import illBundle from '../../../out/ill-v2.json';

const browser = (browserModule as any).default || browserModule;

// Types
export interface Formula {
  tag: string;
  children: (Formula | string)[];
}

export interface Sequent {
  linear: Formula[];
  cartesian: Formula[];
  succedent: Formula;
}

export interface ProofTree {
  rule: string;
  conclusion: Sequent;
  premises: ProofTree[];
  success?: boolean;
}

export interface ProveResult {
  success: boolean;
  proofTree?: ProofTree;
  sequent?: Sequent;
  formatted?: string;
}

// Initialization
let initialized = false;

function ensureInitialized() {
  if (!initialized) {
    browser.initFromBundle(illBundle);
    initialized = true;
  }
}

/**
 * Parse a formula string
 */
export function parseFormula(input: string): Formula {
  ensureInitialized();
  return browser.parseFormula(input);
}

/**
 * Parse a sequent string (e.g., "A, B |- C")
 */
export function parseSequent(input: string): Sequent {
  ensureInitialized();
  return browser.parseSequent(input);
}

/**
 * Render a formula to string
 */
export function renderFormula(formula: Formula, format: 'ascii' | 'latex' = 'ascii'): string {
  ensureInitialized();
  try {
    return browser.render(formula, format);
  } catch (e) {
    console.error('renderFormula error:', e, 'formula:', formula, 'format:', format);
    throw e;
  }
}

/**
 * Render a sequent to string
 */
export function renderSequent(seq: Sequent, format: 'ascii' | 'latex' = 'ascii'): string {
  ensureInitialized();
  return browser.render(seq, format);
}

/**
 * Prove a sequent string
 */
export async function prove(sequentStr: string): Promise<ProveResult> {
  ensureInitialized();
  return browser.proveString(sequentStr);
}

/**
 * Get the loaded calculus (for advanced use)
 */
export function getCalculus() {
  ensureInitialized();
  return browser.getCalculus();
}

/**
 * Check if a formula is atomic
 */
export function isAtomic(formula: Formula): boolean {
  return formula?.tag === 'atom' || formula?.tag === 'freevar';
}

/**
 * Get the connective name from a formula
 */
export function getConnective(formula: Formula): string | null {
  if (!formula?.tag) return null;
  if (formula.tag === 'atom' || formula.tag === 'freevar') return null;
  return formula.tag;
}

/**
 * Build AST tree data for visualization.
 * Returns a TreeNode structure compatible with ASTView.tsx
 */
export function buildASTTree(formula: Formula): any {
  if (!formula?.tag) return null;

  // Build the head object expected by ASTView.tsx
  const node: any = {
    head: {
      constr: formula.tag,
      name: formula.tag
    },
    children: []
  };

  for (const child of formula.children) {
    if (typeof child === 'string') {
      // Leaf node (variable name, atom name, etc.)
      node.children.push({
        head: {
          constr: 'leaf',
          name: child,
          ascii: child
        },
        children: []
      });
    } else if (child?.tag) {
      node.children.push(buildASTTree(child));
    }
  }

  return node;
}

/**
 * Get info about the calculus rules
 */
export function getRulesInfo() {
  ensureInitialized();
  const calc = browser.getCalculus();
  return {
    rules: calc.rules,
    polarity: calc.polarity,
    invertible: calc.invertible
  };
}

/**
 * Get connective info for display
 */
export function getConnectives() {
  ensureInitialized();
  const calc = browser.getCalculus();
  const result: any[] = [];

  for (const [name, constr] of Object.entries(calc.constructors) as [string, any][]) {
    const ann = constr.annotations;
    if (constr.returnType === 'formula' && ann?.ascii) {
      result.push({
        name,
        ascii: ann.ascii,
        latex: ann.latex,
        prec: typeof ann.prec === 'object'
          ? ann.prec.precedence
          : ann.prec,
        polarity: calc.polarity[name],
        category: ann.category
      });
    }
  }

  return result;
}

/**
 * Format proof tree for display
 */
export function formatProofTree(tree: any): string {
  if (!tree) return '';

  const lines: string[] = [];

  function addNode(node: any, indent: number) {
    const prefix = '  '.repeat(indent);
    const seq = node.conclusion
      ? renderSequent(node.conclusion, 'ascii')
      : '?';
    lines.push(`${prefix}${node.rule}: ${seq}`);

    for (const premise of node.premises || []) {
      addNode(premise, indent + 1);
    }
  }

  addNode(tree, 0);
  return lines.join('\n');
}

// ============================================================================
// Calculus Overview API (for CalculusOverview.tsx and MetaOverview.tsx)
// ============================================================================

export interface ConnectiveInfo {
  name: string;
  ascii: string;
  latex: string;
  polarity: 'positive' | 'negative' | 'unknown';
  category?: string;
  precedence?: number;
  arity: number;
}

export interface RuleInfo {
  name: string;
  pretty: string;
  numPremises: number;
  invertible: boolean | null;
  structural: boolean;
  category: string;
}

export interface BNFProduction {
  lhs: string;
  alternatives: string[];
}

/**
 * Get the calculus name
 */
export function getCalculusName(): string {
  ensureInitialized();
  const calc = browser.getCalculus();
  return calc.name || 'Linear Logic';
}

/**
 * Get all formula connectives with metadata
 */
export function getFormulaConnectives(): ConnectiveInfo[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  const result: ConnectiveInfo[] = [];

  for (const [name, constr] of Object.entries(calc.constructors) as [string, any][]) {
    if (constr.returnType !== 'formula') continue;
    if (name === 'atom') continue; // Skip atom constructor

    const prec = constr.annotations.prec;
    const precedence = typeof prec === 'object' ? prec.precedence : (prec || 100);

    result.push({
      name,
      ascii: constr.annotations.ascii || name,
      latex: constr.annotations.latex || constr.annotations.ascii || name,
      polarity: calc.polarity[name] || 'unknown',
      category: constr.annotations.category,
      precedence,
      arity: constr.argTypes.length
    });
  }

  // Sort by category then precedence
  result.sort((a, b) => {
    if (a.category !== b.category) {
      return (a.category || '').localeCompare(b.category || '');
    }
    return (a.precedence || 0) - (b.precedence || 0);
  });

  return result;
}

/**
 * Get all inference rules with metadata, grouped by category
 */
export function getRulesGrouped(): Record<string, RuleInfo[]> {
  ensureInitialized();
  const calc = browser.getCalculus();
  const groups: Record<string, RuleInfo[]> = {
    'Identity': [],
    'Multiplicatives': [],
    'Additives': [],
    'Exponentials': [],
    'Structural': []
  };

  for (const [name, rule] of Object.entries(calc.rules) as [string, any][]) {
    // Determine category based on rule name
    let category = 'Other';
    if (name === 'id' || name === 'Id') {
      category = 'Identity';
    } else if (name.includes('tensor') || name.includes('loli') || name.includes('one')) {
      category = 'Multiplicatives';
    } else if (name.includes('with') || name.includes('plus')) {
      category = 'Additives';
    } else if (name.includes('bang') || name.includes('promotion') || name.includes('dereliction') || name.includes('absorption') || name.includes('copy')) {
      category = 'Exponentials';
    } else if (rule.structural) {
      category = 'Structural';
    }

    if (!groups[category]) {
      groups[category] = [];
    }

    groups[category].push({
      name,
      pretty: rule.pretty || name,
      numPremises: rule.numPremises || 0,
      invertible: calc.invertible[name] ?? rule.invertible,
      structural: rule.structural || false,
      category
    });
  }

  // Remove empty groups
  for (const key of Object.keys(groups)) {
    if (groups[key].length === 0) {
      delete groups[key];
    }
  }

  return groups;
}

/**
 * Get BNF-style grammar productions
 */
export function getBNFGrammar(): BNFProduction[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  const productions: BNFProduction[] = [];

  // Group constructors by return type
  const byType: Record<string, any[]> = {};

  for (const [name, constr] of Object.entries(calc.constructors) as [string, any][]) {
    const rt = constr.returnType;
    if (!byType[rt]) byType[rt] = [];
    byType[rt].push({ name, ...constr });
  }

  // Generate BNF for formula type
  if (byType['formula']) {
    const alternatives: string[] = [];

    for (const constr of byType['formula']) {
      const ascii = constr.annotations.ascii || constr.name;
      if (constr.argTypes.length === 0) {
        // Nullary: just the symbol
        alternatives.push(ascii);
      } else if (constr.argTypes.length === 1) {
        // Unary prefix
        alternatives.push(ascii.replace('_', 'A'));
      } else if (constr.argTypes.length === 2) {
        // Binary
        alternatives.push(ascii.replace('_', 'A').replace('_', 'B'));
      }
    }

    // Add atom
    alternatives.push('p, q, r, ...');

    productions.push({
      lhs: 'Formula',
      alternatives
    });
  }

  // Generate BNF for sequent
  if (byType['sequent']) {
    productions.push({
      lhs: 'Sequent',
      alternatives: ['Γ ; Δ ⊢ A']
    });
  }

  return productions;
}

/**
 * Get polarity information
 */
export function getPolarityInfo(): Array<{ name: string; polarity: string }> {
  ensureInitialized();
  const calc = browser.getCalculus();
  const result: Array<{ name: string; polarity: string }> = [];

  for (const [name, pol] of Object.entries(calc.polarity) as [string, string][]) {
    result.push({ name, polarity: pol });
  }

  return result;
}

/**
 * Get metavariable conventions from directives
 */
export function getMetavarConventions(): Array<{ pattern: string; meaning: string; example: string }> {
  ensureInitialized();
  const calc = browser.getCalculus();
  const directives = calc.directives;

  if (!directives?.metavars) {
    // Default conventions
    return [
      { pattern: 'A, B, C', meaning: 'Formula metavariable', example: 'A -o B' },
      { pattern: 'Γ, Δ', meaning: 'Context (multiset of formulas)', example: 'Γ, A ⊢ B' },
      { pattern: 'G, D', meaning: 'Structure metavariable', example: 'G ; D ⊢ C' },
      { pattern: 'p, q, r', meaning: 'Atomic proposition', example: 'p ⊢ p' },
    ];
  }

  return directives.metavars.map((mv: any) => ({
    pattern: mv.examples || mv.prefix,
    meaning: `${mv.type} metavariable`,
    example: mv.examples || ''
  }));
}

/**
 * Get sort names (base types) from the calculus
 */
export function getSortNames(): string[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  return Object.keys(calc.baseTypes || {});
}

/**
 * Render a rule to LaTeX for display
 */
export function renderRuleToLatex(ruleName: string): { conclusion: string; premises: string[] } | null {
  ensureInitialized();
  const calc = browser.getCalculus();
  const rule = calc.rules[ruleName];

  if (!rule) return null;

  // For v2, rules are stored as AST - we need to render them
  // This is a simplified version - rules in v2 are complex term structures
  // For now, return the pretty name
  return {
    conclusion: rule.pretty || ruleName,
    premises: Array(rule.numPremises).fill('...')
  };
}

/**
 * Get the raw bundle data (for advanced use)
 */
export function getBundle() {
  ensureInitialized();
  return illBundle;
}

/**
 * Get all rules from the bundle
 */
export function getAllRules(): Record<string, any> {
  ensureInitialized();
  const calc = browser.getCalculus();
  return calc.rules || {};
}

/**
 * Check if a rule exists
 */
export function hasRule(ruleName: string): boolean {
  ensureInitialized();
  const calc = browser.getCalculus();
  return ruleName in (calc.rules || {});
}

// ============================================================================
// Manual Proof API (for ManualProof.tsx)
// ============================================================================

export interface V2Sequent {
  linear: Formula[];
  cartesian: Formula[];
  succedent: Formula;
}

export interface V2ProofNode {
  conclusion: V2Sequent;
  premisses: V2ProofNode[];
  rule: string | null;
  proven: boolean;
}

export interface V2ApplicableRule {
  name: string;
  position: 'L' | 'R';
  index?: number;
  formula?: Formula;
  invertible: boolean;
}

/**
 * Parse sequent string into v2 sequent
 */
export function parseSequentV2(input: string): V2Sequent {
  ensureInitialized();
  return browser.parseSequent(input);
}

/**
 * Create initial proof tree from a sequent
 */
export function createProofTreeV2(seq: V2Sequent): V2ProofNode {
  return {
    conclusion: seq,
    premisses: [],
    rule: null,
    proven: false
  };
}

/**
 * Check if proof tree is complete
 */
export function isProofCompleteV2(pt: V2ProofNode): boolean {
  if (!pt.proven && pt.rule === null) return false;
  if (pt.premisses.length === 0 && pt.rule !== null) return true;
  return pt.premisses.every(p => isProofCompleteV2(p));
}

/**
 * Get applicable rules for a sequent (simplified version for UI)
 */
export function getApplicableRulesV2(seq: V2Sequent): V2ApplicableRule[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  const rules: V2ApplicableRule[] = [];

  // Check right rules (based on succedent connective)
  const succTag = seq.succedent?.tag;
  if (succTag && succTag !== 'atom' && succTag !== 'freevar') {
    const ruleName = `${succTag}_r`;
    if (calc.rules[ruleName]) {
      rules.push({
        name: ruleName,
        position: 'R',
        formula: seq.succedent,
        invertible: calc.invertible?.[ruleName] ?? false
      });
    }
    // Check alternatives like with_r1, with_r2
    for (const alt of ['1', '2']) {
      const altName = `${succTag}_r${alt}`;
      if (calc.rules[altName]) {
        rules.push({
          name: altName,
          position: 'R',
          formula: seq.succedent,
          invertible: calc.invertible?.[altName] ?? false
        });
      }
    }
  }

  // Check for identity (atom matching)
  if (seq.succedent?.tag === 'atom' || seq.succedent?.tag === 'freevar') {
    for (let i = 0; i < (seq.linear?.length || 0); i++) {
      const f = seq.linear[i];
      if (f?.tag === seq.succedent?.tag &&
          f?.children?.[0] === seq.succedent?.children?.[0]) {
        rules.push({
          name: 'id',
          position: 'L',
          index: i,
          formula: f,
          invertible: true
        });
        break;
      }
    }
  }

  // Check left rules (based on context formula connectives)
  for (let i = 0; i < (seq.linear?.length || 0); i++) {
    const f = seq.linear[i];
    const tag = f?.tag;
    if (tag && tag !== 'atom' && tag !== 'freevar') {
      const ruleName = `${tag}_l`;
      if (calc.rules[ruleName]) {
        rules.push({
          name: ruleName,
          position: 'L',
          index: i,
          formula: f,
          invertible: calc.invertible?.[ruleName] ?? false
        });
      }
      // Check alternatives
      for (const alt of ['1', '2']) {
        const altName = `${tag}_l${alt}`;
        if (calc.rules[altName]) {
          rules.push({
            name: altName,
            position: 'L',
            index: i,
            formula: f,
            invertible: calc.invertible?.[altName] ?? false
          });
        }
      }
    }
  }

  return rules;
}

/**
 * Auto-prove a sequent (using v2 prover)
 */
export async function autoProveV2(seq: V2Sequent): Promise<{ success: boolean; proofTree?: V2ProofNode }> {
  ensureInitialized();

  const prover = browser.createProver(browser.getCalculus());
  const result = prover.prove(seq, { maxDepth: 50 });

  if (!result.success) {
    return { success: false };
  }

  const convertTree = (pt: any): V2ProofNode => ({
    conclusion: pt.conclusion,
    premisses: (pt.premisses || []).map(convertTree),
    rule: pt.rule || 'id',
    proven: pt.proven
  });

  return {
    success: true,
    proofTree: result.proofTree ? convertTree(result.proofTree) : undefined
  };
}

/**
 * Get the Seq module from browser for advanced operations
 */
export function getSeqModule() {
  ensureInitialized();
  return browser.Seq;
}

/**
 * Get the full browser module for advanced operations
 */
export function getBrowserModule() {
  ensureInitialized();
  return browser;
}
