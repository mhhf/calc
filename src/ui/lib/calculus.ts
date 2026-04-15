/**
 * Calculus API for UI
 *
 * Thin wrapper over lib/browser.js. Lazily initializes from the pre-bundled ILL spec.
 * Provides: parsing, rendering, calculus metadata, and low-level module access.
 * Proof logic lives in proofLogic.ts (not here).
 */

// @ts-ignore - CommonJS module
import * as browserModule from '../../../lib/browser.js';
// @ts-ignore - Generated JSON bundle
import illBundle from '../../../out/ill.json';

const browser = (browserModule as any).default || browserModule;

// Types
export interface Formula {
  tag: string;
  children: (Formula | string)[];
}

// Initialization
let initialized = false;

function ensureInitialized() {
  if (!initialized) {
    browser.initFromBundle(illBundle);
    initialized = true;
  }
}

// ============================================================================
// Parsing & Rendering
// ============================================================================

export function parseFormula(input: string): Formula {
  ensureInitialized();
  return browser.parseFormula(input);
}

export function parseSequent(input: string): any {
  ensureInitialized();
  return browser.parseSequent(input);
}

export function renderFormula(formula: any, format: 'ascii' | 'latex' = 'ascii'): string {
  ensureInitialized();
  try {
    return browser.render(formula, format);
  } catch (e) {
    console.error('renderFormula error:', e, 'formula:', formula, 'format:', format);
    throw e;
  }
}

export function renderSequent(seq: any, format: 'ascii' | 'latex' = 'ascii'): string {
  ensureInitialized();
  return browser.render(seq, format);
}

// ============================================================================
// Calculus Access
// ============================================================================

export function getCalculus() {
  ensureInitialized();
  return browser.getCalculus();
}

/**
 * Build AST tree data for visualization (Sandbox.tsx).
 */
export function buildASTTree(formula: Formula): any {
  if (!formula?.tag) return null;

  const node: any = {
    head: { constr: formula.tag, name: formula.tag },
    children: []
  };

  for (const child of formula.children) {
    if (typeof child === 'string') {
      node.children.push({
        head: { constr: 'leaf', name: child, ascii: child },
        children: []
      });
    } else if (child?.tag) {
      node.children.push(buildASTTree(child));
    }
  }

  return node;
}

// ============================================================================
// Calculus Metadata (for CalculusOverview.tsx, MetaOverview.tsx, CalculusHealth.tsx)
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

export function getCalculusName(): string {
  ensureInitialized();
  const calc = browser.getCalculus();
  return calc.name || 'Linear Logic';
}

export function getFormulaConnectives(): ConnectiveInfo[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  const result: ConnectiveInfo[] = [];

  for (const [name, constr] of Object.entries(calc.constructors) as [string, any][]) {
    if (constr.returnType !== 'formula') continue;
    if (name === 'atom') continue;

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

  result.sort((a, b) => {
    if (a.category !== b.category) {
      return (a.category || '').localeCompare(b.category || '');
    }
    return (a.precedence || 0) - (b.precedence || 0);
  });

  return result;
}

/** Look up connective category from constructor annotations (e.g. "multiplicative" → "Multiplicatives"). */
function getConnectiveCategory(connective: string): string | null {
  ensureInitialized();
  const calc = browser.getCalculus();
  const cat = calc?.constructors?.[connective]?.annotations?.category;
  if (!cat) return null;
  return cat.charAt(0).toUpperCase() + cat.slice(1) + 's';
}

/** Classify a rule into its logical category using descriptor metadata. */
export function getRuleCategory(ruleName: string, rule?: any): string {
  if (ruleName === 'id' || ruleName === 'Id') return 'Identity';
  if (ruleName === 'Focus_L' || ruleName === 'Focus_R') return 'Focus';
  const r = rule ?? browser.getCalculus()?.rules?.[ruleName];
  const connective = r?.descriptor?.connective;
  if (connective) {
    const cat = getConnectiveCategory(connective);
    if (cat) return cat;
  }
  if (r?.structural) return 'Structural';
  return 'Other';
}

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
    const category = getRuleCategory(name, rule);
    if (!groups[category]) groups[category] = [];
    groups[category].push({
      name,
      pretty: rule.pretty || name,
      numPremises: rule.numPremises || 0,
      invertible: calc.invertible[name] ?? rule.invertible,
      structural: rule.structural || false,
      category
    });
  }

  for (const key of Object.keys(groups)) {
    if (groups[key].length === 0) delete groups[key];
  }

  return groups;
}

export function getBNFGrammar(): BNFProduction[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  const productions: BNFProduction[] = [];

  const byType: Record<string, any[]> = {};
  for (const [name, constr] of Object.entries(calc.constructors) as [string, any][]) {
    const rt = constr.returnType;
    if (!byType[rt]) byType[rt] = [];
    byType[rt].push({ name, ...constr });
  }

  if (byType['formula']) {
    const alternatives: string[] = [];
    for (const constr of byType['formula']) {
      const ascii = constr.annotations.ascii || constr.name;
      if (constr.argTypes.length === 0) alternatives.push(ascii);
      else if (constr.argTypes.length === 1) alternatives.push(ascii.replace('_', 'A'));
      else if (constr.argTypes.length === 2) alternatives.push(ascii.replace('_', 'A').replace('_', 'B'));
    }
    alternatives.push('p, q, r, ...');
    productions.push({ lhs: 'Formula', alternatives });
  }

  if (byType['sequent']) {
    productions.push({ lhs: 'Sequent', alternatives: ['Γ ; Δ ⊢ A'] });
  }

  return productions;
}

export function getPolarityInfo(): Array<{ name: string; polarity: string }> {
  ensureInitialized();
  const calc = browser.getCalculus();
  return Object.entries(calc.polarity).map(([name, pol]) => ({ name, polarity: pol as string }));
}

export function getMetavarConventions(): Array<{ pattern: string; meaning: string; example: string }> {
  ensureInitialized();
  const calc = browser.getCalculus();
  const directives = calc.directives;

  if (!directives?.metavars) {
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

export function getSortNames(): string[] {
  ensureInitialized();
  const calc = browser.getCalculus();
  return Object.keys(calc.baseTypes || {});
}

export function getBundle() {
  ensureInitialized();
  return illBundle;
}

export function getAllRules(): Record<string, any> {
  ensureInitialized();
  const calc = browser.getCalculus();
  return calc.rules || {};
}

export function hasRule(ruleName: string): boolean {
  ensureInitialized();
  const calc = browser.getCalculus();
  return ruleName in (calc.rules || {});
}

// ============================================================================
// Low-level Module Access (for proofLogic.ts)
// ============================================================================

export function getSeqModule() {
  ensureInitialized();
  return browser.Seq;
}

export function getBrowserModule() {
  ensureInitialized();
  return browser;
}

export function getManualProofAPI() {
  ensureInitialized();
  return browser.getManualProofAPI();
}
