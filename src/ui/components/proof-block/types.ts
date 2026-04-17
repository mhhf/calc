/**
 * TypeScript types for `proof-tree/v1` serialization format
 * (produced by `lib/prover/serialize-tree.js`). Keep this file in lockstep
 * with the JS serializer's docstring.
 */

export interface FormulaAST {
  tag: string;
  name?: string;        // atom / freevar / metavar
  value?: string;       // strlit (string), binlit / bound / evar (decimal string)
  codepoint?: number;   // charlit — raw uint32
  elements?: (string | null)[]; // arrlit — pool refs
  args?: (string | null)[];     // generic term children — pool refs
  extras?: Array<
    | { kind: 'string'; value: string }
    | { kind: 'int'; value: string }
    | { kind: 'array'; elements: (string | null)[] }
    | { kind: 'other'; value: string }
  >;
}

export interface Sequent {
  /** Calculus-native context names (linear, cartesian, …) → pool refs. */
  contexts: Record<string, (string | null)[]>;
  succedent: string | null;
}

export interface ProofNode {
  id: string;
  sequent: Sequent;
  rule: string | null;
  premises: ProofNode[];
  proven: boolean;
  /** True when this node is a lazy-load stub: its real premises are
   *  held on the server. The viewer renders a fetch button in place
   *  of the normal fold-stub; click routes through POST /api/proof/subtree. */
  elided?: boolean;
}

export interface ProofTreeV1 {
  format: 'proof-tree/v1';
  calculus: string;
  profile: string;
  profileHash?: string;
  formulas: Record<string, FormulaAST>;
  root: ProofNode;
  meta?: Record<string, unknown>;
}

// ── forward-trace/v1 (symex / exec) ─────────────────────────────────────
// Produced by lib/prover/serialize-trace.js. Tree skeleton + leaves; per-leaf
// traces fetch lazily via POST /api/proof/leaf-trace.

export type LeafStatus =
  | 'STOP' | 'REVERT' | 'INVALID' | 'RUNNING' | 'STUCK' | 'NO_STATE';

export interface ForwardLeafSummary {
  leafIndex: number;
  id: string;
  status: LeafStatus;
  stepCount: number;
  state: {
    linear: Array<[string, number]>;
    persistent: string[];
  };
}

export type ForwardNode =
  | { id: string; idx: number; type: 'branch'; children: Array<{ rule: string; choice?: unknown; child: ForwardNode }>; elided?: boolean }
  | { id: string; idx: number; type: 'leaf'; leafIndex: number; status: LeafStatus }
  | { id: string; idx: number; type: 'bound' | 'cycle' | 'memo' | 'dead' };

export interface ForwardTraceV1 {
  format: 'forward-trace/v1';
  mode: 'symex' | 'exec';
  calculus: string;
  profile: string;
  formulas: Record<string, FormulaAST>;
  queryVars: string[];
  initial: { linear: Array<[string, number]>; persistent: string[] };
  stats: {
    totalNodes: number;
    branchCount: number;
    leafCount: number;
    maxDepth: number;
    totalTraceSteps: number;
    maxTraceLen: number;
  };
  tree: ForwardNode;
  leaves: ForwardLeafSummary[];
}

export interface TraceStep {
  step: number;
  ruleName: string;
  consumed: Array<[string, number]>;
}

export interface ForwardLeafDetail {
  leafIndex: number;
  id: string;
  status: LeafStatus;
  stepCount: number;
  state: {
    linear: Array<[string, number]>;
    persistent: string[];
  };
  trace: TraceStep[];
  formulas: Record<string, FormulaAST>;
}

/** One of the five supported layouts; persists in localStorage per-browser. */
export type ProofLayout = 'bussproofs' | 'gentzen' | 'tactic' | 'indented' | 'flipped';

export const PROOF_LAYOUTS: ReadonlyArray<{ id: ProofLayout; label: string }> = [
  { id: 'bussproofs', label: 'Bussproofs' },
  { id: 'gentzen',    label: 'Gentzen' },
  { id: 'tactic',     label: 'Tactic' },
  { id: 'indented',   label: 'Indented' },
  { id: 'flipped',    label: 'Flipped' },
];
