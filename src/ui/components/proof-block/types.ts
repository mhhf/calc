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

/** One of the five supported layouts; persists in localStorage per-browser. */
export type ProofLayout = 'bussproofs' | 'gentzen' | 'tactic' | 'indented' | 'flipped';

export const PROOF_LAYOUTS: ReadonlyArray<{ id: ProofLayout; label: string }> = [
  { id: 'bussproofs', label: 'Bussproofs' },
  { id: 'gentzen',    label: 'Gentzen' },
  { id: 'tactic',     label: 'Tactic' },
  { id: 'indented',   label: 'Indented' },
  { id: 'flipped',    label: 'Flipped' },
];
