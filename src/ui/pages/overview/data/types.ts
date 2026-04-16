/**
 * Architecture overview data model (TODO_0205).
 *
 * Single source of truth for every component in CALC. Each component is
 * tagged once on four independent axes (trust, specificity, pipeline, mode),
 * and every view is a projection onto this same graph. Same name + color
 * everywhere → cross-view component navigation works by id lookup.
 *
 * Adding a new component: extend `COMPONENTS` in components.ts only.
 * Never hand-curate lists per view; always project from this model.
 */

/** Soundness impact of a bug at this layer (Trust Stack axis). */
export type Trust = 'kernel' | 'infrastructure' | 'optimization' | 'ui';

/**
 * How domain-specific is this code (Specificity Tree axis).
 *   framework  — calculus-agnostic (Earley, store, prover core)
 *   logic      — tied to a specific logic (ILL)
 *   theory     — tied to an equational theory (binlit, strlit, sha3)
 *   program    — tied to a program semantics (EVM)
 *   instance   — tied to a specific program instance (multisig contract)
 */
export type Specificity = 'framework' | 'logic' | 'theory' | 'program' | 'instance';

/** When does this code run (Pipeline axis). A component may span stages. */
export type Stage =
  | 'define'   // .calc/.rules source authored
  | 'parse'    // text → AST
  | 'compile'  // AST → internal IR (rule compilation, clause compilation)
  | 'execute'  // run (forward/backward/explore)
  | 'certify'  // ZK witness generation + verification
  | 'present'; // UI / docs / debug display

/** How are proofs produced (Mode axis). A component may support multiple. */
export type Mode =
  | 'backward'       // Andreoli focusing, SLD
  | 'forward'        // committed-choice multiset rewriting
  | 'symbolic'       // exhaustive DFS exploration
  | 'certification'; // ZK proof → Plonky3

/** Which deep-dive page documents this component (for cross-view links). */
export type DeepDive =
  | 'prover'
  | 'engine'
  | 'compilation'
  | 'optimization'
  | 'zk'
  | 'parser'
  | 'applications';

/** Canonical architecture component. */
export interface Component {
  /** Unique id, e.g. 'prover.kernel'. Used for cross-view linking. */
  id: string;
  /** Display name (short). */
  name: string;
  /** One-line summary (rendered in tooltips, atlas rows). */
  summary: string;
  /** Primary file path(s), relative to repo root. */
  files: string[];
  /** Primary tags. */
  trust: Trust;
  specificity: Specificity;
  stages: Stage[];
  modes: Mode[];
  /** Which deep dive explains this component. */
  deepDive: DeepDive;
  /** Optional longer description (markdown-lite). */
  details?: string;
  /** Optional group/cluster id for layer visualisations. */
  cluster?: string;
}

/**
 * A named vertical layer within a stack (for Trust Stack columns and
 * deep-dive layer diagrams). Layer bands reference components by id.
 */
export interface Layer {
  id: string;
  name: string;
  /** Stack this layer belongs to, e.g. 'prover' | 'engine.core' | 'engine.lnl'. */
  stack: string;
  /** 0 = top of stack (most specific). Higher numbers = lower in stack. */
  order: number;
  /** Component ids in this layer. */
  componentIds: string[];
  /** Trust inherited by all components in this layer. */
  trust: Trust;
  /** One-line role description. */
  role: string;
}

/** Directed relationship between two components or layers. */
export interface Connection {
  from: string;
  to: string;
  kind:
    | 'imports'   // hard dep
    | 'wraps'     // optimization wrapper around lower layer
    | 'injects'   // composition-root wiring
    | 'bridges'   // mode transition (e.g. monad bridge)
    | 'feeds';    // pipeline flow
  label?: string;
}

/** Deep-dive page metadata (for landing cards + sub-nav). */
export interface DeepDiveMeta {
  id: DeepDive;
  slug: string;
  title: string;
  oneLiner: string;
  blurb: string;
  /** Icon character (single glyph, no emoji). */
  glyph: string;
}

/** Axis-view page metadata (Trust, Specificity, Pipeline, Atlas). */
export interface ViewMeta {
  id: 'trust' | 'specificity' | 'pipeline' | 'atlas';
  slug: string;
  title: string;
  question: string; // "What if this code is wrong?"
  blurb: string;
  glyph: string;
}
