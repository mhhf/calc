/**
 * Type definitions for lib/proofstate.js
 * Proof search engine with forward/backward chaining
 */

import type { PT } from './pt';
import type { Sequent, Theta, LinearContext } from './sequent';
import type { PolarityOptions } from './node';

/** Rule getter function */
export type GetRuleFn = (ruleName: string) => Sequent[];

/** Options for proof search */
export interface ProofSearchOptions extends PolarityOptions {
  rules: Record<string, Sequent[]>;
  bwd: string[];
  fwd?: Record<string, unknown>;
  getRule: GetRuleFn;
  affine?: boolean;
  debug?: boolean;
  debug_type?: 'live' | 'tree';
  mode?: 'proof';
}

/** Debug information structure */
export interface DebugInfo {
  goal?: string;
  goal_free_vars?: string;
  technique?: string;
  rule?: string[];
  bwd_theta?: string[];
  theta?: string[];
  theta_native?: string[];
  theta_propagated?: string[];
  num_actions?: number;
  success?: boolean;
  premisses?: string[];
  result?: Sequent;
  ptp?: string[];
  [key: string]: unknown;
}

/** Debug tree structure */
export interface DebugTree {
  head: DebugInfo;
  children: DebugTree[];
}

/** Result of proof search */
export interface ProofSearchResult {
  delta_out: LinearContext;
  theta: Theta;
  success: boolean;
  debug: DebugTree;
}

/** Proofstate class - proof search engine */
export interface ProofstateStatic {
  /**
   * Get invertable rule for focused proof search
   * Returns 'R' for right-invertable, id for left-invertable, or false
   */
  getInvertableRule(pt: PT, options: PolarityOptions): string | false;

  /**
   * Automatic proof search
   */
  auto(pt: PT, options: ProofSearchOptions): ProofSearchResult;

  /**
   * Get potential rules for focused formula
   */
  getPotRules(pt: PT, id: string, options: ProofSearchOptions): string[];

  /**
   * Apply a rule to the proof tree
   */
  apply(pt: PT, ruleName: string, id: string, rule: Sequent[]): { success: boolean } | false;

  /**
   * Try identity rule for negative atom
   */
  tryIdNeg(pt: PT): { theta: Theta; delta_out: LinearContext } | false;

  /**
   * Try identity rule for positive atom
   */
  tryIdPos(pt: PT): { theta: Theta; delta_out: LinearContext } | false;

  /**
   * Focus on a formula
   */
  focus(pt: PT, id: string): { success: boolean };

  /**
   * Blur (unfocus) a focused formula
   */
  blur(pt: PT, pos?: 'L' | 'R'): { success: boolean };

  /**
   * Copy a multiset (linear context)
   */
  copyMS(ms: LinearContext, except?: string[]): LinearContext;
}

declare const Proofstate: ProofstateStatic;
export default Proofstate;
export { Proofstate };
