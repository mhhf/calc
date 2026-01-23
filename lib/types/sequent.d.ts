/**
 * Type definitions for lib/sequent.js
 * Logical sequent structure with linear and persistent contexts
 */

import type { Node, ToStringOptions } from './node';
import type { Rule } from './calc';

/** Substitution: array of [variable, replacement] pairs */
export type Theta = [Node, Node][];

/** Resource entry in linear context */
export interface LinearResource {
  num: number;
  val: Node;
}

/** Linear context: mapping from hash ID to resource */
export type LinearContext = Record<string, LinearResource>;

/** Persistent context: mapping from hash ID to node */
export type PersistentContext = Record<string, Node>;

/** Constructor parameters for Sequent */
export interface SequentParams {
  persistent_ctx?: PersistentContext;
  linear_ctx?: LinearContext;
  succedent?: Node;
  focus?: Node;
}

/** Options for getAtoms */
export interface GetAtomsOptions {
  rules: Record<number, Rule>;
}

/** Sequent class - represents a logical sequent */
export interface Sequent {
  persistent_ctx: PersistentContext;
  linear_ctx: LinearContext;
  succedent: Node;
  focus: Node | null;
  focusPosition: 'L' | 'R' | null;
  focusId: string | null;

  /** Apply substitution to this sequent */
  substitute(theta: Theta): Sequent;

  /** Convert to string representation */
  toString(options?: ToStringOptions & { highlight?: Node[] }): string;

  /** Update focus position based on current context */
  ffocus(): void;
}

/** Result of renameUnique */
export interface RenameUniqueResult {
  seq: Sequent;
  theta: Theta;
}

/** Result of renameUniqueArray */
export interface RenameUniqueArrayResult {
  seqs: Sequent[];
  theta: Theta;
}

/** Sequent constructor and static methods */
export interface SequentConstructor {
  new (params?: SequentParams): Sequent;
  (params?: SequentParams): Sequent;

  /** Variable index counter for unique renaming */
  varIndex: number;

  /** Rename variables in multiple sequents to ensure uniqueness */
  renameUniqueArray(seqs: Sequent[]): RenameUniqueArrayResult;

  /** Rename variables in a sequent to ensure uniqueness */
  renameUnique(seq: Sequent): RenameUniqueResult;

  /** Get all free variables in a sequent */
  getFreeVariables(seq: Sequent): Node[];

  /** Create a deep copy of a sequent */
  copy(seq: Sequent): Sequent;

  /** Remove structural variables from linear context */
  remove_structural_variables(seq: Sequent): void;

  /** Check if sequent is stable */
  isStable(seq: Sequent, options: unknown): void;

  /** Add AST to linear context */
  add_to_linear_ctx(seq: Sequent, ast: Node, num?: number): void;

  /** Add multiple resources to antecedent */
  add_to_antecedent_bulk(seq: Sequent, delta: LinearContext): void;

  /** Remove resources from antecedent */
  remove_from_antecedent(seq: Sequent, delta: LinearContext): LinearContext | false;

  /** Construct comparison options for unification */
  constructCompareOptions<T>(r1: T[], r2: T[]): [T, T][][];

  /** Blur (unfocus) a sequent */
  blur(seq: Sequent): void;

  /** Convert parsed tree to sequent */
  fromTree(seq: Node): Sequent;

  /** Get atomic formulas from sequent */
  getAtoms(seq: Sequent, options: GetAtomsOptions): string[];
}

declare const Sequent: SequentConstructor;
export default Sequent;
export { Sequent };
