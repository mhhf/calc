/**
 * Type definitions for lib/node.js
 * AST node representation with format-polymorphic rendering
 */

import type { Rule, FormatStyle } from './calc';

/** Options for Node.toString() */
export interface ToStringOptions {
  style?: FormatStyle;
  brackets?: boolean;
  rules?: Record<number, Rule>;
}

/** Options for polarity checking */
export interface PolarityOptions {
  positive: string[];
  negative: string[];
}

/** Tree node structure returned by Node.toTree() */
export interface TreeNode {
  head: Record<string, string>;
  children: TreeNode[];
}

/** Attributes for tree formatting */
export type TreeAttr = 'ascii' | 'constr' | 'formula' | 'name' | 'precedence' | 'ownprecedence' | 'childprecedence';

/** Options for Node.toTree() */
export interface ToTreeOptions {
  node: Node;
  rules: Record<number, Rule>;
  attrs: TreeAttr[];
}

/** Options for Node.isBrackets() */
export interface IsBracketsOptions {
  style: FormatStyle;
  i: number;
  node: Node;
  rules: Record<number, Rule>;
}

/** Node class - AST representation */
export interface Node {
  id: number;
  vals: (Node | string)[];

  /** Create a deep copy of this node */
  copy(): Node;

  /** Convert to string with specified format style */
  toString(options?: ToStringOptions): string;

  /** Focus this structure (convert term to focused term) */
  doFocus(): void;

  /** Unfocus this structure (convert focused term back to term) */
  doUnfocus(): void;

  /** Check if this is an atomic formula (variable or atomic proposition) */
  isAtomic(options?: PolarityOptions): boolean;

  /** Get the polarity of this node */
  getPolarity(options?: PolarityOptions): '' | 'positive' | 'negative';

  /** Check if this is a term type (Structure_Term_Formula or Structure_Focused_Term_Formula) */
  isTermType(): boolean;

  /** Check if this node has negative polarity */
  isNegative(options?: PolarityOptions): boolean;

  /** Check if this node has positive polarity */
  isPositive(options?: PolarityOptions): boolean;

  /** Check if this is a lax modality */
  isLax(): boolean;

  /** Check if this is a focused formula */
  isFocus(): boolean;

  /** Check if this is a monad */
  isMonad(): boolean;

  /** Get free variables in this node (currently unimplemented) */
  getFreeVariables(): void;
}

/** Node constructor */
export interface NodeConstructor {
  new (id: number, vals: (Node | string)[]): Node;
  (id: number, vals: (Node | string)[]): Node;

  /** Convert node to string with options */
  toString(node: Node | string, options: ToStringOptions): string;

  /** Check if brackets should be drawn for child i */
  isBrackets(options: IsBracketsOptions): boolean;

  /** Format node as tree table string */
  formatTree(options: ToTreeOptions): string;

  /** Convert node to tree structure */
  toTree(options: ToTreeOptions): TreeNode;
}

declare const Node: NodeConstructor;
export default Node;
export { Node };
