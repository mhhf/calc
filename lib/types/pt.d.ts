/**
 * Type definitions for lib/pt.js
 * Proof tree structure and rendering
 */

import type { Sequent, LinearContext } from './sequent';
import type { Node, TreeNode } from './node';

/** Options for PT.toString() */
export interface PTToStringOptions {
  style?: 'html' | 'latex' | 'ascii';
}

/** Constructor parameters for PT */
export interface PTParams {
  premisses?: PT[];
  conclusion: Sequent | Node;
  type?: string;
}

/** Proof tree head in tree representation */
export interface PTTreeHead {
  conclusion: string;
  type: string;
  delta_out: string;
  delta_in: string;
  proven: string;
}

/** Proof tree structure returned by toTree() */
export interface PTTree {
  head: PTTreeHead;
  children: PTTree[];
}

/** Proof Tree class */
export interface PT {
  premisses: PT[];
  conclusion: Sequent;
  type: string;
  delta_in: LinearContext;
  delta_out: LinearContext;
  proven: boolean;

  /** Convert to tree structure for visualization */
  toTree(): PTTree;

  /** Convert to string in specified format */
  toString(options?: PTToStringOptions): string;
}

/** PT constructor and static methods */
export interface PTConstructor {
  new (params: PTParams): PT;
  (params: PTParams): PT;

  /** Create PT from array of nodes (first is conclusion, rest are premisses) */
  fromNodeArray(array: Node[]): PT;
}

declare const PT: PTConstructor;
export default PT;
export { PT };
