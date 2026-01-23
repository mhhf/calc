/**
 * Type definitions for lib/helper.js
 * Tree formatting utilities and visualization helpers
 */

import type { TreeNode } from './node';

/** Database row for formatting */
export type DbRow = Record<string, string>;

/**
 * Format database rows as ASCII table
 */
export function formatDb(db: DbRow[], attrs: string[]): string;

/**
 * Format tree as clean string representation
 */
export function formatCleanTree(tree: TreeNode, loc: string): string;

/**
 * Convert tree to GraphViz DOT format
 */
export function tree2dot(tree: TreeNode, heads: string[]): string;

/**
 * Fold tree in preorder, building clean table
 */
export function foldCleanPreorder(
  tree: TreeNode,
  loc: string,
  prefix?: string,
  last?: boolean
): [string, string?][];

/**
 * Fold tree in preorder, building table with heads
 */
export function foldPreorder(
  tree: TreeNode,
  loc: string,
  prefix?: string,
  last?: boolean
): DbRow[];

declare const helper: {
  formatDb: typeof formatDb;
  formatCleanTree: typeof formatCleanTree;
  tree2dot: typeof tree2dot;
  foldCleanPreorder: typeof foldCleanPreorder;
  foldPreorder: typeof foldPreorder;
};

export default helper;
