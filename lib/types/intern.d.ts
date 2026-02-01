/**
 * Intern - Convert between Node AST and content-addressed Terms
 */

import { Store, ScopedStore } from './store';
import { Term } from './term';
import { Node } from './node';

/**
 * Intern a Node AST into the store, returning a Term
 */
export function internNode(store: Store | ScopedStore, node: Node | string): Term;

/**
 * Extern a Term back to a Node AST
 */
export function externNode(
  store: Store | ScopedStore,
  termOrHash: Term | bigint,
  NodeClass: typeof Node
): Node | string;

/**
 * Intern a sequent-like tree structure
 */
export function internSequent(
  store: Store | ScopedStore,
  sequentNode: Node
): { hash: bigint; term: Term };

/**
 * Check if two nodes are equal via content addressing
 */
export function nodesEqual(
  store: Store | ScopedStore,
  node1: Node | string,
  node2: Node | string
): boolean;

/**
 * Get all subterms of a node (for subformula property)
 */
export function getSubterms(
  store: Store | ScopedStore,
  node: Node | string
): Set<bigint>;

/**
 * Count nodes in a term (for complexity analysis)
 */
export function countNodes(
  store: Store | ScopedStore,
  node: Node | string
): number;
