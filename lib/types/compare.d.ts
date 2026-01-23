/**
 * Type definitions for lib/compare.js
 * Formula comparison and unification
 */

import type { Node } from './node';
import type { Theta } from './sequent';

/** Options for comparison */
export interface CompareOptions {
  debug?: boolean;
}

/**
 * Compare two nodes and compute substitution if they match
 * @param n1 First node
 * @param n2 Second node
 * @param options Comparison options
 * @returns Substitution theta if nodes match, false otherwise
 */
declare function compare(n1: Node, n2: Node, options?: CompareOptions): Theta | false;

export default compare;
export { compare };
