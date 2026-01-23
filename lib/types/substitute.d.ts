/**
 * Type definitions for lib/substitute.js
 * Variable substitution in AST nodes
 */

import type { Node } from './node';

/**
 * Substitute a variable with a value in a node
 * @param node The node to perform substitution in
 * @param key The variable to replace
 * @param val The value to substitute
 * @returns The node with substitution applied (mutates and returns input)
 */
declare function substitute(node: Node | string, key: Node, val: Node): Node | string;

export default substitute;
export { substitute };
