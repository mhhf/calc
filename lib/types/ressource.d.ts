/**
 * Type definitions for lib/ressource.js
 * Resource/variable extraction from nodes
 */

import type { Node } from './node';

/** Ressource class - utility for resource extraction */
export interface RessourceStatic {
  /**
   * Get all free variables in a resource/node
   * @param r The node to extract variables from
   * @returns Array of variable nodes
   */
  getFreeVariables(r: Node): Node[];
}

declare const Ressource: RessourceStatic;
export default Ressource;
export { Ressource };
