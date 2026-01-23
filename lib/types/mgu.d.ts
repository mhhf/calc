/**
 * Type definitions for lib/mgu.js
 * Most General Unifier algorithm
 */

import type { Node } from './node';
import type { Theta } from './sequent';

/** Unification goal: pair of nodes to unify */
export type UnificationGoal = [Node, Node];

/**
 * Compute the most general unifier for a set of goals
 * @param goals Array of node pairs to unify
 * @returns Substitution theta if unification succeeds, false otherwise
 */
declare function mgu(goals: UnificationGoal[]): Theta | false;

export default mgu;
export { mgu };
