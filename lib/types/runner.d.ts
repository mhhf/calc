/**
 * Type definitions for lib/runner.js
 * Proof orchestration and saturation
 */

import type { PT } from './pt';
import type { Sequent } from './sequent';
import type { ProofSearchOptions } from './proofstate';

/** Configuration for chain */
export interface ChainConfig extends ProofSearchOptions {
  pt: PT;
}

/** Configuration for saturate */
export interface SaturateConfig extends ProofSearchOptions {
  seq: Sequent;
}

/**
 * Chain proof search on a proof tree
 */
export function chain(config: ChainConfig): unknown;

/**
 * Saturate a sequent using forward chaining
 */
export function saturate(config: SaturateConfig): unknown;

declare const runner: {
  chain: typeof chain;
  saturate: typeof saturate;
};

export default runner;
