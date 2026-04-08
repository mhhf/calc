/**
 * ILL-specific configuration for the generic compose pipeline.
 *
 * The compose pipeline (lib/engine/compose.js) is calculus-agnostic — all
 * domain-specific knowledge (predicate names, number representation) is
 * injected via configuration objects. This module provides the ILL defaults.
 *
 * Chain configs describe threading predicates whose chains can be algebraically
 * collapsed at compile time. SROA config describes array access patterns that
 * can be scalarized into individual slots.
 */

'use strict';

const { binToInt, intToBin } = require('./ffi/convert');

/**
 * ILL chain fusion configs.
 *
 * Each descriptor identifies a predicate family where output→input threading
 * forms chains that can be collapsed:
 *   - inc(X,Y) * inc(Y,Z) → plus(X, 2, Z)          (unary step)
 *   - checked_sub(G,3,G2) * checked_sub(G2,5,G3) → checked_sub(G,8,G3)  (binary accumulate)
 *   - plus(X,2,Y) * plus(Y,3,Z) → plus(X, 5, Z)    (binary accumulate)
 *
 * parseConstant/buildConstant handle the ILL binary number representation.
 */
const ILL_CHAIN_CONFIGS = [
  {
    pred: 'inc', inputArg: 0, outputArg: 1, constantArg: null,
    fusedPred: 'plus', fusedInputArg: 0, fusedConstantArg: 1, fusedOutputArg: 2,
    parseConstant: binToInt, buildConstant: intToBin,
  },
  {
    pred: 'checked_sub', inputArg: 0, outputArg: 2, constantArg: 1,
    fusedPred: 'checked_sub', fusedInputArg: 0, fusedConstantArg: 1, fusedOutputArg: 2,
    parseConstant: binToInt, buildConstant: intToBin,
  },
  {
    pred: 'plus', inputArg: 0, outputArg: 2, constantArg: 1,
    fusedPred: 'plus', fusedInputArg: 0, fusedConstantArg: 1, fusedOutputArg: 2,
    parseConstant: binToInt, buildConstant: intToBin,
  },
];

/**
 * ILL SROA (Scalar Replacement of Aggregates) config.
 *
 * Describes how array access predicates (arr_get/arr_set) relate to a linear
 * resource (stack) holding the array. parseIndex/buildIndex handle the ILL
 * binary number representation for array indices.
 */
const ILL_SROA_CONFIG = {
  arrayPreds: ['arr_get', 'arr_set'],
  resourcePred: 'stack',
  parseIndex: binToInt,
  buildIndex: intToBin,
};

module.exports = { ILL_CHAIN_CONFIGS, ILL_SROA_CONFIG };
