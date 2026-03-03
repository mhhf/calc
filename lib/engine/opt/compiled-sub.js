/**
 * Compiled substitution optimization.
 *
 * When rules have precompiled substitution recipes (compiledConseqLinear,
 * compiledConseqPersistent), uses subCompiled for fast instantiation
 * instead of the generic subApplyIdx path.
 */

const { subCompiled } = require('../../kernel/substitute');

/**
 * Apply substitution to a consequent pattern using compiled recipe if available.
 * Falls back to subApplyIdx when no recipe exists.
 *
 * @param {number} pattern - Consequent pattern hash
 * @param {number} index - Position in pattern list
 * @param {Array} theta - Substitution bindings
 * @param {Object} slots - Metavar slot mapping
 * @param {Object|null} compiledList - Compiled recipes (compiledConseqLinear or compiledConseqPersistent)
 * @param {Function} subApplyIdx - Fallback substitution function
 * @returns {number} Instantiated hash
 */
function applyCompiledSub(pattern, index, theta, slots, compiledList, subApplyIdx) {
  const recipe = compiledList && compiledList[index];
  if (recipe && recipe.compiled) {
    return recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
  }
  return subApplyIdx(pattern, theta, slots);
}

module.exports = { applyCompiledSub };
