/**
 * State Operations — shared helpers for forward.js and symexec.js.
 *
 * Factored from duplicated consume/produce/skip-preserved logic.
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');

// Preserved optimization — re-exported from opt/preserved.js
const { buildPreservedSkip, filterPreserved } = require('./opt/preserved');

/**
 * Consume linear facts from state.
 * @param {FactSet} linear - linear FactSet (mutated)
 * @param {{ [hash: string]: number }} consumed - facts to consume
 * @param {Arena|null} arena - undo arena (null for clone-based)
 */
function consumeLinear(linear, consumed, arena) {
  for (const hStr in consumed) {
    const hash = Number(hStr);
    const count = consumed[hStr];
    const tagIdx = Store.tagId(hash);
    for (let c = 0; c < count; c++) {
      linear.remove(tagIdx, hash, arena);
    }
  }
}

/**
 * Produce linear facts into state, with preserved-skip and compiled substitution.
 * @param {FactSet} linear - linear FactSet (mutated)
 * @param {number[]} patterns - consequent linear pattern hashes
 * @param {Array} theta - substitution bindings
 * @param {Object} slots - metavar slot mapping
 * @param {Object|null} rule - compiled rule (for preserved + compiled sub)
 * @param {boolean} optimized - whether to use preserved-skip
 * @param {Arena|null} arena - undo arena
 */
function produceLinear(linear, patterns, theta, slots, rule, optimized, arena) {
  const cLinear = rule && rule.compiledConseqLinear;
  let skipCount = null;
  if (optimized && rule && rule.preserved && rule.preserved.length > 0) {
    skipCount = {};
    for (const h of rule.preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  }
  const skipUsed = {};

  for (let i = 0; i < patterns.length; i++) {
    const pattern = patterns[i];
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    let h;
    const recipe = cLinear && cLinear[i];
    if (recipe && recipe.compiled) {
      h = recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
    } else {
      h = subApplyIdx(pattern, theta, slots);
    }
    linear.insert(Store.tagId(h), h, arena);
  }
}

/**
 * Produce persistent facts into state (dedup: skip if already present).
 * @param {FactSet} persistent - persistent FactSet (mutated)
 * @param {number[]} patterns - consequent persistent pattern hashes
 * @param {Array} theta - substitution bindings
 * @param {Object} slots - metavar slot mapping
 * @param {Object|null} rule - compiled rule (for compiled sub)
 * @param {Arena|null} arena - undo arena
 */
function producePersistent(persistent, patterns, theta, slots, rule, arena) {
  const cPersistent = rule && rule.compiledConseqPersistent;
  for (let i = 0; i < patterns.length; i++) {
    const pattern = patterns[i];
    let h;
    const recipe = cPersistent && cPersistent[i];
    if (recipe && recipe.compiled) {
      h = recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
    } else {
      h = subApplyIdx(pattern, theta, slots);
    }
    const tagIdx = Store.tagId(h);
    if (!persistent.has(tagIdx, h)) {
      persistent.insert(tagIdx, h, arena);
    }
  }
}

module.exports = {
  buildPreservedSkip,
  filterPreserved,
  consumeLinear,
  produceLinear,
  producePersistent,
};
