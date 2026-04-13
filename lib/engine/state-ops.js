/**
 * State Operations — shared helpers for forward.js and explore.js.
 *
 * Factored from duplicated consume/produce/skip-preserved logic.
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');

/**
 * Apply substitution to a consequent pattern using compiled recipe if available.
 * Falls back to subApplyIdx when no recipe exists.
 */
function applyCompiledSub(pattern, index, theta, slots, compiledList, _subApplyIdx) {
  const recipe = compiledList && compiledList[index];
  if (recipe && recipe.compiled) {
    return recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
  }
  return _subApplyIdx(pattern, theta, slots);
}

// Preserved optimization — re-exported from preserved.js
const { buildPreservedSkip, filterPreserved } = require('./preserved');

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
// Pooled objects for preserved-skip counting (avoid per-call allocation)
const _poolSkipCount = Object.create(null);
const _poolSkipUsed = Object.create(null);
let _poolSkipKeys = [];

function produceLinear(linear, patterns, theta, slots, rule, optimized, arena) {
  const cLinear = rule && rule.compiledConseqLinear;
  let hasSkip = false;
  if (optimized && rule && rule.preserved && rule.preserved.length > 0) {
    hasSkip = true;
    for (const h of rule.preserved) _poolSkipCount[h] = (_poolSkipCount[h] || 0) + 1;
    _poolSkipKeys = rule.preserved;
  }

  for (let i = 0; i < patterns.length; i++) {
    const pattern = patterns[i];
    if (hasSkip && _poolSkipCount[pattern] > 0 &&
        (_poolSkipUsed[pattern] || 0) < _poolSkipCount[pattern]) {
      _poolSkipUsed[pattern] = (_poolSkipUsed[pattern] || 0) + 1;
      continue;
    }
    const h = applyCompiledSub(pattern, i, theta, slots, cLinear, subApplyIdx);
    linear.insert(Store.tagId(h), h, arena);
  }

  // Reset pooled objects
  if (hasSkip) {
    for (const h of _poolSkipKeys) {
      _poolSkipCount[h] = 0;
      _poolSkipUsed[h] = 0;
    }
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
    const h = applyCompiledSub(patterns[i], i, theta, slots, cPersistent, subApplyIdx);
    const tagIdx = Store.tagId(h);
    if (!persistent.has(tagIdx, h)) {
      persistent.insert(tagIdx, h, arena);
    }
  }
}

/**
 * Mutate state in-place: consume linear facts, produce new facts.
 * Records undo entries in linArena/perArena for backtracking.
 */
function mutateState(state, consumed, theta, linearPatterns, persistentPatterns, slots, rule, linArena, perArena) {
  consumeLinear(state.linear, consumed, linArena);
  produceLinear(state.linear, linearPatterns, theta, slots, rule, !!rule, linArena);
  producePersistent(state.persistent, persistentPatterns, theta, slots, rule, perArena);
}

module.exports = {
  buildPreservedSkip,
  filterPreserved,
  consumeLinear,
  produceLinear,
  producePersistent,
  mutateState,
};
