/**
 * Prediction optimization (Opt_H) — threaded code dispatch.
 *
 * For virtual fingerprint configs, predicts the next rule from the
 * substitution: theta[nextPointerSlot] → new PC → bytecode lookup → rule.
 * Skips findAllMatches when prediction succeeds and no lolis present.
 */

const Store = require('../../kernel/store');
const { buildDiscriminatorIndex } = require('../match');
const ffi = require('../ill/ffi');

const _binToInt = ffi.convert.binToInt;

/**
 * Create a prediction function from rules and fingerprint config.
 * Returns a closure (m) → rule|null, or null if prediction not applicable.
 *
 * The closure captures bytecodeElems and discIndex as closure variables
 * for V8-friendly constant access in the hot loop.
 *
 * @param {Object[]} rules - Compiled rules
 * @param {Object|null} fpConfig - Fingerprint config
 * @param {Object} state - Initial state (for bytecode lookup)
 * @returns {Function|null} (m) → predicted rule or null
 */
function createPredictNext(rules, fpConfig, state) {
  if (!fpConfig || fpConfig.type !== 'virtual') return null;

  const discIndex = buildDiscriminatorIndex(rules);
  let bytecodeElems = null;

  const arrayTagId = Store.TAG[fpConfig.arrayPred];
  if (arrayTagId !== undefined) {
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length === 1) {
      bytecodeElems = Store.getArrayElements(Store.child(arrayGroup[0], 0));
    }
  }

  if (!bytecodeElems) return null;

  // Return closure that captures bytecodeElems/discIndex directly
  return function predictNext(m) {
    const rule = m.rule;
    if (rule.nextPointerSlot === undefined) return null;

    let newPC;
    if (rule.nextPointerSlot === -1) {
      newPC = rule.nextPointerValue;
    } else {
      newPC = m.theta[rule.nextPointerSlot];
      if (newPC === undefined) return null;
    }

    const idx = _binToInt(newPC);
    if (idx === null || idx < 0n || idx >= BigInt(bytecodeElems.length)) return null;
    const opcode = bytecodeElems[Number(idx)];

    const candidates = discIndex[opcode];
    if (!candidates || candidates.length !== 1) return null;
    return candidates[0];
  };
}

module.exports = {
  createPredictNext,
};
