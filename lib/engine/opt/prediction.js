/**
 * Prediction optimization (Opt_H) — threaded code dispatch.
 *
 * For virtual fingerprint configs, predicts the next rule from the
 * substitution: theta[nextPointerSlot] → new PC → bytecode lookup → rule.
 * Skips findAllMatches when prediction succeeds and no lolis present.
 */

const Store = require('../../kernel/store');
const { buildDiscriminatorIndex } = require('../match');
const ffi = require('../ffi');

const _binToInt = ffi.convert.binToInt;

/**
 * Create a prediction context from rules and fingerprint config.
 * Returns null if prediction is not applicable.
 *
 * @param {Object[]} rules - Compiled rules
 * @param {Object|null} fpConfig - Fingerprint config
 * @param {Object} state - Initial state (for bytecode lookup)
 * @returns {{ bytecodeElems: Uint32Array|null, discIndex: Object }|null}
 */
function createPredictionCtx(rules, fpConfig, state) {
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
  return { bytecodeElems, discIndex };
}

/**
 * Predict the next rule from a match result.
 *
 * @param {Object} m - Match result { rule, theta }
 * @param {Object} predCtx - Prediction context { bytecodeElems, discIndex }
 * @returns {Object|null} Predicted rule or null
 */
function predictNext(m, predCtx) {
  if (!predCtx || !predCtx.bytecodeElems) return null;
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
  if (idx === null || idx < 0n || idx >= BigInt(predCtx.bytecodeElems.length)) return null;
  const opcode = predCtx.bytecodeElems[Number(idx)];

  const candidates = predCtx.discIndex[opcode];
  if (!candidates || candidates.length !== 1) return null;
  return candidates[0];
}

module.exports = {
  createPredictionCtx,
  predictNext,
};
