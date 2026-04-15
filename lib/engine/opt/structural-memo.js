/**
 * Structural memoization — coarse-grained state deduplication.
 *
 * Computes a "control hash" from PC value + stack depth. States with
 * the same control hash execute the same instruction sequence, allowing
 * subtree reuse when branching is purely symbolic.
 *
 * Sound when: (a) all oplus branching is on symbolic values, and
 * (b) the constraint solver's pruning doesn't depend on state differences
 * excluded from this hash.
 */

const Store = require('../../kernel/store');

const _emptyI32 = new Int32Array(0);

/**
 * Compute a control hash for structural memoization.
 * Hashes only: PC value + stack arrlit length (stack depth).
 *
 * @param {Object} state - FactSet-based State object
 * @returns {number} 32-bit unsigned hash
 */
function controlHash(state, controlOpts) {
  const pcPred = (controlOpts && controlOpts.pcPred) || 'pc';
  const stackPred = (controlOpts && controlOpts.stackPred) || 'stack';
  const pcTagId = Store.TAG[pcPred];
  const stackTagId = Store.TAG[stackPred];
  const pcGroup = pcTagId !== undefined ? state.linear.group(pcTagId) : _emptyI32;
  const stackGroup = stackTagId !== undefined ? state.linear.group(stackTagId) : _emptyI32;
  const pcVal = pcGroup.length > 0 ? Store.child(pcGroup[0], 0) : 0;
  let stackLen = 0;
  if (stackGroup.length > 0) {
    const arrHash = Store.child(stackGroup[0], 0);
    const elems = Store.getArrayElements(arrHash);
    stackLen = elems ? elems.length : 0;
  }
  return (Math.imul(pcVal | 0, 2654435761) ^ Math.imul(stackLen | 0, 2246822519)) >>> 0;
}

/**
 * Create a memo context for structural memoization.
 * @returns {{ globalControl: Map, boundCount: number }}
 */
function createMemoCtx() {
  return { globalControl: new Map(), boundCount: 0 };
}

/**
 * Record a control hash in the memo if the subtree was fully explored
 * (no bound nodes added since boundBefore).
 *
 * @param {number} controlHash - Control hash to record
 * @param {number} boundBefore - boundCount before exploring subtree
 * @param {Object} memoCtx - { globalControl, boundCount }
 */
function recordMemo(controlHash, boundBefore, memoCtx) {
  if (memoCtx.boundCount === boundBefore) {
    memoCtx.globalControl.set(controlHash, true);
  }
}

module.exports = {
  controlHash,
  createMemoCtx,
  recordMemo,
};
