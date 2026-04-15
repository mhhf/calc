/**
 * Prediction optimization (Opt_H) — threaded code dispatch.
 *
 * For virtual fingerprint configs, predicts the next rule from the
 * substitution: theta[nextPointerSlot] → new PC → bytecode lookup → rule.
 * Skips findAllMatches when prediction succeeds and no lolis present.
 */

const Store = require('../../kernel/store');
const { discIndex } = require('../match');

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
function predictNext(rules, fpConfig, state, opts = {}) {
  if (!opts.binToInt) return null;  // No domain-specific numeric eval — prediction disabled
  const _binToInt = opts.binToInt;
  if (!fpConfig || fpConfig.type !== 'virtual') return null;

  const dIdx = discIndex(rules);
  let bytecodeElems = null;
  let bytecodeTrieRoot = null;

  const arrayTagId = Store.TAG[fpConfig.arrayPred];
  if (arrayTagId !== undefined) {
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length === 1) {
      const arrayHash = Store.child(arrayGroup[0], 0);
      bytecodeElems = Store.getArrayElements(arrayHash);
      if (!bytecodeElems) {
        // Trie format — use O(log N) navigation per lookup
        bytecodeTrieRoot = arrayHash;
      }
    }
  }

  // Use cached arrlit elements from bytecodeToTrie for O(1) prediction.
  // The state._bytecodeElems cache is set during normalizeQuery when
  // arrlit is converted to trie — keeps O(1) prediction hot path.
  if (!bytecodeElems && state._bytecodeElems) {
    bytecodeElems = state._bytecodeElems;
  }

  if (!bytecodeElems && !bytecodeTrieRoot) return null;

  // Trie fallback for states without cached elements
  const _trieNav = bytecodeTrieRoot ? (opts.trieNav || null) : null;

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
    if (idx === null || idx < 0n) return null;

    let opcode;
    if (bytecodeElems) {
      if (idx >= BigInt(bytecodeElems.length)) return null;
      opcode = bytecodeElems[Number(idx)];
    } else {
      opcode = _trieNav(bytecodeTrieRoot, idx);
      if (opcode === null) return null;
    }

    const candidates = dIdx[opcode];
    if (!candidates || candidates.length !== 1) return null;
    return candidates[0];
  };
}

module.exports = {
  predictNext,
};
