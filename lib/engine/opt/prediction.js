/**
 * Prediction optimization (Opt_H) — threaded code dispatch.
 *
 * For virtual fingerprint configs, predicts the next rule from the
 * substitution: theta[nextPointerSlot] → new pointer → array lookup → rule.
 * Skips findAllMatches when prediction succeeds and no dynamic rules present.
 *
 * Generic over the discriminator array: fpConfig.arrayPred names the fact
 * holding an array-literal program (ILL's EVM bytecode is one instance).
 */

import Store from '../../kernel/store.js';
import { discIndex } from '../match.js';
/**
 * Create a prediction function from rules and fingerprint config.
 * Returns a closure (m) → rule|null, or null if prediction not applicable.
 *
 * The closure captures arrElems and discIndex as closure variables
 * for V8-friendly constant access in the hot loop.
 *
 * @param {Object[]} rules - Compiled rules
 * @param {Object|null} fpConfig - Fingerprint config
 * @param {Object} state - Initial state (for discriminator-array lookup)
 * @returns {Function|null} (m) → predicted rule or null
 */
function predictNext(rules, fpConfig, state, opts = {}) {
  if (!opts.evalNumeric) return null;  // No domain numeric eval — prediction disabled
  const _evalNumeric = opts.evalNumeric;
  if (!fpConfig || fpConfig.type !== 'virtual') return null;

  const dIdx = discIndex(rules);
  let arrElems = null;
  let trieRoot = null;

  const arrayTagId = Store.TAG[fpConfig.arrayPred];
  if (arrayTagId !== undefined) {
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length === 1) {
      const arrayHash = Store.child(arrayGroup[0], 0);
      arrElems = Store.getArrayElements(arrayHash);
      if (!arrElems) {
        // Trie format — use O(log N) navigation per lookup
        trieRoot = arrayHash;
      }
    }
  }

  // Generic cross-layer hook: state._fpArrayElems caches the discriminator
  // array's elements for O(1) prediction when the fact itself holds a trie.
  // Any calculus loader converting arrlit → trie may populate it (ILL's
  // EVM normalizer does, calculus/ill/lib/bytecode-normalize.js).
  if (!arrElems && state._fpArrayElems) {
    arrElems = state._fpArrayElems;
  }

  if (!arrElems && !trieRoot) return null;

  // Trie fallback for states without cached elements
  const _trieNav = trieRoot ? (opts.trieNav || null) : null;

  // Return closure that captures arrElems/discIndex directly
  return function predictNext(m) {
    const rule = m.rule;
    if (rule.nextPointerSlot === undefined) return null;

    let nextPtr;
    if (rule.nextPointerSlot === -1) {
      nextPtr = rule.nextPointerValue;
    } else {
      nextPtr = m.theta[rule.nextPointerSlot];
      if (nextPtr === undefined) return null;
    }

    const idx = _evalNumeric(nextPtr);
    if (idx === null || idx < 0n) return null;

    let elem;
    if (arrElems) {
      if (idx >= BigInt(arrElems.length)) return null;
      elem = arrElems[Number(idx)];
    } else {
      elem = _trieNav(trieRoot, idx);
      if (elem === null) return null;
    }

    const candidates = dIdx[elem];
    if (!candidates || candidates.length !== 1) return null;
    return candidates[0];
  };
}

export { predictNext };
export default { predictNext };
