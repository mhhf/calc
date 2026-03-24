/**
 * CALC Terminal State → VMTest Result Extractor
 *
 * Extracts comparable results from CALC's terminal state after
 * forward execution, for comparison against VMTest expected values.
 */

const Store = require('../../../lib/kernel/store');
const { binToInt } = require('../../../lib/engine/ill/ffi/convert');

/**
 * Extract all facts of a given tag from state.linear.
 * Returns array of { hash, children: hash[] }.
 *
 * Handles both predicate-tagged facts (tag = tagName, tagId >= PRED_BOUNDARY)
 * and nullary atoms (tag = 'atom', name = tagName, arity = 0).
 */
function factsOfTag(state, tagName) {
  const tagId = Store.TAG[tagName];
  const results = [];
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (state.linear[hStr] <= 0) continue;

    // Predicate-tagged fact
    if (tagId !== undefined && Store.tagId(h) === tagId) {
      const arity = Store.arity(h);
      const children = [];
      for (let i = 0; i < arity; i++) {
        children.push(Store.child(h, i));
      }
      results.push({ hash: h, children });
      continue;
    }

    // Nullary atom: tag='atom', child(0) is the name string
    if (Store.tag(h) === 'atom' && Store.child(h, 0) === tagName) {
      results.push({ hash: h, children: [] });
    }
  }
  return results;
}

/**
 * Extract termination status from terminal state.
 * Returns 'stop' | 'return' | 'revert' | 'invalid' | 'running'
 *
 * EVM: falling off the end of bytecode is equivalent to STOP.
 * CALC: the engine quiesces with pc pointing past bytecode — no `stop` fact.
 * We detect this by checking if pc >= bytecode length.
 */
function extractTermination(state) {
  for (const tag of ['stop', 'return', 'revert', 'invalid']) {
    if (factsOfTag(state, tag).length > 0) return tag;
  }

  // Check for implicit stop: pc >= bytecode length
  const pcFacts = factsOfTag(state, 'pc');
  const bcFacts = factsOfTag(state, 'bytecode');
  if (pcFacts.length > 0 && bcFacts.length > 0) {
    const pcVal = binToInt(pcFacts[0].children[0]);
    const arrHash = bcFacts[0].children[0];
    // Handle both arrlit and trie-backed bytecode
    const elems = Store.getArrayElements(arrHash);
    if (pcVal !== null && elems && pcVal >= BigInt(elems.length)) {
      return 'stop'; // implicit stop: fell off end of arrlit bytecode
    }
    // Trie-backed bytecode: check if arr_get(trie, pc, ?) fails
    if (pcVal !== null && !elems && Store.tagId(arrHash) >= Store.PRED_BOUNDARY) {
      const { arr_get } = require('../../../lib/engine/ill/ffi/array');
      const idxHash = require('../../../lib/engine/ill/ffi/convert').intToBin(pcVal);
      const mv = Store.put('metavar', ['_extract_v']);
      if (!arr_get([arrHash, idxHash, mv]).success) {
        return 'stop'; // implicit stop: fell off end of trie bytecode
      }
    }
  }

  return 'running';
}

/**
 * Extract remaining gas as BigInt.
 */
function extractGas(state) {
  const gasFacts = factsOfTag(state, 'gas');
  if (gasFacts.length === 0) return null;
  return binToInt(gasFacts[0].children[0]);
}

/**
 * Extract storage as Map<bigint, bigint>.
 * Filters out zero values (EVM convention: zero = empty).
 */
function extractStorage(state) {
  const storageFacts = factsOfTag(state, 'storage');
  const result = new Map();
  for (const f of storageFacts) {
    const key = binToInt(f.children[0]);
    const val = binToInt(f.children[1]);
    if (key !== null && val !== null && val !== 0n) {
      result.set(key, val);
    }
  }
  return result;
}

/**
 * Extract stack as array of BigInt (top first).
 */
function extractStack(state) {
  const stackFacts = factsOfTag(state, 'stack');
  if (stackFacts.length === 0) return [];
  const arrHash = stackFacts[0].children[0];
  const elems = Store.getArrayElements(arrHash);
  if (elems) {
    return elems.map(h => binToInt(h)).filter(v => v !== null);
  }
  // Walk acons/ae structure
  return walkList(arrHash);
}

/**
 * Walk a list structure (acons/ae) and return elements as BigInt[].
 */
function walkList(h) {
  const result = [];
  let current = h;
  while (true) {
    const tag = Store.tag(current);
    if (tag === 'atom' || tag === 'arrlit') {
      // ae or empty arrlit = end of list
      break;
    }
    if (tag === 'acons') {
      const val = binToInt(Store.child(current, 0));
      if (val !== null) result.push(val);
      current = Store.child(current, 1);
    } else {
      break;
    }
  }
  return result;
}

/**
 * Extract full result for VMTest comparison.
 */
function extractResult(state) {
  return {
    termination: extractTermination(state),
    gas: extractGas(state),
    storage: extractStorage(state),
    stack: extractStack(state),
  };
}

/**
 * Parse VMTest expected storage from fixture post data.
 * @param {Object} storageObj - { "0x00": "0xff", ... }
 * @returns {Map<bigint, bigint>}
 */
function parseExpectedStorage(storageObj) {
  const result = new Map();
  if (!storageObj) return result;
  for (const [key, val] of Object.entries(storageObj)) {
    const k = BigInt(key);
    const v = BigInt(val);
    if (v !== 0n) result.set(k, v);
  }
  return result;
}

module.exports = { extractResult, extractTermination, extractGas, extractStorage, extractStack, parseExpectedStorage };
