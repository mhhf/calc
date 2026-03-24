/**
 * Persistent goal proving for LNL forward chaining.
 *
 * Layer: LNL (Linear-Non-Linear)
 *
 * Persistent antecedents (!P) are non-consumable — they must be proved,
 * not matched-and-consumed like linear patterns. Resolution strategies:
 *   1. State lookup: check if fact exists in state.persistent
 *   2. Backward cache: memoized clause resolution (noFFI mode)
 *   3. Clause backchaining: SLD-style resolution via backchain.js
 *
 * The FFI-enhanced variant (provePersistentWithFFI) and compiled persistent
 * step execution (executePersistentStep) live in opt/ffi.js.
 *
 * No ILL-specific imports — ffiParsedModes for backward cache comes
 * from matchOpts, set by the composition layer (forward.js/explore.js).
 */

const Store = require('../../kernel/store');
const { getPredicateHead, collectExternalFreevars, proverBoundExternals } = require('../../kernel/ast');
const { matchIndexed, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed } = require('../../kernel/substitute');
const { tryBackwardCache, clearBackwardCache } = require('../backward-cache');

// ── Persistent proving ──────────────────────────────────────────────

/**
 * Prove persistent patterns via state lookup → backward cache → clause resolution.
 * No FFI — adversarially sound (all proofs via clause resolution).
 *
 * @param {number[]} patterns - Persistent antecedent pattern hashes
 * @param {number} startIdx - Index to start proving from
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, definitions, backchainIndex }
 * @param {Array|null} evidenceOut - Evidence collector (null if not collecting)
 * @param {Object} matchOpts - Match options (canonicalize, ffiParsedModes)
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function provePersistentNaive(patterns, startIdx, theta, slots, state, calc, evidenceOut, matchOpts) {
  const canonicalize = matchOpts && matchOpts.canonicalize;
  const ffiParsedModes = matchOpts && matchOpts.ffiParsedModes;
  let idx = startIdx;
  while (idx < patterns.length) {
    const goal = applyIndexed(patterns[idx], theta, slots);

    // 1. State lookup
    {
      const pattern = patterns[idx];
      const pPred = getPredicateHead(pattern);
      if (pPred) {
        const pTagId = Store.TAG[pPred];
        const effectiveTagId = (pTagId !== undefined && pTagId >= Store.PRED_BOUNDARY)
          ? pTagId : Store.TAG.atom;
        if (effectiveTagId !== undefined && state.persistent.groupLen(effectiveTagId) > 0) {
          const persGroup = state.persistent.group(effectiveTagId);
          let matchedFact = null;
          for (let gi = 0; gi < persGroup.length; gi++) {
            const hn = persGroup[gi];
            const savedUndo = undoSave();
            if (matchIndexed(pattern, hn, theta, slots)) {
              matchedFact = hn;
              undoDiscard(savedUndo);
              break;
            }
            undoRestore(theta, savedUndo);
          }
          if (matchedFact !== null) {
            if (evidenceOut) evidenceOut.push({ goal, method: 'state', fact: matchedFact });
            idx++;
            continue;
          }
        }
      }
    }

    // 2. Backward proof cache
    if (calc && calc.clauses && ffiParsedModes) {
      const wantTerm = !!evidenceOut;
      const cacheResult = tryBackwardCache(goal, slots, theta, calc, wantTerm, canonicalize, ffiParsedModes);
      if (cacheResult !== undefined) {
        if (cacheResult === null) break;
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: { success: true }, term: cacheResult.term });
        idx++;
        continue;
      }
    }

    // 3. Clause resolution (deep, no FFI)
    if (calc && calc.clauses && calc.definitions) {
      const externals = collectExternalFreevars(goal, slots);
      const backward = require('../backchain');
      const wantTerm = !!evidenceOut;
      const result = backward.backchain(goal, calc.clauses, calc.definitions, {
        maxDepth: 20000,
        index: calc.backchainIndex,
        buildTerm: wantTerm,
        allBuckets: true,
      });
      if (result.success) {
        if (externals && proverBoundExternals(result.theta, externals)) break;
        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) {
            theta[slot] = canonicalize ? canonicalize(rt[ri][1]) : rt[ri][1];
          }
        }
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: result, term: result.term });
        idx++;
        continue;
      }
    }
    break;
  }
  return idx;
}

module.exports = {
  provePersistentNaive,
  clearBackwardCache,
};
