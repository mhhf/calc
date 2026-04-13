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
const { isGround } = require('../pattern-utils');
const { tryCompiledClause } = require('../opt/compiled-clauses');

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
  const onProveFail = (matchOpts && matchOpts.onProveFail) || null;
  const onProveSuccess = (matchOpts && matchOpts.onProveSuccess) || null;
  const backchainUseFFI = matchOpts && matchOpts.backchainUseFFI !== undefined
    ? matchOpts.backchainUseFFI : true;
  let idx = startIdx;
  while (idx < patterns.length) {
    const goal = applyIndexed(patterns[idx], theta, slots);

    // Detect non-ground inputs: check if any '+' mode arg is non-ground.
    // This tells profiling where rewrite rules could substitute for FFI.
    let _isGround = true;
    if (onProveSuccess && ffiParsedModes) {
      const head = getPredicateHead(goal);
      const modes = head && ffiParsedModes[head];
      if (modes) {
        const arity = Store.arity(goal);
        for (let i = 0; i < arity && i < modes.length; i++) {
          if (modes[i] === '+' && !isGround(Store.child(goal, i))) {
            _isGround = false;
            break;
          }
        }
      }
    }

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
            if (onProveSuccess) onProveSuccess(goal, 'state', { ground: _isGround, hasFfi: false });
            idx++;
            continue;
          }
        }
      }
    }

    // 1.5. Compiled clause dispatch (zero-subgoal clauses)
    // Skip when evidence is requested — compiled dispatch produces no proof terms,
    // so we fall through to backward cache/chainer which can build them.
    if (calc && calc.clauseDispatch && !evidenceOut) {
      const ccResult = tryCompiledClause(
        calc.clauseDispatch, goal, slots, theta,
        canonicalize || null,
        calc.theoryLookup || null,
        ffiParsedModes || null
      );
      if (ccResult === true) {
        if (onProveSuccess) onProveSuccess(goal, 'compiled', { ground: _isGround, hasFfi: false });
        idx++;
        continue;
      }
    }

    // 2. Backward proof cache
    if (calc && calc.clauses && ffiParsedModes) {
      const wantTerm = !!evidenceOut;
      const cacheResult = tryBackwardCache(goal, slots, theta, calc, wantTerm, canonicalize, ffiParsedModes, backchainUseFFI);
      if (cacheResult !== undefined) {
        if (cacheResult === null) {
          if (onProveFail) onProveFail(goal, 'cached_failure');
          break;
        }
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: { success: true }, term: cacheResult.term });
        if (onProveSuccess) onProveSuccess(goal, 'cache', { ground: _isGround, hasFfi: false });
        idx++;
        continue;
      }
    }

    // 3. Clause resolution (respects backchainUseFFI toggle)
    if (calc && calc.clauses && calc.definitions) {
      const externals = collectExternalFreevars(goal, slots);
      const backward = require('../backchain');
      const wantTerm = !!evidenceOut;
      const result = backward.backchain(goal, calc.clauses, calc.definitions, {
        maxDepth: 20000,
        index: calc.backchainIndex,
        buildTerm: wantTerm,
        allBuckets: true,
        useFFI: backchainUseFFI,
      });
      if (result.success) {
        if (externals && proverBoundExternals(result.theta, externals)) {
          if (onProveFail) onProveFail(goal, 'external_binding', { ground: _isGround, hasFfi: false });
          break;
        }
        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) {
            theta[slot] = canonicalize ? canonicalize(rt[ri][1]) : rt[ri][1];
          }
        }
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: result, term: result.term });
        if (onProveSuccess) onProveSuccess(goal, 'clause', { ground: _isGround, hasFfi: false });
        idx++;
        continue;
      }
    }
    if (onProveFail) onProveFail(goal, 'exhausted', { ground: _isGround, hasFfi: false });
    break;
  }
  return idx;
}

module.exports = {
  provePersistentNaive,
  clearBackwardCache,
};
