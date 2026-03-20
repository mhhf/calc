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
 * The FFI-enhanced variant (provePersistentWithFFI) lives in opt/ffi.js.
 */

const Store = require('../../kernel/store');
const { getPredicateHead, collectExternalFreevars, proverBoundExternals } = require('../../kernel/ast');
const { matchIndexed, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed } = require('../../kernel/substitute');
const ffi = require('../ffi');

const _TAG_METAVAR = Store.TAG.metavar;

// ── Backward proof cache ────────────────────────────────────────────
// For deterministic predicates with known mode (input/output args),
// cache (pred, input_args...) → output_values.
// Soundness: sound iff persistent context is monotonically growing.
// MUST be cleared at start of each run/explore call.

const _backwardCache = new Map();
let _bwCacheProbeId = 0;
function clearBackwardCache() { _backwardCache.clear(); _bwCacheProbeId = 0; }
Store.onClear(clearBackwardCache);

/**
 * Try to resolve a persistent goal via the backward proof cache.
 *
 * @returns {Object|null|undefined}
 *   - undefined: not cacheable or cache miss (prove normally)
 *   - null: cached failure
 *   - { outputs, term }: cached success
 */
function _tryBackwardCache(goal, slots, theta, calc, wantTerm, canonicalize) {
  const head = getPredicateHead(goal);
  if (!head) return undefined;

  const pm = ffi.parsedModes[head];
  if (!pm) return undefined;

  const arity = Store.arity(goal);
  if (arity === 0) return undefined;

  const outputPositions = [];
  const keyChildren = [];
  for (let i = 0; i < pm.length && i < arity; i++) {
    if (pm[i] === '+') {
      const argH = Store.child(goal, i);
      if (Store.isTerm(argH) && Store.tagId(argH) === _TAG_METAVAR) return undefined;
      keyChildren.push(argH);
    } else if (pm[i] === '-') {
      outputPositions.push(i);
    }
  }
  if (outputPositions.length === 0) return undefined;
  const key = Store.put(head, keyChildren);

  const cached = _backwardCache.get(key);
  if (cached !== undefined) {
    if (cached === null) return null;
    const outputs = cached.outputs || cached;
    const term = cached.term;
    if (wantTerm && !term) {
      // Fall through to cache miss to re-prove with buildTerm
    } else {
      for (let oi = 0; oi < outputPositions.length; oi++) {
        const argHash = Store.child(goal, outputPositions[oi]);
        if (Store.isTerm(argHash) && Store.tagId(argHash) === _TAG_METAVAR) {
          const slot = slots[argHash];
          if (slot !== undefined) theta[slot] = outputs[oi];
        } else {
          if (argHash !== outputs[oi]) return null;
        }
      }
      return { outputs, term };
    }
  }

  // Cache miss — probe with fresh metavars
  const probeArgs = new Array(arity);
  const probeMetavars = [];
  for (let i = 0; i < arity; i++) probeArgs[i] = Store.child(goal, i);
  for (const oi of outputPositions) {
    const mv = Store.put('metavar', [`bwc_${_bwCacheProbeId++}`]);
    probeArgs[oi] = mv;
    probeMetavars.push(mv);
  }
  const probeGoal = Store.put(head, probeArgs);

  const backward = require('../backchain');
  const result = backward.backchain(probeGoal, calc.clauses, calc.definitions, {
    maxDepth: 20000,
    index: calc.backchainIndex,
    buildTerm: !!wantTerm,
    allBuckets: true,
    useFFI: false
  });

  if (!result.success) {
    _backwardCache.set(key, null);
    return null;
  }

  const thetaMap = new Map(result.theta);
  const outputValues = [];
  for (const mv of probeMetavars) {
    let val = thetaMap.get(mv);
    if (val === undefined) {
      const mvName = Store.child(mv, 0);
      for (const [k, v] of thetaMap) {
        if (Store.isTerm(k) && Store.tagId(k) === _TAG_METAVAR && Store.child(k, 0) === mvName) {
          val = v; break;
        }
      }
    }
    outputValues.push(val !== undefined && canonicalize ? canonicalize(val) : val);
  }

  const cacheEntry = wantTerm ? { outputs: outputValues, term: result.term } : outputValues;
  _backwardCache.set(key, cacheEntry);

  for (let oi = 0; oi < outputPositions.length; oi++) {
    const argHash = Store.child(goal, outputPositions[oi]);
    if (Store.isTerm(argHash) && Store.tagId(argHash) === _TAG_METAVAR) {
      const slot = slots[argHash];
      if (slot !== undefined) theta[slot] = outputValues[oi];
    } else {
      if (argHash !== outputValues[oi]) return null;
    }
  }
  return { outputs: outputValues, term: result.term };
}

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
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function provePersistentNaive(patterns, startIdx, theta, slots, state, calc, evidenceOut, matchOpts) {
  const canonicalize = matchOpts && matchOpts.canonicalize;
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
    if (calc && calc.clauses) {
      const wantTerm = !!evidenceOut;
      const cacheResult = _tryBackwardCache(goal, slots, theta, calc, wantTerm, canonicalize);
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
        useFFI: false
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

// ── Compiled persistent step execution ──────────────────────────────

const _ffiIsGround = ffi.convert.isGround;
const _ffiParsedModes = ffi.parsedModes;
const _psArgs = [0, 0, 0, 0];
for (const key in _ffiParsedModes) {
  if (_ffiParsedModes[key].length > 4) {
    throw new Error(`FFI '${key}' arity ${_ffiParsedModes[key].length} exceeds _psArgs buffer size 4`);
  }
}

/**
 * Execute a compiled persistent step spec against theta.
 *
 * @param {Object} spec - { ffiFn, argSpecs, arity, multiModal, _slots }
 * @param {Array} theta - Metavar bindings
 * @returns {boolean|null} true (proved), false (definitive failure), null (needs generic fallback)
 */
function executePersistentStep(spec, theta) {
  for (let i = 0; i < spec.arity; i++) {
    const as = spec.argSpecs[i];
    if (as.literal !== undefined) {
      _psArgs[i] = as.literal;
    } else {
      const val = theta[as.slot];
      _psArgs[i] = val !== undefined ? val : as.freevar;
      if (!spec.multiModal && as.isInput &&
          (val === undefined || !_ffiIsGround(val))) {
        return null;
      }
    }
  }

  const result = spec.ffiFn(_psArgs);
  if (result && result.success) {
    const ft = result.theta;
    const specSlots = spec._slots;
    for (let fi = 0; fi < ft.length; fi++) {
      const s = specSlots[ft[fi][0]];
      if (s !== undefined) theta[s] = ft[fi][1];
    }
    return true;
  }
  if (result && !result.success && !result.reason) return false;
  return null;
}

module.exports = {
  provePersistentNaive,
  clearBackwardCache,
  executePersistentStep,
};
