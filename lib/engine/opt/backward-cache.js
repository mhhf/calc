/**
 * Backward proof cache for persistent goal resolution.
 *
 * Layer: generic engine infrastructure (a cache, but consumed unconditionally
 * by forward.js/explore.js — it lives at the engine root, NOT in opt/,
 * because generic-layer files import it and the layer DAG forbids
 * generic → opt).
 *
 * For deterministic predicates with known mode (input/output args),
 * caches (pred, input_args...) → output_values.
 *
 * ## Soundness Argument
 *
 * The cache is sound under these conditions:
 *
 * 1. **Cleared at start of each run()/explore() call.** This is the primary
 *    invariant. The COMPOSITION ROOT (index.js exec/explore wrappers) and
 *    lib/timed settle call clearBWCache()
 *    before entering the main loop.
 *
 * 2. **Backchainer resolution depends only on the clause database (immutable
 *    within a run), NOT on persistent state.** The clause database is built
 *    once from .ill definitions and never changes. FFI functions are pure
 *    (same inputs → same outputs). Therefore cached results from backchaining
 *    are valid across all DFS paths.
 *
 * 3. **Cached successes remain valid on all paths.** A persistent goal proved
 *    by backchaining (FFI or clause resolution) will succeed identically on
 *    any DFS path because the clause database is path-independent.
 *
 * 4. **Cached failures are conservative.** A goal that failed backchaining
 *    with no state match will correctly fail on paths with fewer persistent
 *    facts. On paths with MORE persistent facts, the cached failure is stale
 *    (the goal might succeed via state lookup), but this only causes
 *    re-proving — slower but never unsound (no false positives).
 *
 * 5. **Arena undo does retract persistent facts on backtrack.** This means
 *    a state-lookup success cached on path A may be invalid on path B (which
 *    has fewer persistent facts). The cache avoids this by keying on input
 *    args only and storing backchain results, not state-lookup results.
 *    State lookup is always re-done fresh in provePersistent.
 *
 * Extracted from lnl/persistent.js for toggleability and testability.
 */

import Store from '../../kernel/store.js';
import { predHead } from '../../kernel/ast.js';
import { matchIndexed, undoSave, undoRestore, undoDiscard } from '../../kernel/unify.js';
import backward from '../backchain.js';
const _TAG_METAVAR = Store.TAG.metavar;

/**
 * Bind a goal's output positions to their cached/computed output values by
 * UNIFICATION (not assignment-or-exact-hash). A fused/SROA rule can carry a
 * partially-instantiated output pattern — e.g. `arr_set(A, I, V, acons(H, T))`
 * — where the '-' position is a compound term, not a bare metavar. Unifying
 * `acons(H, T)` with the computed result array binds H and T; a naive
 * `argHash !== value` hash comparison would instead reject the (correct) proof
 * as a failure. The cache memoizes clause resolution, so its output binding
 * must be exactly as expressive as the unifier the backchainer uses — never
 * less (the FFI principle applied to the cache: the optimization must agree
 * with the semantics on every goal shape).
 *
 * Returns true iff every position unifies (theta mutated in place); on any
 * mismatch it rolls back all bindings and returns false (a genuine mismatch —
 * the cached output is incompatible with this goal's output pattern).
 */
function _bindOutputs(goal, outputPositions, outputValues, theta, slots) {
  const save = undoSave();
  for (let oi = 0; oi < outputPositions.length; oi++) {
    const val = outputValues[oi];
    // The probe left this output symbolic (undetermined): don't constrain the
    // goal's slot — the caller's final sweep freshens it to an eigenvariable.
    if (val === undefined) continue;
    const argHash = Store.child(goal, outputPositions[oi]);
    if (!matchIndexed(argHash, val, theta, slots)) { undoRestore(theta, save); return false; }
  }
  // Commit the bindings and reclaim the undo-log space (the ffi.js pattern):
  // the outputs are applied to theta but are not rollback-tracked — matching
  // the prior direct-assignment behaviour and bounding the shared undo stack.
  undoDiscard(save);
  return true;
}

const PROFILE = typeof process !== 'undefined' && process.env.CALC_PERF_PROFILE === '1';

const _backwardCache = new Map();
let _bwCacheProbeId = 0;
let _cacheProfile = { hits: 0, misses: 0, negHits: 0 };

function clearBWCache() {
  _backwardCache.clear();
  _bwCacheProbeId = 0;
}

function getCacheProfile() { return _cacheProfile; }
function resetCacheProfile() { _cacheProfile.hits = _cacheProfile.misses = _cacheProfile.negHits = 0; }

Store.onClear(clearBWCache);

/**
 * Try to resolve a persistent goal via the backward proof cache.
 *
 * @param {number} goal - Instantiated goal hash
 * @param {Object} slots - Hash → slot index mapping
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} calc - { clauses, definitions, backchainIndex }
 * @param {boolean} wantTerm - Whether to include proof term in result
 * @param {Function|null} canonicalize - Canonicalization function
 * @param {Object} ffiParsedModes - Parsed FFI modes by predicate
 * @returns {Object|null|undefined}
 *   - undefined: not cacheable or cache miss (prove normally)
 *   - null: cached failure
 *   - { outputs, term }: cached success
 */
function tryBWCache(goal, slots, theta, calc, wantTerm, canonicalize, ffiParsedModes, useFFI) {
  const head = predHead(goal);
  if (!head) return undefined;

  const pm = ffiParsedModes[head];
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
    if (cached === null) { _cacheProfile.negHits++; return null; }
    const outputs = cached.outputs || cached;
    const term = cached.term;
    if (wantTerm && !term) {
      // Fall through to cache miss to re-prove with buildTerm
    } else {
      if (!_bindOutputs(goal, outputPositions, outputs, theta, slots)) return null;
      _cacheProfile.hits++;
      return { outputs, term };
    }
  }

  // Cache miss — probe with fresh metavars
  _cacheProfile.misses++;
  const probeArgs = new Array(arity);
  const probeMetavars = [];
  for (let i = 0; i < arity; i++) probeArgs[i] = Store.child(goal, i);
  for (const oi of outputPositions) {
    const mv = Store.put('metavar', [`bwc_${_bwCacheProbeId++}`]);
    probeArgs[oi] = mv;
    probeMetavars.push(mv);
  }
  const probeGoal = Store.put(head, probeArgs);

  const result = backward.backchain(probeGoal, calc.clauses, calc.definitions, {
    ...(calc.backwardOpts || {}),
    maxDepth: 20000,
    index: calc.backchainIndex,
    buildTerm: !!wantTerm,
    allBuckets: true,
    useFFI: useFFI !== undefined ? useFFI : true,
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

  if (!_bindOutputs(goal, outputPositions, outputValues, theta, slots)) return null;
  return { outputs: outputValues, term: result.term };
}

export { tryBWCache, clearBWCache, getCacheProfile, resetCacheProfile };
export default { tryBWCache, clearBWCache, getCacheProfile, resetCacheProfile };
