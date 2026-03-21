/**
 * Backward proof cache for persistent goal resolution.
 *
 * Layer: Optimization (toggleable)
 *
 * For deterministic predicates with known mode (input/output args),
 * caches (pred, input_args...) → output_values.
 *
 * Soundness: sound iff persistent context is monotonically growing.
 * MUST be cleared at start of each run/explore call.
 *
 * Extracted from lnl/persistent.js for toggleability and testability.
 */

const Store = require('../../kernel/store');
const { getPredicateHead } = require('../../kernel/ast');

const _TAG_METAVAR = Store.TAG.metavar;

const _backwardCache = new Map();
let _bwCacheProbeId = 0;

function clearBackwardCache() {
  _backwardCache.clear();
  _bwCacheProbeId = 0;
}

Store.onClear(clearBackwardCache);

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
function tryBackwardCache(goal, slots, theta, calc, wantTerm, canonicalize, ffiParsedModes) {
  const head = getPredicateHead(goal);
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

module.exports = { tryBackwardCache, clearBackwardCache };
