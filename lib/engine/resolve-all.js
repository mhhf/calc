/**
 * Compile-time SLD resolution — enumerate ALL ground solutions.
 *
 * Used by grade-0 tabling: resolve `!_0 head <- premise1 <- premise2`
 * into a set of virtual ground facts at compile time.
 *
 * Uses Map-based theta for O(1) variable lookup and most-constrained-first
 * goal selection to avoid infinite branching from generative predicates
 * (e.g., plus with two free variables).
 */

'use strict';

const { performance } = require('perf_hooks');
const Store = require('../kernel/store');
const { unify } = require('../kernel/unify');
const { apply } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');
const { predHead } = require('../kernel/ast');
const { collectMetavars, isGround } = require('./pattern-utils');
const backward = require('./backchain');


// ─── Profiling accumulator factory ─────────────────────────────────────────────
// Create a fresh accumulator for resolve-all instrumentation. All fields are
// numeric counters/millis so merging across calls is a field-wise sum.
// Used by compose.js tabling to drill into where time is spent inside SLD search.
// When `prof` is null, all instrumentation short-circuits — zero overhead.
function _newProf() {
  return {
    // Search shape
    searchNodes: 0,
    maxDepth: 0,
    solutionsFound: 0,
    // Goal selection (freeCount loop)
    selectGoalMs: 0,
    freeCountCalls: 0,
    // mapApply on current goal
    mapApplyMs: 0,
    mapApplyCalls: 0,
    // alpha-rename clauses/defs
    alphaRenMs: 0,
    alphaRenCalls: 0,
    // unify (counters only — too hot to time per-call without skew)
    unifyAttempts: 0,
    unifySucceeded: 0,
    unifyFailures: 0,
    // Unify wall-clock: batched across a clause/def loop to amortize perf.now() cost
    unifyMs: 0,
    // composeSub (includes canonicalize cost)
    composeSubMs: 0,
    composeSubCalls: 0,
    // apply() on premises after unification
    applyPremisesMs: 0,
    applyPremisesCalls: 0,
    // backchain.prove (ground goal delegation)
    backchainMs: 0,
    backchainCalls: 0,
    backchainSuccesses: 0,
    // FFI fast path
    ffiMs: 0,
    ffiCalls: 0,
    ffiSuccesses: 0,
    // Native predicate handlers (between, ...)
    nativeMs: 0,
    nativeCalls: 0,
    // Candidate lookup shape (defIdx / clIdx dispatch)
    backchainLookups: 0,
    totalCandidates: 0,
    maxCandidates: 0,
    // One-time index build
    indexMs: 0,
    indexCalls: 0,
  };
}


/**
 * Alpha-rename a clause (head + premises) with fresh metavars, using a single
 * renaming θ over all metavars in head ∪ premises.
 *
 * `mvs` is the precomputed list of metavar hashes for this clause — captured
 * once at index-build time via `_collectClauseMvs` because the set is static
 * per clause but the function is called on every SLD-resolution hit.
 */
function alphaRen(head, premises, mvs) {
  if (mvs.length === 0) return { head, premises };
  const theta = new Array(mvs.length);
  for (let i = 0; i < mvs.length; i++) theta[i] = [mvs[i], freshMetavar()];
  return {
    head: apply(head, theta),
    premises: premises.map(p => apply(p, theta)),
  };
}

/** Collect every distinct metavar hash in head ∪ premises as an array. */
function _collectClauseMvs(head, premises) {
  const s = new Set();
  collectMetavars(head, s);
  for (const p of premises) collectMetavars(p, s);
  return [...s];
}

/**
 * Apply a Map-based substitution to a term.
 * O(term_size) — each node does O(1) Map lookup.
 */
function mapApply(h, thetaMap) {
  if (thetaMap.size === 0) return h;
  function go(hash) {
    const bound = thetaMap.get(hash);
    if (bound !== undefined) return go(bound);
    const t = Store.tag(hash);
    if (!t || t === 'atom' || t === 'freevar' || t === 'metavar' ||
        t === 'binlit' || t === 'strlit' || t === 'charlit') return hash;
    if (Store.tagId(hash) === Store.TAG.arrlit) {
      const elems = Store.getArrayElements(hash);
      if (!elems || elems.length === 0) return hash;
      let changed = false;
      const ne = new Uint32Array(elems.length);
      for (let i = 0; i < elems.length; i++) {
        ne[i] = go(elems[i]);
        if (ne[i] !== elems[i]) changed = true;
      }
      return changed ? Store.putArray(ne) : hash;
    }
    const a = Store.arity(hash);
    if (a === 0) return hash;
    let changed = false;
    const nc = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (typeof c === 'number' && Store.isTerm(c)) {
        const rc = go(c);
        nc.push(rc);
        if (rc !== c) changed = true;
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(Store.tag(hash), nc) : hash;
  }
  return go(h);
}

/**
 * Compose a Map theta with an array theta2 from unify().
 * Canonicalizes all values to prevent non-canonical binary (i/o/e chains)
 * from generating duplicate search branches.
 */
function composeSub(thetaMap, theta2, canonicalize) {
  if (theta2.length === 0) return thetaMap;
  const newMap = new Map();
  for (const [mv, val] of thetaMap) {
    if (isGround(val)) {
      newMap.set(mv, val);
    } else {
      const applied = apply(val, theta2);
      newMap.set(mv, canonicalize ? canonicalize(applied) : applied);
    }
  }
  for (const [mv, val] of theta2) {
    if (!newMap.has(mv)) newMap.set(mv, canonicalize ? canonicalize(val) : val);
  }
  return newMap;
}

/**
 * Convert a Map theta to an array, fully resolving all values.
 * Each value is mapApply'd through the theta to eliminate metavar chains
 * (e.g., ?A → i(?B), ?B → e becomes ?A → i(e)).
 */
function mapToArray(thetaMap) {
  const arr = [];
  for (const [k, v] of thetaMap) arr.push([k, mapApply(v, thetaMap)]);
  return arr;
}

function buildSimpleIndex(clauses, definitions) {
  const defIdx = new Map();
  const clIdx = new Map();
  for (const [name, hash] of definitions) {
    const pred = predHead(hash);
    if (pred) {
      if (!defIdx.has(pred)) defIdx.set(pred, []);
      defIdx.get(pred).push({ name, hash, mvs: _collectClauseMvs(hash, []) });
    }
  }
  for (const [name, clause] of clauses) {
    const pred = predHead(clause.hash);
    if (pred) {
      if (!clIdx.has(pred)) clIdx.set(pred, []);
      clIdx.get(pred).push({
        name,
        hash: clause.hash,
        premises: clause.premises,
        mvs: _collectClauseMvs(clause.hash, clause.premises),
      });
    }
  }
  return { defIdx, clIdx };
}

/**
 * Count free (unbound) metavars in a term after applying thetaMap.
 * Used by most-constrained-first heuristic.
 */
function freeCount(h, thetaMap) {
  const mvs = new Set();
  collectMetavars(h, mvs);
  let free = 0;
  for (const mv of mvs) {
    if (!thetaMap.has(mv)) free++;
  }
  return free;
}

const DEFAULT_MAX_SOLUTIONS = 10000;
const MAX_DEPTH = 2000;

/**
 * Enumerate all solutions of a goal list via SLD resolution.
 *
 * Uses most-constrained-first goal selection: at each step, picks the goal
 * with the fewest free metavars. This ensures constraining goals (e.g.,
 * inc(Q, 48)) run before generative goals (e.g., plus(47, N, Q)),
 * preventing infinite branching from underconstrained predicates.
 *
 * Ground goals (0 free metavars) delegate to the Backchainer which has FFI
 * support for O(1) arithmetic evaluation.
 *
 * @param {number[]} goals - list of goal hashes to resolve conjunctively
 * @param {Map} clauses - name → { hash, premises }
 * @param {Map} definitions - name → hash (zero-premise axioms)
 * @param {Object} [opts]
 * @param {number} [opts.maxSolutions=10000] - safety bound
 * @returns {Array<Array<[number,number]>>} array of theta (each a list of [metavar, value] pairs)
 */
function resolve(goals, clauses, definitions, opts = {}) {
  // Callers provide canonicalize/nativePredicates (orchestrator injects from
  // calculus config, direct callers use ILL-specific helpers if needed).
  const canonicalize = opts.canonicalize || null;
  const nativePredicates = opts.nativePredicates || {};
  const _ffiCtx = opts.ffiContext || null;
  const _ffiDirect = opts.ffiDirect || null;
  const _backchainOpts = opts.backchainOpts || {};
  // Optional profiling accumulator. When provided, timings/counters are
  // recorded in-place on the given object (merge across multiple resolve()
  // calls by passing the same object). All instrumentation is gated behind
  // `prof` truthiness → zero overhead when omitted.
  const prof = opts.prof || null;

  const maxSolutions = opts.maxSolutions || DEFAULT_MAX_SOLUTIONS;
  const solutions = [];

  let _tIdx0 = 0;
  if (prof) _tIdx0 = performance.now();
  const { defIdx, clIdx } = buildSimpleIndex(clauses, definitions);
  if (prof) { prof.indexMs += performance.now() - _tIdx0; prof.indexCalls++; }

  function search(remainingGoals, thetaMap, depth) {
    if (prof) {
      prof.searchNodes++;
      if (depth > prof.maxDepth) prof.maxDepth = depth;
    }
    if (solutions.length >= maxSolutions + 1) return;
    if (depth > MAX_DEPTH) return;

    if (remainingGoals.length === 0) {
      solutions.push(mapToArray(thetaMap));
      if (prof) prof.solutionsFound++;
      return;
    }

    // Most-constrained-first: pick goal with fewest free metavars
    const _tSel0 = prof ? performance.now() : 0;
    let bestIdx = 0;
    let bestFree = Infinity;
    for (let i = 0; i < remainingGoals.length; i++) {
      const free = freeCount(remainingGoals[i], thetaMap);
      if (prof) prof.freeCountCalls++;
      if (free < bestFree) {
        bestFree = free;
        bestIdx = i;
        if (free === 0) break; // ground goal — resolve immediately
      }
    }
    if (prof) prof.selectGoalMs += performance.now() - _tSel0;

    const _tApply0 = prof ? performance.now() : 0;
    const currentGoal = mapApply(remainingGoals[bestIdx], thetaMap);
    if (prof) { prof.mapApplyMs += performance.now() - _tApply0; prof.mapApplyCalls++; }

    const rest = remainingGoals.length === 1 ? [] :
      [...remainingGoals.slice(0, bestIdx), ...remainingGoals.slice(bestIdx + 1)];
    const pred = predHead(currentGoal);
    if (!pred) return;

    // FFI fast path: O(1) arithmetic for ground/partially-ground goals.
    // When ffiDirect + ffiContext are provided, uses FFI for plus, inc, etc.
    // Without them, falls through to clause resolution.
    const _tFfi0 = (prof && _ffiDirect && _ffiCtx) ? performance.now() : 0;
    const ffiResult = (_ffiDirect && _ffiCtx)
      ? _ffiDirect(currentGoal, _ffiCtx.meta, _ffiCtx.get, _ffiCtx.parsedModes, _ffiCtx.isFFIGround)
      : null;
    if (prof && _ffiDirect && _ffiCtx) { prof.ffiMs += performance.now() - _tFfi0; prof.ffiCalls++; }
    if (ffiResult && ffiResult.success) {
      if (prof) prof.ffiSuccesses++;
      const _tCs0 = prof ? performance.now() : 0;
      const newTheta = composeSub(thetaMap, ffiResult.theta || [], canonicalize);
      if (prof) { prof.composeSubMs += performance.now() - _tCs0; prof.composeSubCalls++; }
      search(rest, newTheta, depth + 1);
      return;
    }

    // Native predicate handlers (injectable via opts.nativePredicates).
    // Default: between(X, Lo, Hi) → enumerate X = Lo..Hi using ILL binToInt/intToBin.
    const nativeHandler = nativePredicates[pred];
    if (nativeHandler) {
      const _tNat0 = prof ? performance.now() : 0;
      const handled = nativeHandler(currentGoal, rest, thetaMap, depth, search);
      if (prof) { prof.nativeMs += performance.now() - _tNat0; prof.nativeCalls++; }
      if (handled) return;
    }

    // Ground goals without FFI: use the Backchainer (clause resolution).
    if (bestFree === 0) {
      const _tBk0 = prof ? performance.now() : 0;
      const result = backward.prove(currentGoal, clauses, definitions, _backchainOpts);
      if (prof) { prof.backchainMs += performance.now() - _tBk0; prof.backchainCalls++; }
      if (result.success && result.theta) {
        if (prof) prof.backchainSuccesses++;
        const _tCs0 = prof ? performance.now() : 0;
        const newTheta = composeSub(thetaMap, result.theta, canonicalize);
        if (prof) { prof.composeSubMs += performance.now() - _tCs0; prof.composeSubCalls++; }
        search(rest, newTheta, depth + 1);
      }
      return;
    }

    // Non-ground goals: full SLD enumeration.

    // Try definitions (zero-premise axioms)
    const defs = defIdx.get(pred) || [];
    if (prof && defs.length > 0) {
      prof.backchainLookups++;
      if (defs.length > prof.maxCandidates) prof.maxCandidates = defs.length;
      prof.totalCandidates += defs.length;
    }
    for (const def of defs) {
      if (solutions.length >= maxSolutions + 1) return;
      const _tAr0 = prof ? performance.now() : 0;
      const renamed = alphaRen(def.hash, [], def.mvs);
      if (prof) { prof.alphaRenMs += performance.now() - _tAr0; prof.alphaRenCalls++; }

      const _tUn0 = prof ? performance.now() : 0;
      const theta2 = unify(currentGoal, renamed.head);
      if (prof) {
        prof.unifyMs += performance.now() - _tUn0;
        prof.unifyAttempts++;
        if (theta2) prof.unifySucceeded++; else prof.unifyFailures++;
      }
      if (theta2) {
        const _tCs0 = prof ? performance.now() : 0;
        const newTheta = composeSub(thetaMap, theta2, canonicalize);
        if (prof) { prof.composeSubMs += performance.now() - _tCs0; prof.composeSubCalls++; }
        search(rest, newTheta, depth + 1);
      }
    }

    // Try clauses (with premises)
    const cls = clIdx.get(pred) || [];
    if (prof && cls.length > 0) {
      prof.backchainLookups++;
      if (cls.length > prof.maxCandidates) prof.maxCandidates = cls.length;
      prof.totalCandidates += cls.length;
    }
    for (const cl of cls) {
      if (solutions.length >= maxSolutions + 1) return;
      const _tAr0 = prof ? performance.now() : 0;
      const renamed = alphaRen(cl.hash, cl.premises, cl.mvs);
      if (prof) { prof.alphaRenMs += performance.now() - _tAr0; prof.alphaRenCalls++; }

      const _tUn0 = prof ? performance.now() : 0;
      const theta2 = unify(currentGoal, renamed.head);
      if (prof) {
        prof.unifyMs += performance.now() - _tUn0;
        prof.unifyAttempts++;
        if (theta2) prof.unifySucceeded++; else prof.unifyFailures++;
      }
      if (theta2) {
        const _tCs0 = prof ? performance.now() : 0;
        const newTheta = composeSub(thetaMap, theta2, canonicalize);
        if (prof) { prof.composeSubMs += performance.now() - _tCs0; prof.composeSubCalls++; }
        const _tAp0 = prof ? performance.now() : 0;
        const newGoals = [
          ...renamed.premises.map(p => apply(p, theta2)),
          ...rest,
        ];
        if (prof) { prof.applyPremisesMs += performance.now() - _tAp0; prof.applyPremisesCalls++; }
        search(newGoals, newTheta, depth + 1);
      }
    }
  }

  search(goals, new Map(), 0);

  if (solutions.length > maxSolutions) {
    throw new Error(
      `resolve: exceeded max solutions (${maxSolutions}) — ` +
      `ensure the clause is range-bounded`
    );
  }

  return solutions;
}

module.exports = { resolve, newProf: _newProf };
