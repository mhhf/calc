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

const Store = require('../kernel/store');
const { unify, setTheories } = require('../kernel/unify');
const { defaultTheories } = require('../kernel/eq-theory');
const { binlitTheory } = require('./ill/binlit-theory');
const { apply } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');
const { getPredicateHead } = require('../kernel/ast');
const { collectMetavars, isGround } = require('./pattern-utils');
const backward = require('./backchain');
const { tryFFIDirect } = require('./opt/ffi');
const { binToInt, intToBin } = require('./ill/ffi/convert');

/**
 * Alpha-rename a clause (head + premises) with fresh metavars.
 * Single renaming theta covers all metavars in head AND premises.
 */
function alphaRenameClause(head, premises) {
  const mvs = new Set();
  collectMetavars(head, mvs);
  for (const p of premises) collectMetavars(p, mvs);
  if (mvs.size === 0) return { head, premises };
  const theta = [];
  for (const mv of mvs) theta.push([mv, freshMetavar()]);
  return {
    head: apply(head, theta),
    premises: premises.map(p => apply(p, theta)),
  };
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
function composeMapTheta(thetaMap, theta2) {
  if (theta2.length === 0) return thetaMap;
  const newMap = new Map();
  for (const [mv, val] of thetaMap) {
    if (isGround(val)) {
      newMap.set(mv, val);
    } else {
      newMap.set(mv, binlitTheory.canonicalize(apply(val, theta2)));
    }
  }
  for (const [mv, val] of theta2) {
    if (!newMap.has(mv)) newMap.set(mv, binlitTheory.canonicalize(val));
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
    const pred = getPredicateHead(hash);
    if (pred) { if (!defIdx.has(pred)) defIdx.set(pred, []); defIdx.get(pred).push({ name, hash }); }
  }
  for (const [name, clause] of clauses) {
    const pred = getPredicateHead(clause.hash);
    if (pred) { if (!clIdx.has(pred)) clIdx.set(pred, []); clIdx.get(pred).push({ name, hash: clause.hash, premises: clause.premises }); }
  }
  return { defIdx, clIdx };
}

/**
 * Count free (unbound) metavars in a term after applying thetaMap.
 * Used by most-constrained-first heuristic.
 */
function countFreeMetavars(h, thetaMap) {
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
function resolveAll(goals, clauses, definitions, opts = {}) {
  setTheories([...defaultTheories, binlitTheory]);

  const maxSolutions = opts.maxSolutions || DEFAULT_MAX_SOLUTIONS;
  const solutions = [];
  const { defIdx, clIdx } = buildSimpleIndex(clauses, definitions);

  function search(remainingGoals, thetaMap, depth) {
    if (solutions.length >= maxSolutions + 1) return;
    if (depth > MAX_DEPTH) return;

    if (remainingGoals.length === 0) {
      solutions.push(mapToArray(thetaMap));
      return;
    }

    // Most-constrained-first: pick goal with fewest free metavars
    let bestIdx = 0;
    let bestFree = Infinity;
    for (let i = 0; i < remainingGoals.length; i++) {
      const free = countFreeMetavars(remainingGoals[i], thetaMap);
      if (free < bestFree) {
        bestFree = free;
        bestIdx = i;
        if (free === 0) break; // ground goal — resolve immediately
      }
    }

    const currentGoal = mapApply(remainingGoals[bestIdx], thetaMap);
    const rest = remainingGoals.length === 1 ? [] :
      [...remainingGoals.slice(0, bestIdx), ...remainingGoals.slice(bestIdx + 1)];
    const pred = getPredicateHead(currentGoal);
    if (!pred) return;

    // FFI fast path: O(1) arithmetic for ground/partially-ground goals.
    // Handles plus, inc, lt, le, gte, etc. when input positions are ground.
    // Avoids expensive SLD resolution through binary arithmetic clauses.
    const ffiResult = tryFFIDirect(currentGoal);
    if (ffiResult && ffiResult.success) {
      search(rest, composeMapTheta(thetaMap, ffiResult.theta || []), depth + 1);
      return;
    }

    // Native between enumeration: between(X, Lo, Hi) where Lo, Hi are ground.
    // Directly generates X = Lo..Hi without SLD recursion through inc/lt/le.
    if (pred === 'between' && Store.arity(currentGoal) === 3) {
      const x = Store.child(currentGoal, 0);
      const lo = Store.child(currentGoal, 1);
      const hi = Store.child(currentGoal, 2);
      const loInt = binToInt(lo);
      const hiInt = binToInt(hi);
      if (loInt !== null && hiInt !== null) {
        const xInt = binToInt(x);
        if (xInt !== null) {
          // X is ground — membership check
          if (xInt >= loInt && xInt <= hiInt) {
            search(rest, thetaMap, depth + 1);
          }
        } else {
          // X is non-ground — enumerate Lo..Hi
          for (let n = loInt; n <= hiInt; n++) {
            if (solutions.length >= maxSolutions + 1) return;
            const valHash = intToBin(n);
            const theta2 = unify(x, valHash);
            if (theta2) {
              search(rest, composeMapTheta(thetaMap, theta2), depth + 1);
            }
          }
        }
        return;
      }
    }

    // Ground goals without FFI: use the Backchainer (clause resolution).
    if (bestFree === 0) {
      const result = backward.prove(currentGoal, clauses, definitions);
      if (result.success && result.theta) {
        search(rest, composeMapTheta(thetaMap, result.theta), depth + 1);
      }
      return;
    }

    // Non-ground goals: full SLD enumeration.

    // Try definitions (zero-premise axioms)
    const defs = defIdx.get(pred) || [];
    for (const def of defs) {
      if (solutions.length >= maxSolutions + 1) return;
      const renamed = alphaRenameClause(def.hash, []);
      const theta2 = unify(currentGoal, renamed.head);
      if (theta2) {
        search(rest, composeMapTheta(thetaMap, theta2), depth + 1);
      }
    }

    // Try clauses (with premises)
    const cls = clIdx.get(pred) || [];
    for (const cl of cls) {
      if (solutions.length >= maxSolutions + 1) return;
      const renamed = alphaRenameClause(cl.hash, cl.premises);
      const theta2 = unify(currentGoal, renamed.head);
      if (theta2) {
        const newTheta = composeMapTheta(thetaMap, theta2);
        const newGoals = [
          ...renamed.premises.map(p => apply(p, theta2)),
          ...rest,
        ];
        search(newGoals, newTheta, depth + 1);
      }
    }
  }

  search(goals, new Map(), 0);

  if (solutions.length > maxSolutions) {
    throw new Error(
      `resolveAll: exceeded max solutions (${maxSolutions}) — ` +
      `ensure the clause is range-bounded`
    );
  }

  return solutions;
}

module.exports = { resolveAll };
