// @ts-check
/**
 * Compose optimization pass P6 — McCarthy array-axiom normalization +
 * SROA (scalar replacement of aggregates) (RES_0143 M4; extracted from
 * compose.js).
 *
 * Operates on cc-declared array-access predicates (sroaConfig): peels
 * acons layers from array goals and expands cons patterns in linear
 * resources. Semantics-preserving, doubly opt-in — compose0 receives
 * this pass as a PASS RECORD via composeOpts.optPasses (F3 pipeline
 * shape) from the composition root.
 */

import Store from '../../kernel/store.js';
import { unify } from '../../kernel/unify.js';
import { apply } from '../../kernel/substitute.js';
import { freshMetavar } from '../../kernel/fresh.js';
import { flattenAnte, unwrapComp } from '../formula-utils.js';
import { predHead, rTensor } from '../../kernel/ast.js';
import { collectMetavars, isGround } from '../pattern-utils.js';
import { _makeRule, _requireConnTags, _tagDisjoint } from '../compose.js';
import { gradeW, grade0 } from '../grades.js';

// ─── Pass 6: SROA — scalar replacement of aggregates ─────────────────────────

/**
 * SROA (Scalar Replacement of Aggregates) for array-backed resources.
 *
 * Only applies to rules with `isFused: true` (produced by fusePair).
 * When such a rule has persistent array-access goals with ground indices on
 * an array held by a linear resource, SROA expands the array pattern into
 * individual slots and eliminates the goals.
 *
 * Example: resource([X | REST]) * !get(REST, 0, Y) * !set(REST, 0, X, REST')
 *   becomes: resource([X, S0 | TAIL]) with Y=S0, REST'=[X | TAIL]
 *
 * Preceded by McCarthy normalization (read-head, write-head axioms) which
 * resolves goals on concrete acons patterns before SROA handles the metavar case.
 *
 * @param {Object[]} pool - raw rules
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @param {Object} sroaConfig - { arrayPreds, resourcePred, parseIndex, buildIndex }
 * @returns {{ rules: Object[], sroaCount: number, mccarthyCount: number }}
 */
function _sroa(pool, rc, getModeMeta, sroaConfig) {
  if (!sroaConfig) return { rules: pool, sroaCount: 0, mccarthyCount: 0 };
  const cfg = sroaConfig;
  const result = [];
  let sroaCount = 0;
  let mccarthyCount = 0;

  for (const rule of pool) {
    if (!rule.isFused) {
      result.push(rule);
      continue;
    }

    // Phase A: McCarthy normalization — peel acons layers from array-access goals.
    // get([H|T], 0, V) → V=H (direct), get([H|T], N, V) → get(T, N-1, V) (reduced).
    const normalized = _mccarthy(rule, rc, cfg);
    const effective = normalized || rule;
    if (normalized) mccarthyCount++;

    // Phase B: SROA — expand cons pattern for remaining metavar array goals.
    const transformed = _trySROA(effective, rc, cfg);
    if (transformed) {
      result.push(transformed);
      sroaCount++;
      continue;
    }
    result.push(effective);
  }

  return { rules: result, sroaCount, mccarthyCount };
}

// ─── McCarthy array axiom normalization ──────────────────────────────────────
//
// When array-access goals have an acons (cons cell) as their array argument,
// list-based rewrite rules derived from McCarthy's select/store axioms reduce
// them. McCarthy (1962) and Stump et al. (2001) state the axioms over flat
// arrays: select(store(a,i,v),i)=v, select(store(a,i,v),j)=select(a,j).
// Our acons(H,T) head-tail encoding is semantically equivalent for ground
// non-negative indices, forming a convergent conditional rewrite system:
//   get([H|T], 0, V)  →  V = H                    (read-head)
//   get([H|T], N, V)  →  get(T, N-1, V)           (read-tail, N>0)
//   set([H|T], 0, W, R)  →  R = [W|T]             (write-head)
//   set([H|T], N, W, R)  →  set(T, N-1, W, I), R = [H|I]  (write-tail)
//
// Termination: structural recursion on acons depth. Confluence: ground indices
// mean at most one rule fires per goal (no critical pairs).
// Applied iteratively for deeper acons chains. Goals resolved directly are
// eliminated; goals reduced to metavar base are left for SROA.

/**
 * Peel acons layers from a hash, collecting head elements.
 * @returns {{ base: number, heads: number[], depth: number }}
 */
function _peelCons(h) {
  const heads = [];
  let cur = h;
  while (Store.tag(cur) === 'acons' && Store.arity(cur) === 2) {
    heads.push(Store.child(cur, 0));
    cur = Store.child(cur, 1);
  }
  return { base: cur, heads, depth: heads.length };
}

/**
 * McCarthy normalization for a single rule.
 * Peels acons layers from array-access goals, resolving or reducing them.
 * Returns transformed rule or null if nothing to normalize.
 */
function _mccarthy(rule, rc, sroaConfig) {
  const { bangTag, loliTag } = _requireConnTags(rc, false);
  const anteHash = Store.child(rule.hash, 0);
  const ante = flattenAnte(anteHash, rc);
  const arrGoals = _arrGoals(ante.persistent, sroaConfig);

  // Find goals with acons arrVar and ground index
  const aconsGoals = [];
  for (const g of arrGoals) {
    if (Store.tag(g.arrVar) !== 'acons') continue;
    if (!isGround(g.idx) || sroaConfig.parseIndex(g.idx) === null) continue;
    aconsGoals.push(g);
  }
  if (aconsGoals.length === 0) return null;

  /** @type {[number, number][]} */
  const theta = [];
  const eliminatedGoals = new Set();
  const newGoals = []; // replacement goals with reduced index

  for (const g of aconsGoals) {
    const { base, heads, depth } = _peelCons(g.arrVar);
    const idxNum = Number(sroaConfig.parseIndex(g.idx));

    if (g.type === 'get') {
      if (idxNum < depth) {
        // McCarthy read-head: get([H0..Hk|T], idx, V) with idx < k → V = H[idx]
        theta.push([g.outVar, heads[idxNum]]);
        eliminatedGoals.add(g.hash);
      } else {
        // McCarthy read-tail: reduce index by depth, goal now references base
        const newIdx = sroaConfig.buildIndex(BigInt(idxNum - depth));
        const newGoalHash = Store.put(sroaConfig.arrayPreds[0], [base, newIdx, g.outVar]);
        eliminatedGoals.add(g.hash);
        newGoals.push(newGoalHash);
      }
    } else if (g.type === 'set') {
      if (idxNum < depth) {
        // McCarthy write-head: replace heads[idx], rebuild acons chain
        const newHeads = [...heads];
        newHeads[idxNum] = g.val;
        let rebuilt = base;
        for (let i = newHeads.length - 1; i >= 0; i--) {
          rebuilt = Store.put('acons', [newHeads[i], rebuilt]);
        }
        _decompTheta(g.outVar, rebuilt, theta);
        eliminatedGoals.add(g.hash);
      } else {
        // McCarthy write-tail: reduce index, wrap output with preserved heads
        const innerOut = freshMetavar();
        const newIdx = sroaConfig.buildIndex(BigInt(idxNum - depth));
        const newGoalHash = Store.put(sroaConfig.arrayPreds[1], [base, newIdx, g.val, innerOut]);
        let rebuilt = innerOut;
        for (let i = heads.length - 1; i >= 0; i--) {
          rebuilt = Store.put('acons', [heads[i], rebuilt]);
        }
        _decompTheta(g.outVar, rebuilt, theta);
        eliminatedGoals.add(g.hash);
        newGoals.push(newGoalHash);
      }
    }
  }

  if (eliminatedGoals.size === 0) return null;

  // Compose theta: resolve transitive bindings (acyclic → single pass)
  for (let i = 0; i < theta.length; i++) {
    theta[i][1] = apply(theta[i][1], theta);
  }

  // Apply theta to the whole rule
  const thetaApplied = apply(rule.hash, theta);
  const newConseqHash = Store.child(thetaApplied, 1);

  // Reconstruct antecedent: remove eliminated goals, add reduced goals
  const newAnteRaw = Store.child(thetaApplied, 0);
  const newAnte = flattenAnte(newAnteRaw, rc);

  const appliedEliminated = new Set();
  for (const h of eliminatedGoals) appliedEliminated.add(apply(h, theta));

  const anteParts = [];
  for (const h of newAnte.linear) anteParts.push(h);
  for (const p of newAnte.persistent) {
    if (!appliedEliminated.has(p)) anteParts.push(Store.put(bangTag, [gradeW(), p]));
  }
  for (const ng of newGoals) {
    anteParts.push(Store.put(bangTag, [gradeW(), apply(ng, theta)]));
  }
  for (const p of (newAnte.grade0 || [])) anteParts.push(Store.put(bangTag, [grade0(), p]));
  const newAnteHash = rTensor(anteParts);

  const newFullHash = Store.put(loliTag, [newAnteHash, newConseqHash]);

  return _tagDisjoint({
    name: rule.name,
    hash: newFullHash,
    antecedent: newAnteHash,
    consequent: newConseqHash,
    sourceLabel: rule.sourceLabel || null,
  });
}

/**
 * Try to apply SROA to a single rule. Returns new rule or null.
 */
function _trySROA(rule, rc, sroaConfig) {
  const { bangTag, loliTag } = _requireConnTags(rc, false);
  const anteHash = Store.child(rule.hash, 0);
  const ante = flattenAnte(anteHash, rc);

  // Phase 1: Find array get/set persistent goals and the array holder.
  const arrGoals = _arrGoals(ante.persistent, sroaConfig);
  if (arrGoals.length === 0) return null;

  const arrBaseVars = new Set();
  for (const g of arrGoals) arrBaseVars.add(g.arrVar);

  // Find a linear fact holding an array var (resource([TOP | REST]) or resource(S))
  // Walk the full acons chain — after McCarthy normalization, the arrVar may be
  // nested several levels deep (e.g., resource([A | [B | REST]]) with arrVar=REST).
  const resourcePred = sroaConfig ? sroaConfig.resourcePred : null;
  let baseVar = null;
  for (const h of ante.linear) {
    const pred = predHead(h);
    if (!pred || Store.arity(h) !== 1) continue;
    if (resourcePred && pred !== resourcePred) continue;
    const child = Store.child(h, 0);
    let cur = child;
    while (Store.tag(cur) === 'acons' && Store.arity(cur) === 2) {
      const tail = Store.child(cur, 1);
      if (arrBaseVars.has(tail)) { baseVar = tail; break; }
      cur = tail;
    }
    if (baseVar) break;
    if (Store.tag(child) === 'metavar' && arrBaseVars.has(child)) { baseVar = child; break; }
  }
  if (!baseVar) return null;

  // Phase 2: Collect version chain (fixpoint over array-set outputs).
  const chainGoals = [];
  const allVersions = new Set([baseVar]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const g of arrGoals) {
      if (!allVersions.has(g.arrVar) || chainGoals.includes(g)) continue;
      if (!isGround(g.idx) || sroaConfig.parseIndex(g.idx) === null) return null;
      chainGoals.push(g);
      if (g.type === 'set') { allVersions.add(g.outVar); changed = true; }
    }
  }
  if (chainGoals.length === 0) return null;

  // Phase 3: Determine expansion depth = max index + 1.
  let maxIdx = 0n;
  for (const g of chainGoals) { const i = sroaConfig.parseIndex(g.idx); if (i > maxIdx) maxIdx = i; }
  const depth = Number(maxIdx) + 1;

  // Phase 4: Build theta — the core substitution.
  // (a) Expand baseVar: A → [V0, V1, ..., VK | TAIL]
  const slotVars = [];
  for (let i = 0; i < depth; i++) slotVars.push(freshMetavar());
  const tailVar = freshMetavar();

  /** @type {[number, number][]} */
  const theta = [];
  {
    let baseArr = tailVar;
    for (let i = slotVars.length - 1; i >= 0; i--) baseArr = Store.put('acons', [slotVars[i], baseArr]);
    theta.push([baseVar, baseArr]);
  }

  // (b) Trace version chain: get(V, idx, X) → X = V_slots[idx]
  //                           set(V, idx, val, V') → V' = modified slots
  const versionSlots = new Map();
  versionSlots.set(baseVar, [...slotVars]);

  const processQueue = [baseVar];
  const processed = new Set();
  while (processQueue.length > 0) {
    const curVar = processQueue.shift();
    if (processed.has(curVar)) continue;
    processed.add(curVar);
    const curSlots = versionSlots.get(curVar);
    if (!curSlots) continue;

    for (const g of chainGoals) {
      if (g.arrVar !== curVar || g.type !== 'get') continue;
      theta.push([g.outVar, curSlots[Number(sroaConfig.parseIndex(g.idx))]]);
    }
    for (const g of chainGoals) {
      if (g.arrVar !== curVar || g.type !== 'set') continue;
      const idx = Number(sroaConfig.parseIndex(g.idx));
      const newSlots = [...curSlots];
      newSlots[idx] = g.val;
      let newArr = tailVar;
      for (let i = newSlots.length - 1; i >= 0; i--) newArr = Store.put('acons', [newSlots[i], newArr]);
      // Decompose structured output patterns (e.g. [?H | ?T] from fusion)
      _decompTheta(g.outVar, newArr, theta);
      versionSlots.set(g.outVar, newSlots);
      processQueue.push(g.outVar);
    }
  }

  // Compose theta: apply requires idempotent substitution, but version chains
  // create transitive entries (e.g. [X, Y] + [Y, V0]). Resolve by applying
  // theta to all values. Acyclic chain → single pass suffices.
  for (let i = 0; i < theta.length; i++) {
    theta[i][1] = apply(theta[i][1], theta);
  }

  // Phase 5: Apply theta to the whole rule hash (preserves existentials).
  const thetaApplied = apply(rule.hash, theta);
  const newConseqHash = Store.child(thetaApplied, 1);

  // Only the antecedent needs structural surgery: remove eliminated persistent goals.
  const newAnteRaw = Store.child(thetaApplied, 0);
  const newAnte = flattenAnte(newAnteRaw, rc);

  // Build set of theta-applied goal hashes to remove
  const eliminatedGoals = new Set();
  for (const g of chainGoals) eliminatedGoals.add(apply(g.hash, theta));

  const anteParts = [];
  for (const h of newAnte.linear) anteParts.push(h);
  for (const p of newAnte.persistent) {
    if (!eliminatedGoals.has(p)) anteParts.push(Store.put(bangTag, [gradeW(), p]));
  }
  for (const p of (newAnte.grade0 || [])) anteParts.push(Store.put(bangTag, [grade0(), p]));
  const newAnteHash = rTensor(anteParts);

  const newFullHash = Store.put(loliTag, [newAnteHash, newConseqHash]);

  return _tagDisjoint({
    name: `${rule.name}[sroa:${depth}]`,
    hash: newFullHash,
    antecedent: newAnteHash,
    consequent: newConseqHash,
    sourceLabel: rule.sourceLabel || null,
  });
}

/**
 * Decompose a pattern against a concrete expanded array, adding bindings to theta.
 * Handles structured output patterns from array-set (e.g. [?H | ?T] from fusion).
 * For metavar leaves, adds a direct substitution. For acons patterns, recurses.
 */
function _decompTheta(pattern, expanded, theta) {
  if (Store.tag(pattern) === 'metavar') {
    theta.push([pattern, expanded]);
    return;
  }
  if (Store.tag(pattern) === 'acons' && Store.arity(pattern) === 2) {
    // Pattern is [head | tail] — decompose against expanded acons chain
    if (Store.tag(expanded) === 'acons' && Store.arity(expanded) === 2) {
      _decompTheta(Store.child(pattern, 0), Store.child(expanded, 0), theta);
      _decompTheta(Store.child(pattern, 1), Store.child(expanded, 1), theta);
    } else {
      // Structural mismatch — push whole substitution as fallback
      theta.push([pattern, expanded]);
    }
    return;
  }
  // Ground or other — push whole substitution
  theta.push([pattern, expanded]);
}

/**
 * Collect array-access persistent goals matching the SROA config.
 * @param {number[]} persistent - persistent goal hashes
 * @param {Object} sroaConfig - { arrayPreds: [getPred, setPred], ... }
 * @returns {Array<{ type, hash, arrVar, idx, outVar, val? }>}
 */
function _arrGoals(persistent, sroaConfig) {
  const cfg = sroaConfig;
  const getPred = cfg.arrayPreds[0];
  const setPred = cfg.arrayPreds[1];
  const goals = [];
  for (const p of persistent) {
    const pred = predHead(p);
    if (pred === getPred && Store.arity(p) === 3) {
      goals.push({
        type: 'get',
        hash: p,
        arrVar: Store.child(p, 0),
        idx: Store.child(p, 1),
        outVar: Store.child(p, 2),
      });
    } else if (pred === setPred && Store.arity(p) === 4) {
      goals.push({
        type: 'set',
        hash: p,
        arrVar: Store.child(p, 0),
        idx: Store.child(p, 1),
        val: Store.child(p, 2),
        outVar: Store.child(p, 3),
      });
    }
  }
  return goals;
}

// ── Pipeline pass record (RES_0143 F3) ───────────────────────────────
/** P6: McCarthy acons-peeling + SROA over cc-declared array predicates.
 *  Grounds array-slot bindings → resolveAfter. */
const sroaPass = {
  name: 'sroa',
  phase: 'load/compose/sroa',
  enabled: (ctx) => !!ctx.sroaConfig,
  run(pool, ctx) {
    const r = _sroa(pool, ctx.rc, ctx.getModeMeta, ctx.sroaConfig);
    ctx.diagnostics.sroaTransformed = r.sroaCount;
    ctx.diagnostics.mccarthyNormalized = r.mccarthyCount;
    return { pool: r.rules, meta: {
      sroaTransformed: r.sroaCount, mccarthyNormalized: r.mccarthyCount,
    } };
  },
  resolveAfter: true,
};

export { _sroa as sroa, _mccarthy, _trySROA, sroaPass };
export default { sroa: _sroa, sroaPass };
