/**
 * Grade-0 Cut Elimination — compose rules through !_0 intermediate types.
 *
 * Three-layer API:
 *   L1: cutPair        — atomic cut elimination (grade-agnostic)
 *   L2: predMap   — analysis (producers/consumers/bridges)
 *   L3: compose0       — multi-pass scheduler → ComposeResult
 *
 * All domain-specific knowledge (predicate names, number representation) is
 * injected via configuration objects. See calculus/ill/lib/compose-config.js
 * for the ILL-specific defaults.
 *
 * Theory: stratified cut elimination (THY_0015). SELL cut admissibility
 * (Nigam-Miller PPDP 2009) ensures each cutPair call preserves
 * derivability. Grade-0 erasure (Atkey 2018, Choudhury et al. POPL 2021)
 * justifies that grade-0 intermediates are compile-time scaffolding.
 */

'use strict';

import Store from '../kernel/store.js';
import { unify } from '../kernel/unify.js';
import { apply } from '../kernel/substitute.js';
import { freshMetavar } from '../kernel/fresh.js';
import { flattenAnte, unwrapComp, resolveConn } from './formula-utils.js';
import { predHead, rTensor } from '../kernel/ast.js';
import { collectMetavars, isGround } from './pattern-utils.js';
import { grade0, gradeW, monadUnit } from './grades.js';
import { resolve as _resolveAll, newProf as _newResolveProf } from './resolve-all.js';
// Profiling emission (pure, onPhase-gated) — extracted verbatim to
// compose-profile.js (audit 2026-09-02 readability split).
import { emitTablingProfile } from './compose-profile.js';

// ─── Tabling cache ──────────────────────────────────────────────────────────
// In-memory cache for resolve results. Survives across compose0 calls
// within the same process (helps when multiple test files load the same program).
// Invalidated on Store.clear() via the onClear hook.

const _tablingCache = new Map();
const _composeCache = new Map();
Store.onClear(() => { _tablingCache.clear(); _composeCache.clear(); });

/** Canonical string key for tabling cache — no collision risk (C22). */
function _tablingCacheKey(clauses, definitions) {
  const cParts = [];
  const dParts = [];
  if (clauses) for (const [, cl] of clauses) cParts.push(cl.hash);
  if (definitions) for (const [, dh] of definitions) dParts.push(dh);
  return cParts.join(',') + '|' + dParts.join(',');
}

/** Canonical string key for full compose cache — no collision risk (C22). */
function _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts, hasResolver) {
  const parts = [_tablingCacheKey(clauses, definitions)];
  const rParts = [];
  for (let i = 0; i < compiledRules.length; i++) rParts.push(compiledRules[i].hash);
  parts.push(rParts.join(','));
  if (extraGrade0Facts) {
    const fParts = [];
    for (const [, facts] of extraGrade0Facts) {
      for (const f of facts) fParts.push(f.hash);
    }
    parts.push(fParts.join(','));
  }
  if (hasResolver) parts.push('R');
  return parts.join(';');
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/**
 * TODO_0216 Phase 0 H3 — pool-invariant assertion stub.
 *
 * Dead code by default. When `CALC_POOL_DISJOINT='strict'` is set, every
 * alphaRename site asserts that the rule it's about to rename carries
 * `rule.meta.disjointInPool === true`. Flipped on in Phase 4 (idea B) so
 * any compose entrypoint that forgets to pre-rename the pool is caught
 * at the rename boundary instead of leaking silently.
 */
const _POOL_DISJOINT_STRICT = typeof process !== 'undefined' && process.env.CALC_POOL_DISJOINT === 'strict';
function _assertDisjointInPool(rule, site) {
  if (!_POOL_DISJOINT_STRICT) return;
  if (!rule || !rule.meta || rule.meta.disjointInPool !== true) {
    throw new Error(
      `[TODO_0216 B] alphaRename at ${site}: rule "${rule && rule.name}" ` +
      `is not tagged disjointInPool. Pool-invariant is violated.`
    );
  }
}

// TODO_0216 Phase 4 (idea B): pool-disjoint invariant.
// When enabled, compose0 alpha-renames every rule in a pool ONCE into
// globally-fresh metavar IDs (via existing alphaRename + freshMetavar), tags
// each rule with meta.disjointInPool=true, and the per-pair alphaRename at
// cutPair/specialize/fusePair becomes a no-op for tagged rules.
//
// Invariant: rules in the pool have pairwise-disjoint metavar sets. Unify
// between producer and consumer is safe without per-pair rename.
//
// Default on; set CALC_POOL_DISJOINT=0 to disable for A/B comparison
// (same namespace as the 'strict' assert mode above; the old
// CALC_0216_POOL_DISJOINT spelling was unified in the 2026-09-02 audit).
const _POOL_DISJOINT_ENABLED = typeof process === 'undefined' || process.env.CALC_POOL_DISJOINT !== '0';

/**
 * Alpha-rename all metavars in a formula hash.
 * Returns { hash: freshHash, theta: [[oldMV, newMV], ...] }.
 */
function alphaRename(hash) {
  const mvs = new Set();
  collectMetavars(hash, mvs);
  if (mvs.size === 0) return { hash, theta: [] };
  const theta = [];
  for (const mv of mvs) {
    theta.push([mv, freshMetavar()]);
  }
  return { hash: apply(hash, theta), theta };
}

/**
 * Gate alphaRename: skip when rule is already tagged disjointInPool under
 * the Phase 4 invariant; fall back to the existing rename otherwise.
 *
 * Keeps `_assertDisjointInPool` active so CALC_POOL_DISJOINT=strict still
 * catches untagged rules — the gate changes HOT-path behaviour only.
 */
function _renameForCompose(rule, site) {
  if (_POOL_DISJOINT_ENABLED && rule.meta && rule.meta.disjointInPool === true) {
    return { hash: rule.hash, theta: [] };
  }
  _assertDisjointInPool(rule, site);
  return alphaRename(rule.hash);
}

/**
 * Tag a pool of rules with the pool-disjoint invariant.
 * Each rule gets a one-time alphaRename so its metavars are globally fresh,
 * then meta.disjointInPool = true is set.
 *
 * Idempotent: already-tagged rules are returned unchanged.
 *
 * @param {Array} rules
 * @returns {Array}
 */
function assignDisjointMetavarRanges(rules) {
  if (!_POOL_DISJOINT_ENABLED) return rules;
  const out = new Array(rules.length);
  for (let i = 0; i < rules.length; i++) {
    const r = rules[i];
    if (r.meta && r.meta.disjointInPool === true) {
      out[i] = r;
      continue;
    }
    const { hash: freshHash } = alphaRename(r.hash);
    // NOTE: we only swap `hash` + tag `meta.disjointInPool`.
    //
    // Compiled rules carry a flattened `antecedent`/`consequent` OBJECT plus
    // slot tables and metavar maps derived from the original metavars.
    // Overwriting those with raw-hash children would break `predMap()` and
    // any downstream reader that expects the compiled shape.
    //
    // The compile.js fields go "stale" relative to the renamed hash — the
    // metavars in `metavarSlots`/etc. still point to the pre-rename IDs —
    // but they are NEVER read in compose's hot path: cutPair/fusePair/
    // specialize use `producer.hash` directly and re-flatten from scratch.
    // Accepting the staleness here avoids a full re-compile per rule.
    out[i] = {
      ...r,
      hash: freshHash,
      meta: { ...(r.meta || {}), disjointInPool: true },
    };
  }
  return out;
}

/**
 * Find the first element in arr whose predicate head matches predHead.
 * Returns { index, hash } or null.
 */
function findByPredHead(arr, pred) {
  for (let i = 0; i < arr.length; i++) {
    if (predHead(arr[i]) === pred) {
      return { index: i, hash: arr[i] };
    }
  }
  return null;
}

/**
 * Remove element at index from array, return new array.
 */
function removeAt(arr, idx) {
  const out = new Array(arr.length - 1);
  for (let i = 0, j = 0; i < arr.length; i++) {
    if (i !== idx) out[j++] = arr[i];
  }
  return out;
}

// ─── Rule reassembly ─────────────────────────────────────────────────────────
// Every compose pass (cut elimination, specialization, fusion, SROA) produces
// a new rule from flat antecedent/consequent parts. This helper wraps the
// shared reassembly: bang-wrap persistent/grade-0, tensor-fold, monad-wrap.
//
// Note: the connective shape (bang/tensor/monad/loli) is fixed to SELL-like
// logics. The compose pipeline is generic in predicate names and number
// representations, but assumes this formula structure throughout.

/**
 * Build a loli rule hash from flat antecedent and consequent parts.
 * @param {{ linear: number[], persistent: number[], grade0?: number[] }} ante
 * @param {{ linear: number[], persistent: number[], grade0?: number[] }} conseq
 * @returns {{ hash: number, antecedent: number, consequent: number }}
 */
function _buildRuleHash(ante, conseq, rc) {
  // Structural tags come from the resolved connective table (rc) — REQUIRED
  // (RES_0143 L7: the former shared-surface name fallbacks silently kicked
  // in for rc-less callers; compose always runs under a calculus config,
  // so absence is a caller bug, not a default).
  // The grade unit rides rc.gradeUnit (from cc.gradeUnit via composeOpts);
  // the SELL zero (monadUnit) remains the documented default.
  const { bangTag, monadTag, loliTag } = _requireConnTags(rc, true);
  const anteParts = [
    ...ante.linear,
    ...ante.persistent.map(p => Store.put(bangTag, [gradeW(), p])),
    ...(ante.grade0 || []).map(p => Store.put(bangTag, [grade0(), p])),
  ];
  const anteHash = rTensor(anteParts);
  const conseqParts = [
    ...conseq.linear,
    ...conseq.persistent.map(p => Store.put(bangTag, [gradeW(), p])),
    ...(conseq.grade0 || []).map(p => Store.put(bangTag, [grade0(), p])),
  ];
  const conseqBody = rTensor(conseqParts);
  const conseqHash = Store.put(monadTag, [((rc && rc.gradeUnit) || monadUnit)(), conseqBody]);
  const hash = Store.put(loliTag, [anteHash, conseqHash]);
  return { hash, antecedent: anteHash, consequent: conseqHash };
}

/** Resolved structural tags for compose passes — loud on absence (RES_0143 L7). */
function _requireConnTags(rc, needMonad) {
  const bangTag = rc && rc.exponential;
  const loliTag = rc && rc.implication;
  const monadTag = rc && rc.computation && rc.computation.tag;
  if (!bangTag || !loliTag || (needMonad && !monadTag)) {
    throw new Error('compose: resolved connectives (exponential/implication' +
      (needMonad ? '/computation' : '') + ') are required — build rc via ' +
      'resolveConn(cc.connectives); the engine holds no shared-name fallback');
  }
  return { bangTag, loliTag, monadTag };
}

/**
 * Convenience: build a raw rule object from flat parts + metadata.
 * @param {Object} [flags] - optional flags to spread onto the rule (e.g. { isFused: true })
 *
 * TODO_0216 Phase 4: when pool-disjoint is enabled, every derived rule
 * inherits the invariant. `_makeRule` is only called from compose0 passes
 * (cutPair, specialize, fuse-blocks, fuse-chains, fusePair, fusePairEx,
 * oplus projection), all of which run AFTER `assignDisjointMetavarRanges`
 * has tagged the initial pool. A fused/projected rule's metavars are a
 * subset of its disjoint-tagged inputs, so the output is disjoint from
 * every other pool rule too. Tagging here makes `_renameForCompose`'s
 * short-circuit actually engage on iteration 2+ of chain fusion (where
 * the producer is a prior fusion's output, not an original pool entry).
 */
function _tagDisjoint(rule) {
  if (_POOL_DISJOINT_ENABLED) {
    rule.meta = { ...(rule.meta || {}), disjointInPool: true };
  }
  return rule;
}

function _makeRule(name, ante, conseq, sourceLabel, flags, rc) {
  const { hash, antecedent, consequent } = _buildRuleHash(ante, conseq, rc);
  const rule = { name, hash, antecedent, consequent, sourceLabel: sourceLabel || null };
  if (flags) Object.assign(rule, flags);
  return _tagDisjoint(rule);
}

// ─── Persistent goal ordering ────────────────────────────────────────────────

/**
 * Topologically sort persistent goals so that inputs are grounded before use.
 *
 * After cutPair merges producer + consumer persistent goals, the naive
 * concatenation may violate input→output dependencies. The backward prover
 * resolves goals strictly in order, so we must reorder: goals whose inputs
 * depend on another goal's output come after it.
 *
 * Uses mode metadata (+/- per position) to distinguish inputs from outputs.
 * MultiModal predicates allow at most 1 input position to be ungrounded
 * (it becomes the computed output).
 *
 * @param {number[]} goals - persistent goal hashes (post-theta)
 * @param {number[]} linearPatterns - linear patterns (their metavars are grounded at runtime)
 * @param {Function|null} getModeMeta - (predHead) → { modes: string[], multiModal: boolean } | null
 * @returns {number[]} topologically sorted goals
 */
function sortGoals(goals, linearPatterns, getModeMeta) {
  if (!getModeMeta || goals.length <= 1) return goals;
  const idx = _sortGoalIndices(goals, linearPatterns, getModeMeta, null);
  const out = new Array(idx.length);
  for (let i = 0; i < idx.length; i++) out[i] = goals[idx[i]];
  return out;
}

/**
 * Same topological sort as `sortGoals` but returns an index permutation.
 *
 * The permutation is candidate-invariant across specialization against a
 * ground fact: after substituting θ (whose values are all ground),
 *   post-sub posMVs[j] = pre-sub posMVs[j] \ θ.keys()
 *   post-sub grounded  = pre-sub grounded  \ θ.keys()
 * so running this pre-sub with `extraGrounded = θ.keys()` yields the same
 * order as `sortGoals` post-sub. The outer specialize loop exploits this
 * to compute the permutation once per rule and reuse across all candidates.
 *
 * @param {number[]} goals
 * @param {number[]} linearPatterns
 * @param {Function|null} getModeMeta
 * @param {Set<number>|null} extraGrounded - optional metavars to pre-ground
 * @returns {number[]} permutation — `goals[result[k]]` is the k-th scheduled goal
 */
function _sortGoalIndices(goals, linearPatterns, getModeMeta, extraGrounded) {
  if (!getModeMeta || goals.length <= 1) {
    const identity = new Array(goals.length);
    for (let i = 0; i < goals.length; i++) identity[i] = i;
    return identity;
  }

  // Metavars grounded by linear pattern matching (+ optional extras).
  const grounded = new Set();
  for (const pat of linearPatterns) collectMetavars(pat, grounded);
  if (extraGrounded) for (const mv of extraGrounded) grounded.add(mv);

  // Analyze each goal: per-position metavars + mode info
  const infos = goals.map((goal, originalIdx) => {
    const pred = predHead(goal);
    const meta = pred ? getModeMeta(pred) : null;
    const arity = Store.arity(goal);
    const posMVs = [];
    const allMVs = new Set();
    for (let j = 0; j < arity; j++) {
      const s = new Set();
      collectMetavars(Store.child(goal, j), s);
      posMVs.push(s);
      for (const mv of s) allMVs.add(mv);
    }
    return { originalIdx, meta, arity, posMVs, allMVs };
  });

  // Readiness check: can this goal fire given current grounded set?
  function isReady(info) {
    const { meta, arity, posMVs, allMVs } = info;
    if (!meta || arity !== meta.modes.length) {
      // No mode info — conservative: all metavars must already be grounded
      for (const mv of allMVs) if (!grounded.has(mv)) return false;
      return true;
    }
    let ungroundedInputs = 0;
    for (let j = 0; j < arity; j++) {
      if (meta.modes[j] === '+') {
        for (const mv of posMVs[j]) {
          if (!grounded.has(mv)) { ungroundedInputs++; break; }
        }
      }
    }
    return meta.multiModal ? ungroundedInputs <= 1 : ungroundedInputs === 0;
  }

  // Greedy topological sort
  const scheduledIdx = [];
  const remaining = new Set(infos.map((_, i) => i));
  let progress = true;
  while (progress && remaining.size > 0) {
    progress = false;
    for (const idx of remaining) {
      if (isReady(infos[idx])) {
        scheduledIdx.push(infos[idx].originalIdx);
        remaining.delete(idx);
        for (const mv of infos[idx].allMVs) grounded.add(mv);
        progress = true;
        break; // restart scan — earlier goals may now be ready
      }
    }
  }
  // Append any remaining goals in original order (cycle or unknown modes)
  if (remaining.size > 0) {
    const sorted = [...remaining].sort((a, b) => infos[a].originalIdx - infos[b].originalIdx);
    for (const idx of sorted) scheduledIdx.push(infos[idx].originalIdx);
  }
  return scheduledIdx;
}

// ─── L1: Atomic cut elimination ─────────────────────────────────────────────

/**
 * Compose two rules through a shared cut formula. Grade-agnostic.
 *
 * @param {Object} producer - compiled rule whose consequent grade0[] has cutPredHead
 * @param {Object} consumer - compiled rule whose antecedent grade0[] has cutPredHead
 * @param {string} cutPredHead - predicate head string identifying the cut type
 * @param {Object} rc - resolved connectives (from resolveConn)
 * @param {Function|null} getModeMeta - mode metadata for persistent goal sorting
 * @returns {Object|null} raw rule { name, hash, antecedent, consequent, sourceLabel } or null
 */
function cutPair(producer, consumer, cutPredHead, rc, getModeMeta) {
  // Step 1: Alpha-rename producer to prevent metavar collision.
  // We rename the full loli hash, then re-derive ante/conseq.
  const { hash: freshProdHash } = _renameForCompose(producer, 'cutPair');
  const freshProdAnte = Store.child(freshProdHash, 0);
  const freshProdConseq = Store.child(freshProdHash, 1);

  // Step 2: Flatten both sides.
  // NOTE: compiled.antecedent is the flattened object, not a hash.
  // We derive raw hashes from compiled.hash (the full loli formula).
  const pAnte = flattenAnte(freshProdAnte, rc);
  const pConseqBody = unwrapComp(freshProdConseq, rc);
  const pConseq = flattenAnte(pConseqBody, rc);

  const consumerAnteHash = Store.child(consumer.hash, 0);
  const consumerConseqHash = Store.child(consumer.hash, 1);
  const cAnte = flattenAnte(consumerAnteHash, rc);
  const cConseqBody = unwrapComp(consumerConseqHash, rc);
  const cConseq = flattenAnte(cConseqBody, rc);

  // Step 3: Locate cut formula in producer's conseq.grade0 and consumer's ante.grade0.
  const pMatch = findByPredHead(pConseq.grade0, cutPredHead);
  const cMatch = findByPredHead(cAnte.grade0, cutPredHead);
  if (!pMatch || !cMatch) return null;

  // Step 4: Unify the cut formulas.
  const theta = unify(pMatch.hash, cMatch.hash);
  if (theta === null) return null;

  // Step 5: Apply θ and merge, removing the cut formula from each side.
  const pConseqGrade0Rest = removeAt(pConseq.grade0, pMatch.index);
  const cAnteGrade0Rest = removeAt(cAnte.grade0, cMatch.index);

  const applyAll = arr => arr.map(h => apply(h, theta));

  const combinedAnteLinear = applyAll([...pAnte.linear, ...cAnte.linear]);
  const combinedAntePersistent = sortGoals(
    applyAll([...pAnte.persistent, ...cAnte.persistent]),
    combinedAnteLinear,
    getModeMeta
  );
  const combinedAnteGrade0 = applyAll([...pAnte.grade0, ...cAnteGrade0Rest]);

  const combinedConseqLinear = applyAll([...pConseq.linear, ...cConseq.linear]);
  const combinedConseqPersistent = applyAll([...pConseq.persistent, ...cConseq.persistent]);
  const combinedConseqGrade0 = applyAll([...pConseqGrade0Rest, ...cConseq.grade0]);

  // Step 6: Reassemble and return raw rule.
  return _makeRule(
    `${consumer.name}:${producer.name}`,
    { linear: combinedAnteLinear, persistent: combinedAntePersistent, grade0: combinedAnteGrade0 },
    { linear: combinedConseqLinear, persistent: combinedConseqPersistent, grade0: combinedConseqGrade0 },
    consumer.sourceLabel || producer.sourceLabel,
    undefined, rc
  );
}

/**
 * Specialize a rule by resolving a persistent goal against a ground grade-0 clause.
 * Separate from cutPair — different semantics (ground fact × rule, not rule × rule).
 *
 * @param {Object} rule - Rule with .hash (loli formula) and .name
 * @param {number} factHash - Ground clause hash
 * @param {string} factName - Clause name
 * @param {string} pred - Predicate head to resolve
 * @param {Object} rc - Resolved connectives
 * @param {Function|null} getModeMeta - Mode metadata for persistent goal sorting
 * @returns {Object|null} Raw rule { name, hash, antecedent, consequent, sourceLabel } or null
 */
function specialize(rule, factHash, factName, pred, rc, getModeMeta) {
  const ctx = _specializeContext(rule, pred, rc, getModeMeta);
  if (!ctx) return null;
  return _specializeFromContext(ctx, factHash, factName);
}

/**
 * Build the rule-invariant setup needed by `_specializeFromContext`. Returns
 * null if `rule` has no persistent goal matching `pred`.
 *
 * Hoisted out of `specialize()` so the outer multi-stage loop can compute the
 * setup once per (rule, pred) and iterate all fact candidates without repeating
 * rename + flatten + findGoal + sortGoal permutation (TODO_0217).
 */
function _specializeContext(rule, pred, rc, getModeMeta) {
  const { hash: freshRuleHash } = _renameForCompose(rule, 'specialize');
  const freshAnteHash = Store.child(freshRuleHash, 0);
  const freshConseqHash = Store.child(freshRuleHash, 1);

  const ante = flattenAnte(freshAnteHash, rc);
  const goalMatch = findByPredHead(ante.persistent, pred);
  if (!goalMatch) return null;

  const conseqBody = unwrapComp(freshConseqHash, rc);
  const conseq = flattenAnte(conseqBody, rc);
  const remainingPersistent = removeAt(ante.persistent, goalMatch.index);

  // Seed `extraGrounded` with goalHash's metavars: a ground-fact unification
  // grounds exactly those keys. See _sortGoalIndices JSDoc for invariance proof.
  const goalKeys = new Set();
  collectMetavars(goalMatch.hash, goalKeys);
  const sortedIdx = _sortGoalIndices(remainingPersistent, ante.linear, getModeMeta, goalKeys);

  return {
    name: rule.name,
    sourceLabel: rule.sourceLabel,
    ante,
    conseq,
    goalMatchHash: goalMatch.hash,
    remainingPersistent,
    sortedIdx,
    rc,
  };
}

/**
 * Per-candidate specialization step — only does the θ-dependent work:
 * unify with the fact, apply θ to every array, reassemble via _makeRule.
 * The sort permutation from `ctx` is reused instead of re-sorting post-sub.
 */
function _specializeFromContext(ctx, factHash, factName) {
  const theta = unify(ctx.goalMatchHash, factHash);
  if (theta === null) return null;

  const { ante, conseq, remainingPersistent, sortedIdx } = ctx;

  const applyArr = arr => {
    const out = new Array(arr.length);
    for (let i = 0; i < arr.length; i++) out[i] = apply(arr[i], theta);
    return out;
  };

  const subRemaining = applyArr(remainingPersistent);
  const combinedAntePersistent = new Array(sortedIdx.length);
  for (let i = 0; i < sortedIdx.length; i++) combinedAntePersistent[i] = subRemaining[sortedIdx[i]];

  return _makeRule(
    `${ctx.name}:${factName}`,
    {
      linear: applyArr(ante.linear),
      persistent: combinedAntePersistent,
      grade0: applyArr(ante.grade0),
    },
    {
      linear: applyArr(conseq.linear),
      persistent: applyArr(conseq.persistent),
      grade0: applyArr(conseq.grade0),
    },
    ctx.sourceLabel,
    undefined, ctx.rc
  );
}

// ─── L2: Analysis ───────────────────────────────────────────────────────────

/**
 * Extract grade-0 predicate heads from a compiled rule's flattened arrays.
 * @param {Object} compiled - compiled rule with antecedent.grade0[] and consequent.grade0[]
 * @returns {{ produced: string[], consumed: string[] }}
 */
function getGrade0Roles(compiled) {
  const produced = new Set();
  const consumed = new Set();

  const anteG0 = compiled.antecedent.grade0 || [];
  for (const h of anteG0) {
    const pred = predHead(h);
    if (pred) consumed.add(pred);
  }

  // consequent.grade0 comes from the expanded consequent (effectiveConseq)
  const conseqG0 = compiled.consequent.grade0 || [];
  for (const h of conseqG0) {
    const pred = predHead(h);
    if (pred) produced.add(pred);
  }

  return { produced: [...produced], consumed: [...consumed] };
}

/**
 * Build grade-0 predicate map from compiled rules.
 *
 * @param {Object[]} compiledRules
 * @returns {Map<string, { producers: Object[], consumers: Object[], bridges: Object[] }>}
 */
function predMap(compiledRules) {
  const map = new Map();

  function ensure(pred) {
    if (!map.has(pred)) map.set(pred, { producers: [], consumers: [], bridges: [] });
    return map.get(pred);
  }

  // First pass: classify producers and consumers per predicate.
  for (const r of compiledRules) {
    if (!r.hasGrade0) continue;
    const { produced, consumed } = getGrade0Roles(r);
    for (const p of produced) ensure(p).producers.push(r);
    for (const c of consumed) ensure(c).consumers.push(r);
  }

  // Second pass: detect bridges — rules that consume pred A and produce pred B.
  for (const r of compiledRules) {
    if (!r.hasGrade0) continue;
    const { produced, consumed } = getGrade0Roles(r);
    if (produced.length > 0 && consumed.length > 0) {
      // Rule crosses grade-0 predicates — it's a bridge for all involved preds
      const allPreds = new Set([...produced, ...consumed]);
      for (const p of allPreds) ensure(p).bridges.push(r);
    }
  }

  return map;
}

// ─── Fact indexing ──────────────────────────────────────────────────────────
// For predicates with many grade-0 facts, O(N) brute-force specialize
// calls per rule dominate compile time. Index facts by argument values for O(1)
// lookup. Threshold: 8+ facts before indexing (below that, linear scan is faster).

/**
 * Build per-position argument indexes for a set of grade-0 facts.
 * @param {Array} facts - [{name, hash}]
 * @returns {Array|null} posIndexes[pos] = Map<argHash, [fact]> or null if not selective
 */
function _factIndex(facts) {
  if (facts.length < 8) return null;

  const arity = Store.arity(facts[0].hash);
  if (arity === 0) return null;

  const indexes = [];
  let anySelective = false;
  for (let pos = 0; pos < arity; pos++) {
    const idx = new Map();
    for (const f of facts) {
      const key = Store.child(f.hash, pos);
      if (!idx.has(key)) idx.set(key, []);
      idx.get(key).push(f);
    }
    if (idx.size > 1) {
      indexes.push(idx);
      anySelective = true;
    } else {
      indexes.push(null);
    }
  }

  return anySelective ? indexes : null;
}

/**
 * Look up matching facts using the argument index.
 * Finds the most selective indexed position where the goal has a ground arg.
 * @param {Array} posIndexes - from _factIndex
 * @param {number} goalHash - persistent goal hash
 * @returns {Array|null} matching facts, or null to fall back to brute force
 */
function _indexLookup(posIndexes, goalHash) {
  const goalArity = Store.arity(goalHash);
  let best = null;

  for (let pos = 0; pos < goalArity && pos < posIndexes.length; pos++) {
    const idx = posIndexes[pos];
    if (!idx) continue;

    const goalArg = Store.child(goalHash, pos);
    if (typeof goalArg !== 'number' || Store.tag(goalArg) === 'metavar') continue;

    const hits = idx.get(goalArg);
    if (!hits) return []; // Ground arg with no matching fact → empty result
    if (!best || hits.length < best.length) best = hits;
  }

  return best;
}

// ─── Additive chain fusion ───────────────────────────────────────────────────
// (moved to opt/compose-fuse.js — RES_0143 M4: P5.5 is an optimization
// pass; compose0 receives it via composeOpts.fusePasses.)

// ─── Residual persistent resolution ─────────────────────────────────────────
// After specialization and fusion, rules may still have persistent goals whose
// inputs are all ground. A residualResolver callback computes their outputs at
// compile time, propagating groundness to dependent goals via running theta.

/**
 * Resolve ALL residual persistent goals on a single rule in one pass.
 *
 * Pre-sorts goals topologically (via sortGoals) so that each goal's
 * inputs are grounded before it's attempted. A running theta composition
 * propagates bindings: resolving goal A may ground the input of goal B.
 *
 * No alpha-rename needed: resolver returns fully ground facts, so no metavar
 * collision with the rule's own metavars is possible.
 *
 * @param {Object} rule - raw rule {name, hash, ...}
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta - mode metadata for persistent goal sorting
 * @param {Function} resolver - (goalHash) → factHash | null
 * @returns {Object} updated rule (same object if nothing resolved)
 */
function _resolveOnce(rule, rc, getModeMeta, resolver) {
  const anteHash = Store.child(rule.hash, 0);
  const conseqHash = Store.child(rule.hash, 1);
  const ante = flattenAnte(anteHash, rc);
  const conseqBody = unwrapComp(conseqHash, rc);
  const conseq = flattenAnte(conseqBody, rc);

  // Sort goals so inputs are grounded before dependent goals are attempted.
  // This ensures the running theta propagates correctly through chains like
  // f(GROUND, ?Y) → g(?Y, ?Z) → h(?Z, ?W).
  //
  // Single-sort invariant: the filtered+θ-applied remaining goals stay
  // topologically sorted without a second sortGoals pass, because
  //   (a) filtering a topologically sorted sequence preserves topological order
  //       (removing nodes can't introduce new dependencies), and
  //   (b) θ from resolver unification carries only ground values, so post-θ
  //       each remaining goal's metavar set only shrinks — readiness can
  //       only improve, never degrade.
  // See _sortGoalIndices JSDoc for the permutation invariance proof.
  const sortedGoals = sortGoals(ante.persistent, ante.linear, getModeMeta);

  // Track which POSITIONS in sortedGoals resolved (avoids Map + dedupe bookkeeping).
  const resolvedSortedIdx = new Set();
  const resolvedPreds = [];
  let combinedTheta = [];

  for (let k = 0; k < sortedGoals.length; k++) {
    const goal = sortedGoals[k];
    const applied = apply(goal, combinedTheta);
    const factHash = resolver(applied);
    if (factHash === null) continue;

    const theta_i = unify(applied, factHash);
    if (theta_i === null) continue;

    // Compose theta_i into combinedTheta (idempotent substitution composition)
    for (let j = 0; j < combinedTheta.length; j++) {
      combinedTheta[j][1] = apply(combinedTheta[j][1], theta_i);
    }
    for (const [mv, val] of theta_i) {
      if (!combinedTheta.find(([m]) => m === mv)) combinedTheta.push([mv, val]);
    }
    resolvedSortedIdx.add(k);
    resolvedPreds.push(predHead(goal) || 'unknown');
  }

  if (resolvedSortedIdx.size === 0) return rule;

  // Apply combined theta and reassemble — ONCE
  const applyAll = arr => arr.map(h => apply(h, combinedTheta));

  const resolvedSuffix = resolvedPreds.length > 0
    ? ':resolved:' + resolvedPreds.join(':resolved:')
    : '';

  // Build final persistent goals by walking sortedGoals in order, skipping
  // resolved entries. Order is already topological — no resort needed.
  const finalPersistent = new Array(sortedGoals.length - resolvedSortedIdx.size);
  let _wi = 0;
  for (let k = 0; k < sortedGoals.length; k++) {
    if (resolvedSortedIdx.has(k)) continue;
    finalPersistent[_wi++] = apply(sortedGoals[k], combinedTheta);
  }

  return _makeRule(
    rule.name + resolvedSuffix,
    {
      linear: applyAll(ante.linear),
      persistent: finalPersistent,
      grade0: applyAll(ante.grade0),
    },
    {
      linear: applyAll(conseq.linear),
      persistent: applyAll(conseq.persistent),
      grade0: applyAll(conseq.grade0),
    },
    rule.sourceLabel,
    undefined, rc
  );
}

// ─── Basic block fusion ──────────────────────────────────────────────────────
// (moved to opt/compose-fuse.js — RES_0143 M4: P5 is an optimization
// pass; compose0 receives it via composeOpts.fusePasses.)

// ─── Pass 6: SROA + McCarthy ─────────────────────────────────────────────────
// (moved to opt/compose-sroa.js — RES_0143 M4: P6 is an optimization
// pass; compose0 receives it via composeOpts.fusePasses.)

// ─── L2.5: Elimination ordering ─────────────────────────────────────────────

/**
 * Build topological elimination order for grade-0 persistent predicates.
 * Uses Kahn's algorithm for cycle detection + topological sort.
 *
 * Direction: if predicates A and B co-occur as persistent goals in some rule
 * and share a metavar, the one with fewer metavars (more ground/constraining)
 * comes first. Independent predicates are included in arbitrary order.
 *
 * @param {Map} grade0Facts - predHead → [{name, hash}]
 * @param {Object[]} rules - rules with .hash (loli formula)
 * @param {Object} rc - resolved connectives
 * @returns {string[]} elimination order (predicates to specialize, earliest first)
 */
function elimOrder(grade0Facts, rules, rc) {
  const preds = [...grade0Facts.keys()];
  if (preds.length <= 1) return preds;

  const predSet = new Set(preds);
  const adj = new Map();     // pred → Set<pred> (successors)
  const inDeg = new Map();   // pred → incoming edge count
  for (const p of preds) { adj.set(p, new Set()); inDeg.set(p, 0); }

  // Analyze co-occurring grade-0 persistent goals in each rule
  for (const rule of rules) {
    const ante = flattenAnte(Store.child(rule.hash, 0), rc);
    const g0Goals = [];
    for (const goal of ante.persistent) {
      const pred = predHead(goal);
      if (pred && predSet.has(pred)) {
        const mvs = new Set();
        collectMetavars(goal, mvs);
        g0Goals.push({ pred, mvs });
      }
    }
    if (g0Goals.length < 2) continue;

    // For each pair, add edge from more-ground to less-ground
    for (let i = 0; i < g0Goals.length; i++) {
      for (let j = i + 1; j < g0Goals.length; j++) {
        let shared = false;
        for (const mv of g0Goals[i].mvs) {
          if (g0Goals[j].mvs.has(mv)) { shared = true; break; }
        }
        if (!shared) continue;

        const a = g0Goals[i], b = g0Goals[j];
        if (a.mvs.size < b.mvs.size) {
          if (!adj.get(a.pred).has(b.pred)) {
            adj.get(a.pred).add(b.pred);
            inDeg.set(b.pred, inDeg.get(b.pred) + 1);
          }
        } else if (b.mvs.size < a.mvs.size) {
          if (!adj.get(b.pred).has(a.pred)) {
            adj.get(b.pred).add(a.pred);
            inDeg.set(a.pred, inDeg.get(a.pred) + 1);
          }
        }
        // Equal metavar count: no ordering constraint
      }
    }
  }

  // Kahn's algorithm
  const queue = [];
  for (const [p, deg] of inDeg) {
    if (deg === 0) queue.push(p);
  }

  const order = [];
  while (queue.length > 0) {
    const p = queue.shift();
    order.push(p);
    for (const next of adj.get(p)) {
      const newDeg = inDeg.get(next) - 1;
      inDeg.set(next, newDeg);
      if (newDeg === 0) queue.push(next);
    }
  }

  if (order.length < preds.length) {
    const inCycle = preds.filter(p => !order.includes(p));
    throw new Error(
      `Grade-0 persistent predicate cycle: ${inCycle.join(', ')} — ` +
      `cannot determine elimination order`
    );
  }

  return order;
}

// ─── L3: Orchestration ──────────────────────────────────────────────────────

/**
 * Grade-0 cut elimination: multi-stage composition (THY_0015, TODO_0160).
 *
 * Pass 1: Linear composition via cutPair (grade-0 types in antecedent/consequent)
 * Pass 2: Multi-stage persistent specialization via specialize.
 *         Builds dependency DAG → Kahn's topological sort → stage-by-stage elimination.
 *         Includes tabling: grade-0 clauses with premises are resolved via
 *         compile-time backward proof search (TODO_0160).
 *
 * @param {Object[]} compiledRules - all compiled rules (some with hasGrade0)
 * @param {Object} connectives - connective table (e.g. illConnectives())
 * @param {Function|null} getModeMeta - mode metadata for persistent goal ordering
 * @param {Map|null} clauses - backward clause map (some with grade0: true)
 * @param {Map|null} definitions - backward definitions map (zero-premise axioms)
 * @param {Map|null} extraGrade0Facts - externally-provided grade-0 facts (predHead → [{name, hash}])
 * @param {Function|null} scopeGuard - (rule, pred, goalHash, flatAnte) → boolean; false = skip specialization
 * @param {Object} [opts] - Additional options
 * @param {Function|null} [opts.residualResolver] - (goalHash) → factHash | null; resolve persistent goals at compile time
 * @param {boolean} [opts.fuseBasicBlocks] - Enable linear basic block fusion
 * @param {string} [opts.linearFusionPredicate] - threading predicate for block fusion (required if fuseBasicBlocks)
 * @param {ChainConfig[]} [opts.chainFusionPredicates] - chain fusion descriptors
 * @param {Object} [opts.sroaConfig] - SROA configuration { arrayPreds, resourcePred, parseIndex, buildIndex }
 * @returns {{ composedRules: Object[], removedNames: Set, predicateMap: Map, diagnostics: Object }}
 */
function compose0(compiledRules, connectives, getModeMeta, clauses, definitions, extraGrade0Facts, scopeGuard, opts) {
  const o = opts || {};
  const residualResolver = o.residualResolver || null;
  // Optimization passes (P5/P5.5/P6) are INJECTED via o.fusePasses from
  // the composition root (opt/compose-fuse.js + opt/compose-sroa.js,
  // RES_0143 M4) — semantic passes (P1-P4) live here; fusion is opt-in
  // twice (the doFuse flag AND the injected pass record).
  const doFuse = o.fuseBasicBlocks || false;
  const skipSpecialize = o.skipSpecialize === true;
  const chainConfigs = o.chainFusionPredicates || null;
  const linearFusionPredicate = o.linearFusionPredicate || null;
  const sroaConfig = o.sroaConfig || null;
  const canonicalize = o.canonicalize || null;
  const backchainOpts = o.backchainOpts || {};
  const ffiContext = o.ffiContext || null;
  const ffiDirect = o.ffiDirect || null;
  const fusionBarriers = o.fusionBarriers || null;
  const onPhase = o.onPhase || null;
  const _pStart = () => onPhase ? performance.now() : 0;
  const _pEnd = (name, t, meta) => { if (onPhase) onPhase(name, performance.now() - t, meta); };
  const _pEmit = (name, ms, meta) => { if (onPhase) onPhase(name, ms, meta); };

  // Full-result cache: all compose outputs are deterministic for the same Store content.
  // Key covers clauses + definitions + forwardRules (via compiledRules hashes).
  const fullKey = _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts, !!residualResolver || doFuse);
  const fullCached = _composeCache.get(fullKey);
  if (fullCached) return fullCached;

  const rc = resolveConn(connectives);
  // Grade unit of the computation (cc.gradeUnit) — threaded onto rc so
  // _buildRuleHash mints composed consequents with the calculus's own
  // unit rather than the SELL default (RES_0143 L7).
  if (o.gradeUnit) rc.gradeUnit = o.gradeUnit;
  const diagnostics = {
    pairsAttempted: 0,
    pairsSucceeded: 0,
    pairsSkipped: 0,
    specializations: 0,
    grade0Predicates: [],
    errors: [],
  };

  // TODO_0216 Phase 4 (idea B): pool-disjoint invariant.
  // One pre-rename pass so per-pair alphaRename becomes a no-op inside
  // cutPair/specialize/fusePair. Idempotent + gated — no-op when
  // CALC_POOL_DISJOINT=0.
  compiledRules = assignDisjointMetavarRanges(compiledRules);

  // ── Pass 1: Linear composition (grade-0 types) ────────────────────

  const _tPass1 = _pStart();
  const predicateMap = predMap(compiledRules);

  let pass1Rules = [];
  if (predicateMap.size > 0) {
    // Validation
    for (const [pred, entry] of predicateMap) {
      diagnostics.grade0Predicates.push(pred);
      if (entry.producers.length === 0) {
        diagnostics.errors.push(
          `Grade-0 type '${pred}' is consumed but never produced`
        );
      }
      if (entry.consumers.length === 0) {
        diagnostics.errors.push(
          `Grade-0 type '${pred}' is produced but never consumed`
        );
      }
      if (entry.bridges.length > 0) {
        const bridgeNames = entry.bridges.map(r => r.name).join(', ');
        diagnostics.errors.push(
          `Grade-0 type '${pred}' has bridge rules (${bridgeNames}) — ` +
          `bridge composition not yet supported`
        );
      }
    }

    if (diagnostics.errors.length === 0) {
      for (const [pred, entry] of predicateMap) {
        for (const producer of entry.producers) {
          for (const consumer of entry.consumers) {
            diagnostics.pairsAttempted++;
            const result = cutPair(producer, consumer, pred, rc, getModeMeta);
            if (result) {
              pass1Rules.push(result);
              diagnostics.pairsSucceeded++;
            } else {
              diagnostics.pairsSkipped++;
            }
          }
        }
      }
    }

    // Defense-in-depth: filter pass-1 rules with grade-0 residuals
    const validPass1 = [];
    for (const raw of pass1Rules) {
      const anteFlat = flattenAnte(Store.child(raw.hash, 0), rc);
      const conseqBody = unwrapComp(Store.child(raw.hash, 1), rc);
      const conseqFlat = flattenAnte(conseqBody, rc);
      if (anteFlat.grade0.length > 0 || conseqFlat.grade0.length > 0) {
        diagnostics.errors.push(
          `Composed rule '${raw.name}' still has grade-0 residuals — ` +
          `bridge composition required for multi-predicate grade-0`
        );
      } else {
        validPass1.push(raw);
      }
    }
    pass1Rules = validPass1;
  }
  _pEnd('load/compose/pass1-linear', _tPass1, {
    predicates: predicateMap.size,
    pairsAttempted: diagnostics.pairsAttempted,
    pairsSucceeded: diagnostics.pairsSucceeded,
    pairsSkipped: diagnostics.pairsSkipped,
    validationErrors: diagnostics.errors.length,
    pass1RulesOut: pass1Rules.length,
  });

  // ── Pass 2: Persistent specialization (grade-0 clause facts) ──────

  // Collect grade-0 clauses grouped by predicate head.
  // Clauses WITH premises are resolved via compile-time tabling (TODO_0160).
  // Uses in-memory cache to skip resolve on repeated loads.
  const _tGrade0 = _pStart();
  const grade0Facts = new Map(); // predHead → [{name, hash}, ...]
  let _tEnumAcc = 0;
  let _tTabAcc = 0;
  let _simpleFacts = 0;
  let _premiseClauses = 0;
  let _tablingSolutions = 0;
  let _tablingErrors = 0;
  let _grade0CacheHit = false;

  // ── Profiling accumulators (only populated when onPhase is set) ─────
  // _tabResolveProf is shared across every _resolveAll call so we get one
  // aggregated counter set for the entire tabling block.
  // _tabPerClause records wall-clock + shape of each tabled clause for later
  // top-K / histogram computation.
  const _tabResolveProf = onPhase ? _newResolveProf() : null;
  const _tabPerClause = onPhase ? [] : null;
  // Extra sub-phase accumulators measured directly in this block (outside
  // _resolveAll), so every ms of tabling wall-clock is attributable:
  let _tabApplyHeadMs = 0;      // apply(clause.hash, solution) per produced fact
  let _tabCanonMs = 0;          // canonicalize() per produced fact
  let _tabOverheadErr = 0;      // try/catch overhead charges for errored clauses
  let _tabProducedFacts = 0;    // number of fact hashes produced (solutions materialized)

  if (clauses) {
    const tabKey = _tablingCacheKey(clauses, definitions);
    const tabCached = _tablingCache.get(tabKey);

    if (tabCached) {
      // Cache hit — restore grade0Facts
      _grade0CacheHit = true;
      for (const [pred, facts] of tabCached.facts) {
        grade0Facts.set(pred, [...facts]);
      }
      diagnostics.tablings = tabCached.tablings;
    } else {
      for (const [name, clause] of clauses) {
        if (!clause.grade0) continue;
        const head = predHead(clause.hash);
        if (!head) continue;
        if (!grade0Facts.has(head)) grade0Facts.set(head, []);

        if (clause.premises && clause.premises.length > 0) {
          // Tabling: enumerate all ground solutions via backward proof search
          const _tTab0 = onPhase ? performance.now() : 0;
          _premiseClauses++;
          let _clauseSolutions = 0;
          let _clauseErrored = false;
          // Snapshot resolver counters so per-clause meta can report its own delta
          const _snap = onPhase ? {
            searchNodes: _tabResolveProf.searchNodes,
            unifyAttempts: _tabResolveProf.unifyAttempts,
          } : null;
          try {
            const solutions = _resolveAll(
              clause.premises, clauses, definitions || new Map(),
              { maxSolutions: 10000, canonicalize, backchainOpts,
                ffiContext, ffiDirect, prof: _tabResolveProf }
            );
            for (let i = 0; i < solutions.length; i++) {
              const _tApH0 = onPhase ? performance.now() : 0;
              let fact = apply(clause.hash, solutions[i]);
              if (onPhase) _tabApplyHeadMs += performance.now() - _tApH0;
              if (canonicalize) {
                const _tCn0 = onPhase ? performance.now() : 0;
                fact = canonicalize(fact);
                if (onPhase) _tabCanonMs += performance.now() - _tCn0;
              }
              grade0Facts.get(head).push({
                name: `${name}:${i}`,
                hash: fact,
              });
              if (onPhase) _tabProducedFacts++;
            }
            _tablingSolutions += solutions.length;
            _clauseSolutions = solutions.length;
            diagnostics.tablings = (diagnostics.tablings || 0) + solutions.length;
          } catch (e) {
            _tablingErrors++;
            _clauseErrored = true;
            if (onPhase) _tabOverheadErr++;
            diagnostics.errors.push(`Tabling '${name}': ${e.message}`);
          }
          if (onPhase) {
            const _elapsed = performance.now() - _tTab0;
            _tTabAcc += _elapsed;
            _tabPerClause.push({
              name,
              ms: _elapsed,
              solutions: _clauseSolutions,
              premises: clause.premises.length,
              errored: _clauseErrored,
              searchNodes: _tabResolveProf.searchNodes - _snap.searchNodes,
              unifyAttempts: _tabResolveProf.unifyAttempts - _snap.unifyAttempts,
            });
          }
        } else {
          const _tEn0 = onPhase ? performance.now() : 0;
          grade0Facts.get(head).push({ name, hash: clause.hash });
          _simpleFacts++;
          if (onPhase) _tEnumAcc += performance.now() - _tEn0;
        }
      }

      // Cache for subsequent loads
      const toCache = new Map();
      for (const [pred, facts] of grade0Facts) toCache.set(pred, [...facts]);
      _tablingCache.set(tabKey, { facts: toCache, tablings: diagnostics.tablings || 0 });
    }
  }

  // Merge externally-provided grade-0 facts (e.g., from a domain-specific loader)
  let _extrasMerged = 0;
  let _extrasFactCount = 0;
  if (extraGrade0Facts) {
    for (const [pred, facts] of extraGrade0Facts) {
      if (!grade0Facts.has(pred)) grade0Facts.set(pred, []);
      const existing = grade0Facts.get(pred);
      for (const f of facts) { existing.push(f); _extrasFactCount++; }
      _extrasMerged++;
    }
  }
  const _totalGrade0Facts = [...grade0Facts.values()].reduce((n, a) => n + a.length, 0);
  _pEnd('load/compose/grade0-facts', _tGrade0, {
    predicatesProduced: grade0Facts.size,
    simpleFacts: _simpleFacts,
    premiseClauses: _premiseClauses,
    tablingSolutions: _tablingSolutions,
    tablingErrors: _tablingErrors,
    cacheHit: _grade0CacheHit,
    extrasPredicates: _extrasMerged,
    extrasFacts: _extrasFactCount,
    totalFacts: _totalGrade0Facts,
  });
  if (!_grade0CacheHit) {
    _pEmit('load/compose/grade0-facts/enumerate', _tEnumAcc, { simpleFacts: _simpleFacts });
  }
  if (!_grade0CacheHit && onPhase) {
    emitTablingProfile(_pEmit, {
      rp: _tabResolveProf, perClause: _tabPerClause, tTabAcc: _tTabAcc,
      premiseClauses: _premiseClauses, tablingSolutions: _tablingSolutions,
      tablingErrors: _tablingErrors, producedFacts: _tabProducedFacts,
      applyHeadMs: _tabApplyHeadMs, canonMs: _tabCanonMs, canonicalize,
    });
  }

  const removedNames = new Set();
  let specializedPool = [];

  const _tSpecialize = _pStart();
  let _specStages = 0;
  let _specOrderMs = 0;
  let _specPoolInitial = 0;
  let _specPass1ForSpec = 0;
  let _specCompiledForSpec = 0;
  if (grade0Facts.size > 0 && !skipSpecialize) {
    // ── Pool: collect all rules eligible for persistent specialization ──

    // Separate pass-1 outputs into those needing specialization and those that don't
    const pass1ForSpec = [];
    const pass1Direct = [];
    for (const raw of pass1Rules) {
      const ante = flattenAnte(Store.child(raw.hash, 0), rc);
      let hasG0Goal = false;
      for (const goal of ante.persistent) {
        const pred = predHead(goal);
        if (pred && grade0Facts.has(pred)) { hasG0Goal = true; break; }
      }
      (hasG0Goal ? pass1ForSpec : pass1Direct).push(raw);
    }

    // Add compiledRules with grade-0 persistent goals (not handled in Pass 1)
    const compiledForSpec = [];
    for (const rule of compiledRules) {
      if (rule.hasGrade0) continue;
      if (removedNames.has(rule.name)) continue;
      const persistent = rule.antecedent.persistent || [];
      let hasG0Goal = false;
      for (const goal of persistent) {
        const pred = predHead(goal);
        if (pred && grade0Facts.has(pred)) { hasG0Goal = true; break; }
      }
      if (hasG0Goal) {
        compiledForSpec.push(rule);
        removedNames.add(rule.name);
      }
    }

    let pool = [...pass1ForSpec, ...compiledForSpec];
    _specPass1ForSpec = pass1ForSpec.length;
    _specCompiledForSpec = compiledForSpec.length;
    _specPoolInitial = pool.length;

    // ── Elimination order: dependency DAG + Kahn's topological sort ──

    const _tOrder = onPhase ? performance.now() : 0;
    const order = elimOrder(grade0Facts, pool, rc);
    if (onPhase) _specOrderMs = performance.now() - _tOrder;
    for (const pred of order) {
      diagnostics.grade0Predicates.push(pred);
    }

    // ── Multi-stage specialization: one predicate per stage ──

    const MAX_COMPOSED_PER_STAGE = 100000;

    for (const pred of order) {
      const facts = grade0Facts.get(pred);
      if (!facts || facts.length === 0) continue;

      const _tStage = onPhase ? performance.now() : 0;
      _specStages++;

      // Build argument index for O(1) fact lookup (critical for large fact sets)
      const factIndex = _factIndex(facts);

      let _stageSpecializations = 0;
      let _stageCandidates = 0;
      let _stageGuarded = 0;
      let _stageMatched = 0;
      const _stageRulesIn = pool.length;
      const nextPool = [];
      for (const rule of pool) {
        const ante = flattenAnte(Store.child(rule.hash, 0), rc);
        const goalMatch = findByPredHead(ante.persistent, pred);

        if (!goalMatch) {
          nextPool.push(rule); // pass through — no matching goal
          continue;
        }
        _stageMatched++;

        // Scoping guard: caller can reject specialization for specific rule/pred combos.
        // Passes the ORIGINAL flattened ante (pre-rename) so guard callbacks that
        // inspect metavar identities see stable hashes.
        if (scopeGuard && !scopeGuard(rule, pred, goalMatch.hash, ante)) {
          nextPool.push(rule); // pass through — scoping guard rejected
          diagnostics.scopeGuarded = (diagnostics.scopeGuarded || 0) + 1;
          _stageGuarded++;
          continue;
        }

        // Use indexed lookup when available (O(1) vs O(N) for large fact sets)
        const candidates = factIndex
          ? (_indexLookup(factIndex, goalMatch.hash) || facts)
          : facts;
        _stageCandidates += candidates.length;
        if (candidates.length === 0) continue;

        // Rule-invariant setup (rename + flatten + findGoal + sort permutation)
        // is hoisted out of the fact loop — θ-dependent work only runs inside.
        const ctx = _specializeContext(rule, pred, rc, getModeMeta);

        for (const fact of candidates) {
          let result = _specializeFromContext(ctx, fact.hash, fact.name);
          if (result) {
            // Transitive resolution: resolve goals that became ground after specialization
            if (residualResolver) {
              result = _resolveOnce(result, rc, getModeMeta, residualResolver);
            }
            nextPool.push(result);
            diagnostics.specializations++;
            _stageSpecializations++;
          }
        }
      }

      if (onPhase) {
        _pEmit(`load/compose/specialize/stage/${pred}`, performance.now() - _tStage, {
          facts: facts.length,
          rulesIn: _stageRulesIn,
          rulesMatched: _stageMatched,
          candidates: _stageCandidates,
          specializations: _stageSpecializations,
          scopeGuarded: _stageGuarded,
          rulesOut: nextPool.length,
          indexed: !!factIndex,
        });
      }

      if (nextPool.length > MAX_COMPOSED_PER_STAGE) {
        throw new Error(
          `Multi-stage composition: ${nextPool.length} rules after stage '${pred}' ` +
          `exceeds limit (${MAX_COMPOSED_PER_STAGE})`
        );
      }

      pool = nextPool;
    }

    pass1Rules = pass1Direct;
    specializedPool = pool;
  }
  _pEnd('load/compose/specialize', _tSpecialize, {
    stages: _specStages,
    pass1ForSpec: _specPass1ForSpec,
    compiledForSpec: _specCompiledForSpec,
    poolInitial: _specPoolInitial,
    poolFinal: specializedPool.length,
    totalSpecializations: diagnostics.specializations,
    scopeGuarded: diagnostics.scopeGuarded || 0,
  });
  if (_specOrderMs > 0) {
    _pEmit('load/compose/specialize/order', _specOrderMs, {
      predicates: grade0Facts.size,
    });
  }

  // ── Pass 3+4: Batch residual resolution ────────────────────────────
  // Most work done during transitive resolution in specialization loop.
  // This pass catches any remaining resolvable goals (safety net).
  const _tResidual = _pStart();
  const _residualPoolIn = specializedPool.length;
  if (residualResolver && specializedPool.length > 0) {
    specializedPool = specializedPool.map(r => _resolveOnce(r, rc, getModeMeta, residualResolver));
    diagnostics.residualResolutions = specializedPool.reduce((n, r) => {
      const name = r.name;
      const resCount = (name.match(/resolved:/g) || []).length;
      return n + resCount;
    }, 0);
  }
  _pEnd('load/compose/residual', _tResidual, {
    poolIn: _residualPoolIn,
    poolOut: specializedPool.length,
    resolutions: diagnostics.residualResolutions || 0,
    hasResolver: !!residualResolver,
  });

  // ── Pass 5: Basic block fusion ──────────────────────────────────────
  // Fuse 1:1 producer→consumer pairs into mega-rules via shared linear resource.
  const _tFuseBlocks = _pStart();
  const _fuseBlocksPoolIn = specializedPool.length;
  const fusePasses = o.fusePasses || null;
  if (doFuse && fusePasses && specializedPool.length > 0) {
    const fuseResult = fusePasses.fuseBasicBlocks(specializedPool, rc, getModeMeta, linearFusionPredicate, fusionBarriers, onPhase);
    specializedPool = fuseResult.rules;
    diagnostics.fusedRuleReduction = fuseResult.fusedCount;
    diagnostics.fuseChainLengths = fuseResult.chainLengths;
  }
  _pEnd('load/compose/fuse-blocks', _tFuseBlocks, {
    enabled: doFuse,
    poolIn: _fuseBlocksPoolIn,
    poolOut: specializedPool.length,
    fusedReduction: diagnostics.fusedRuleReduction || 0,
    chains: (diagnostics.fuseChainLengths || []).length,
    chainLengths: diagnostics.fuseChainLengths || [],
    maxChainLength: (diagnostics.fuseChainLengths || []).reduce((m, l) => Math.max(m, l), 0),
    avgChainLength: (diagnostics.fuseChainLengths || []).length
      ? (diagnostics.fuseChainLengths.reduce((a, b) => a + b, 0) / diagnostics.fuseChainLengths.length)
      : 0,
  });

  // ── Pass 5.5: Additive chain fusion after basic block fusion ────────
  // Fused mega-rules accumulate threading chains. Collapse them algebraically.
  const _tFuseChains = _pStart();
  const _fuseChainsPoolIn = specializedPool.length;
  if (doFuse && fusePasses && specializedPool.length > 0) {
    specializedPool = fusePasses.fuseChains(specializedPool, rc, getModeMeta, chainConfigs);
  }
  _pEnd('load/compose/fuse-chains', _tFuseChains, {
    enabled: doFuse,
    poolIn: _fuseChainsPoolIn,
    poolOut: specializedPool.length,
    chainConfigs: chainConfigs ? chainConfigs.length : 0,
  });

  // ── Pass 5.6: Second residual resolution after fusion ───────────────
  // Fusion may create newly-ground goals. Resolve them before SROA.
  if (residualResolver && doFuse && specializedPool.length > 0) {
    specializedPool = specializedPool.map(r => _resolveOnce(r, rc, getModeMeta, residualResolver));
  }

  // ── Pass 6: McCarthy normalization + SROA ──────────────────────────
  // McCarthy: peel acons layers from array-access goals (read/write-head axioms).
  // SROA: expand cons pattern in linear resource, eliminate remaining array goals.
  // Replacement strategy: SROA'd version replaces original (OOB = stall either way).
  const _tSroa = _pStart();
  const _sroaPoolIn = specializedPool.length;
  if (doFuse && fusePasses && specializedPool.length > 0) {
    const sroaResult = fusePasses.sroa(specializedPool, rc, getModeMeta, sroaConfig);
    specializedPool = sroaResult.rules;
    diagnostics.sroaTransformed = sroaResult.sroaCount;
    diagnostics.mccarthyNormalized = sroaResult.mccarthyCount;
  }
  _pEnd('load/compose/sroa', _tSroa, {
    enabled: doFuse,
    poolIn: _sroaPoolIn,
    poolOut: specializedPool.length,
    sroaTransformed: diagnostics.sroaTransformed || 0,
    mccarthyNormalized: diagnostics.mccarthyNormalized || 0,
    hasConfig: !!sroaConfig,
  });

  // ── Pass 6.5: Post-SROA residual resolution ───────────────────────
  // McCarthy + SROA ground variables (array slot bindings), enabling resolution
  // of dependent goals that were previously blocked by non-ground inputs.
  if (residualResolver && doFuse && specializedPool.length > 0) {
    specializedPool = specializedPool.map(r => _resolveOnce(r, rc, getModeMeta, residualResolver));
  }

  // Return all results: pass-1 (unspecialized) + multi-stage specialized
  const composedRules = [...pass1Rules, ...specializedPool];
  const result = { composedRules, removedNames, predicateMap, diagnostics };
  _composeCache.set(fullKey, result);
  return result;
}

export { cutPair, specialize, predMap, elimOrder, compose0, _resolveOnce, _tablingCacheKey, _composeFullKey, sortGoals, _makeRule, _renameForCompose, removeAt, _requireConnTags, _tagDisjoint };
export default { cutPair, specialize, predMap, elimOrder, compose0, _resolveOnce, _tablingCacheKey, _composeFullKey, sortGoals };
