/**
 * Pattern matching, indexing, and persistent proving dispatch.
 *
 * Matching pipeline: FactSet-based state → pattern matching → persistent proving.
 * Contains:
 *   - Profiling instrumentation
 *   - Rule indexing (discIndex, fpDetect)
 *   - Pattern matching (tryMatch pipeline)
 *
 * Persistent proving, existential resolution, dynamic-rule matching, and
 * compiled persistent steps live in the structural family's modules
 * (family/<name>/lib/, injected via cc.family.engine — TODO_0086):
 *   - family/lnl/lib/persistent.js — proveNaive
 *   - family/lnl/lib/existential.js — resolveEx
 *   - family/lnl/lib/loli.js — matchLoli (the matchDynamicRule binding)
 *
 * State is a FactSet-based State object (lib/engine/fact-set.js).
 * State IS the index — no separate buildStateIndex needed.
 */

import Store from '../kernel/store.js';
import { predHead } from '../kernel/ast.js';
import { matchIndexed as _matchIdx, undoSave, undoRestore, undoDiscard } from '../kernel/unify.js';
import { applyIndexed as _subApplyIdx } from '../kernel/substitute.js';
import { deltaBypass } from './delta-bypass.js';
// ─── Profiling ──────────────────────────────────────────────────────

const PROFILE = typeof process !== 'undefined' && process.env.CALC_PERF_PROFILE === '1';
const profile = { matchTime: 0, matchCalls: 0, subTime: 0, subCalls: 0, proveTime: 0, proveCalls: 0 };
function getProfile() { return profile; }
function resetProfile() {
  profile.matchTime = profile.matchCalls = 0;
  profile.subTime = profile.subCalls = 0;
  profile.proveTime = profile.proveCalls = 0;
}

// JIT-friendly: early return when PROFILE=0 lets v8 inline/eliminate timing code.
function matchIdx(pattern, hash, theta, slots) {
  if (!PROFILE) return _matchIdx(pattern, hash, theta, slots);
  const t0 = performance.now();
  const result = _matchIdx(pattern, hash, theta, slots);
  profile.matchTime += performance.now() - t0;
  profile.matchCalls++;
  return result;
}

function subApplyIdx(hash, theta, slots) {
  if (!PROFILE) return _subApplyIdx(hash, theta, slots);
  const t0 = performance.now();
  const result = _subApplyIdx(hash, theta, slots);
  profile.subTime += performance.now() - t0;
  profile.subCalls++;
  return result;
}

// ─── Rule Indexing ──────────────────────────────────────────────────
// (moved to opt/fingerprint.js, RES_0143 M5 — fpDetect/fpValue/discIndex
// are optimization machinery; the matcher only READS the optional
// state._byKey / state._fpPred fields the fingerprint layer maintains.)

// ─── Pattern Matching ───────────────────────────────────────────────

// Reusable work buffers (avoids allocation per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);

// Tier-2 trigger flag (TODO_0309): armed by matchLinear1 when a linear
// pattern scanned a multi-candidate group — i.e. the committed pass made
// (or could have made) a genuine CHOICE. Reset per tryMatch. Strategy A
// (delta bypass) and B (secondary index) are functional by construction
// and never arm it.
let _commitHadChoice = false;

// Pooled Maps for tryMatch (cleared on each call, copied on success)
const _poolConsumed = new Map();
const _poolReserved = new Map();
// Max metavar slots per rule. 128 covers observed max (~32) with headroom
// for fused rules. Assertion in tryMatch guards against silent overflow.
const MAX_SLOTS = 128;
const _poolTheta = new Array(MAX_SLOTS);
const _poolPreservedCount = new Map();

/**
 * Match one linear pattern against state facts.
 * Dispatches across three strategies in order:
 *   A. Delta bypass — direct child extraction for flat delta patterns
 *   B. Secondary index — O(1) lookup for fingerprint predicate
 *   C. General matching — full unification against all indexed candidates
 *
 * Mutates theta/consumed/reserved on success. Returns true if matched.
 */
function matchLinear1(pattern, origPos, rule, state, theta, slots,
                         consumed, reserved, preservedCount, usePreserved) {
  const meta = rule.linearMeta[pattern];
  const pred = meta.pred;
  const isPreserved = usePreserved && (preservedCount.get(pattern) || 0) > 0;
  // Dispatch by the pattern's OWN head tag (compile.js predTag): the
  // global name→tag table is ambiguous across loaded programs (an
  // atom-headed pattern must take the atom path even when a same-named
  // predicate tag exists). Name fallback only for stale cached rules.
  const tagIdx = meta.predTag !== undefined
    ? (meta.predTag >= Store.PRED_BOUNDARY ? meta.predTag : -1)
    : (pred ? Store.TAG[pred] : -1);

  // Strategy A: Delta bypass — direct child extraction for flat delta patterns
  if (deltaBypass(pattern, origPos, rule, state, theta,
                       consumed, reserved, isPreserved, tagIdx)) {
    return true;
  }

  // Strategy B: Secondary index O(1) lookup for fingerprint predicate
  if (pred === state._fpPred && state._byKey && meta.secondaryKeyPattern !== null) {
    const keyValue = subApplyIdx(meta.secondaryKeyPattern, theta, slots);
    const codeFact = state._byKey[keyValue];
    if (codeFact) {
      const cfTag = Store.tagId(codeFact);
      const available = state.linear.count(cfTag, codeFact) - (consumed.get(codeFact) || 0) - (reserved.get(codeFact) || 0);
      if (available > 0) {
        const savedUndo = undoSave();
        if (matchIdx(pattern, codeFact, theta, slots)) {
          if (isPreserved) {
            reserved.set(codeFact, (reserved.get(codeFact) || 0) + 1);
            preservedCount.set(pattern, preservedCount.get(pattern) - 1);
          } else {
            consumed.set(codeFact, (consumed.get(codeFact) || 0) + 1);
          }
          return true;
        }
        undoRestore(theta, savedUndo);
      }
    }
  }

  // Strategy C: General matching against all indexed candidates
  let candidates;
  if (tagIdx >= 0) {
    candidates = state.linear.group(tagIdx);
  } else if (pred) {
    // Atom predicate: get atom group (caller filters by pred head match).
    // Tag-aware when the compiled predTag is present — the name-based
    // lookup would misroute to a same-named predicate tag's group.
    candidates = meta.predTag !== undefined
      ? state.groupForPredTag(meta.predTag, pred)
      : state.groupForPred(pred);
  } else {
    // Wildcard pred: collect all linear facts
    const all = [];
    state.linear.forEach(h => all.push(h));
    candidates = all;
  }

  // Tier-2 trigger (TODO_0309): committing here is only a CHOICE when the
  // group holds more than one candidate — the flag arms the backtracking
  // rematch in tryMatch. Raw group length over-approximates (duplicates,
  // already-consumed facts) — safe: tier 2 is a complete re-search.
  if (candidates.length > 1) _commitHadChoice = true;

  for (let ci = 0; ci < candidates.length; ci++) {
    const h = candidates[ci];
    const hTag = tagIdx >= 0 ? tagIdx : Store.tagId(h);
    const available = state.linear.count(hTag, h) - (consumed.get(h) || 0) - (reserved.get(h) || 0);
    if (available <= 0) continue;

    const savedUndo = undoSave();
    if (matchIdx(pattern, h, theta, slots)) {
      if (isPreserved) {
        reserved.set(h, (reserved.get(h) || 0) + 1);
        preservedCount.set(pattern, preservedCount.get(pattern) - 1);
      } else {
        consumed.set(h, (consumed.get(h) || 0) + 1);
      }
      return true;
    }
    undoRestore(theta, savedUndo);
  }

  return false;
}

/**
 * Algorithm: Interleaved Linear Matching + Persistent Proving
 *
 * Implements the matching judgment for compiled forward rules:
 * Given rule (Γ_lin ; Γ_pers ⊢ C), find substitution θ such that
 * θ(Γ_lin) ⊆ Δ (linear state) and θ(Γ_pers) are provable.
 *
 * Uses a worklist with deferred patterns to handle inter-phase
 * dependencies: some linear patterns contain metavars that are only
 * bound by persistent proving (e.g., a linear pattern mentioning Y
 * where Y is an output of !plus(X,1,Y)).
 *
 * Returns persistentIdx (>= 0) on success, -1 on failure.
 */
function matchLinearAll(rule, state, theta, slots, consumed, reserved,
                        preservedCount, usePreserved, persistentList, calc, evidenceOut, matchOpts) {
  const linearPats = rule.antecedent.linear || [];
  let rpLen = linearPats.length;
  for (let i = 0; i < rpLen; i++) {
    _workPatterns[i] = linearPats[i];
    _workPositions[i] = i;
  }

  let persistentIdx = 0;
  let iterations = 0;
  const maxIterations = rpLen + persistentList.length + 10;

  while (rpLen > 0 || persistentIdx < persistentList.length) {
    if (++iterations > maxIterations) return -1;

    let madeProgress = false;

    // Phase 1: Match linear patterns
    let deferredLen = 0;
    for (let pi = 0; pi < rpLen; pi++) {
      const pattern = _workPatterns[pi];
      const origPos = _workPositions[pi];
      const meta = rule.linearMeta[pattern];

      // Defer if dependencies on unbound persistent outputs
      if (meta.persistentDeps.size > 0) {
        let hasUnbound = false;
        for (const v of meta.persistentDeps) {
          if (theta[slots[v]] === undefined) { hasUnbound = true; break; }
        }
        if (hasUnbound) {
          _workPatterns[deferredLen] = pattern;
          _workPositions[deferredLen] = origPos;
          deferredLen++;
          continue;
        }
      }

      if (!matchLinear1(pattern, origPos, rule, state, theta, slots,
                            consumed, reserved, preservedCount, usePreserved)) {
        return -1;
      }
      madeProgress = true;
    }

    rpLen = deferredLen;

    // Phase 2: Prove persistent patterns.
    // When collecting evidence or profiling: skip the compiled FFI fast path
    // (persistentSteps) because execPS doesn't record HOW the goal
    // was proved — it just returns true/false. Fall through to provePersistent
    // which captures evidence/hooks per goal. Consistent with "FFI is optimization"
    // — when we need observability, we use the slower but instrumented path.
    const useCompiledSteps = matchOpts.useCompiledSteps;
    const hasHooks = matchOpts.onProveSuccess || matchOpts.onProveFail;
    if (!evidenceOut && !hasHooks && useCompiledSteps && matchOpts.execPS) {
      const persSteps = rule.persistentSteps;
      if (persSteps) {
        while (persistentIdx < persistentList.length) {
          const step = persSteps[persistentIdx];
          if (!step) break;  // no compiled step → fall through to generic
          const r = matchOpts.execPS(step, theta);
          if (r === true) { persistentIdx++; madeProgress = true; continue; }
          if (r === false) break;  // FFI definitive/advisory failure — fall through to generic path
          break;  // null → needs generic path (non-ground input, etc.)
        }
      }
    }
    if (persistentIdx < persistentList.length) {
      const proveFn = matchOpts.provePersistent;
      if (!proveFn) return -1;  // No prove function — cannot resolve persistent goals
      const newIdx = proveFn(persistentList, persistentIdx, theta, slots, state, calc, evidenceOut, matchOpts);
      if (newIdx > persistentIdx) madeProgress = true;
      persistentIdx = newIdx;
    }

    if (!madeProgress && (rpLen > 0 || persistentIdx < persistentList.length)) {
      return -1;
    }
  }

  return persistentIdx;
}

/**
 * Tier-2 complete linear matching (TODO_0309): backtracking join search.
 *
 * matchLinearAll (tier 1, the hot path) COMMITS to the first unifying
 * fact per pattern — correct whenever the join is functional. When a
 * later pattern or persistent goal fails under that commitment, a
 * DIFFERENT candidate for an earlier pattern may still satisfy the rule;
 * tier 1 then reports the rule inapplicable, and which way it goes
 * depends on fact hash order (SAX-style states — several `proc` facts
 * joined against a persistent cell — made this observable). Tier 2 is
 * the complete search: depth-first over candidate facts per linear
 * pattern (rule order, general iteration only — no committed
 * A/B shortcuts), persistent goals proven under each complete linear
 * assignment. Cost is bounded by the product of candidate group sizes
 * and paid only when tier 1 fails on a rule whose antecedent items
 * share metavars (needsJoinSearch).
 *
 * Persistent WITNESS commitment is unchanged: provePersistent commits
 * per goal exactly as in tier 1 — but it reruns under every linear
 * assignment, so linear-bound inputs flow correctly. Residual gap
 * (recorded in TODO_0309): a multi-witness persistent goal whose choice
 * feeds a LATER persistent goal still commits to its first witness.
 */
function matchJoinSearch(rule, state, theta, slots, consumed, reserved,
                         preservedCount, usePreserved, persistentList, calc, evidenceOut, matchOpts) {
  const linearPats = rule.antecedent.linear || [];
  const n = linearPats.length;

  const provePhase = () => {
    if (persistentList.length === 0) return true;
    const proveFn = matchOpts.provePersistent;
    if (!proveFn) return false;
    const savedUndo = undoSave();
    const ev = evidenceOut ? [] : null;
    const idx = proveFn(persistentList, 0, theta, slots, state, calc, ev, matchOpts);
    if (idx >= persistentList.length) {
      if (ev) evidenceOut.push(...ev);
      return true;
    }
    undoRestore(theta, savedUndo);
    return false;
  };

  const matchFrom = (pi) => {
    if (pi >= n) return provePhase();
    const pattern = linearPats[pi];
    const meta = rule.linearMeta[pattern];
    const isPreserved = usePreserved && (preservedCount.get(pattern) || 0) > 0;
    const tagIdx = meta.predTag !== undefined
      ? (meta.predTag >= Store.PRED_BOUNDARY ? meta.predTag : -1)
      : (meta.pred ? Store.TAG[meta.pred] : -1);
    let candidates;
    if (tagIdx >= 0) {
      candidates = state.linear.group(tagIdx);
    } else if (meta.pred) {
      candidates = meta.predTag !== undefined
        ? state.groupForPredTag(meta.predTag, meta.pred)
        : state.groupForPred(meta.pred);
    } else {
      const all = [];
      state.linear.forEach(h => all.push(h));
      candidates = all;
    }

    for (let ci = 0; ci < candidates.length; ci++) {
      const h = candidates[ci];
      const hTag = tagIdx >= 0 ? tagIdx : Store.tagId(h);
      const available = state.linear.count(hTag, h) - (consumed.get(h) || 0) - (reserved.get(h) || 0);
      if (available <= 0) continue;

      const savedUndo = undoSave();
      if (matchIdx(pattern, h, theta, slots)) {
        if (isPreserved) {
          reserved.set(h, (reserved.get(h) || 0) + 1);
          preservedCount.set(pattern, preservedCount.get(pattern) - 1);
        } else {
          consumed.set(h, (consumed.get(h) || 0) + 1);
        }
        if (matchFrom(pi + 1)) return true;
        if (isPreserved) {
          reserved.set(h, reserved.get(h) - 1);
          preservedCount.set(pattern, preservedCount.get(pattern) + 1);
        } else {
          consumed.set(h, consumed.get(h) - 1);
        }
      }
      undoRestore(theta, savedUndo);
    }
    return false;
  };

  return matchFrom(0) ? persistentList.length : -1;
}

/** Collect metavar hashes of a pattern into `out`. */
function _patternMetavars(h, out) {
  if (!Store.isTerm(h)) return;
  if (Store.tag(h) === 'metavar') { out.add(h); return; }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) _patternMetavars(c, out);
  }
}

/** Tier-2 gate: does any metavar occur in two antecedent items? Cached. */
function needsJoinSearch(rule) {
  if (rule._joinSearch !== undefined) return rule._joinSearch;
  const items = [...(rule.antecedent.linear || []), ...(rule.antecedent.persistent || [])];
  let shared = false;
  if (items.length >= 2) {
    const seen = new Set();
    outer:
    for (const it of items) {
      const vars = new Set();
      _patternMetavars(it, vars);
      for (const v of vars) {
        if (seen.has(v)) { shared = true; break outer; }
        seen.add(v);
      }
    }
  }
  rule._joinSearch = shared;
  return shared;
}

/**
 * Try to match a rule against state.
 *
 * Orchestrates: setup → matchLinearAll → existential resolution → result.
 * Returns { rule, theta, slots, consumed, optimized } or null.
 *
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts (EMPTY_MATCH_OPTS is the canonical empty default). The default
 * parameter guarantees callers never need to pass a matchOpts for basic use.
 */
function tryMatch(rule, state, calc, matchOpts = EMPTY_MATCH_OPTS) {
  // Reuse pooled Maps (cleared per call, copied on success)
  _poolConsumed.clear();
  _poolReserved.clear();

  const topUndo = undoSave();
  const { metavarSlots: slots, metavarCount } = rule;
  if (metavarCount > MAX_SLOTS) {
    throw new Error(`tryMatch: rule '${rule.name}' has ${metavarCount} metavars, exceeds MAX_SLOTS=${MAX_SLOTS}`);
  }
  _poolTheta.fill(undefined, 0, metavarCount);

  _poolPreservedCount.clear();
  const preserved = rule.preserved;
  const optPreserved = matchOpts.optimizePreserved && preserved && preserved.length > 0;
  if (optPreserved) {
    for (const h of preserved) {
      _poolPreservedCount.set(h, (_poolPreservedCount.get(h) || 0) + 1);
    }
  }
  // read-marked patterns (rule.readOnly, E7.2) ALWAYS take the reserved
  // path — reading is semantics, not an optimization: the fact is matched
  // but never consumed (and never re-produced, so its stamp is untouched).
  const readOnly = rule.readOnly;
  if (readOnly) {
    for (const h of readOnly) {
      _poolPreservedCount.set(h, (_poolPreservedCount.get(h) || 0) + 1);
    }
  }
  const useReserve = optPreserved || !!(readOnly && readOnly.length > 0);

  const persistentList = rule.antecedent.persistent || [];
  const wantEvidence = matchOpts.evidence;
  const evidenceOut = wantEvidence ? [] : null;
  _commitHadChoice = false;
  let result = matchLinearAll(rule, state, _poolTheta, slots, _poolConsumed, _poolReserved,
                              _poolPreservedCount, useReserve, persistentList, calc, evidenceOut, matchOpts);

  if (result < 0 && _commitHadChoice && needsJoinSearch(rule)) {
    // Tier 2 (TODO_0309): the committed pass may have failed on a
    // non-functional join — rerun as a complete backtracking search
    // from a clean slate.
    undoRestore(_poolTheta, topUndo);
    _poolConsumed.clear();
    _poolReserved.clear();
    _poolTheta.fill(undefined, 0, metavarCount);
    _poolPreservedCount.clear();
    if (optPreserved) {
      for (const h of preserved) {
        _poolPreservedCount.set(h, (_poolPreservedCount.get(h) || 0) + 1);
      }
    }
    if (readOnly) {
      for (const h of readOnly) {
        _poolPreservedCount.set(h, (_poolPreservedCount.get(h) || 0) + 1);
      }
    }
    if (evidenceOut) evidenceOut.length = 0;
    result = matchJoinSearch(rule, state, _poolTheta, slots, _poolConsumed, _poolReserved,
                             _poolPreservedCount, useReserve, persistentList, calc, evidenceOut, matchOpts);
  }

  if (result < 0) {
    undoRestore(_poolTheta, topUndo);
    return null;
  }

  // Resolve existential slots (always succeeds — binds to freshEvar on failure)
  if (rule.existentialSlots && rule.existentialSlots.length > 0) {
    const _resolveEx = matchOpts.resolveEx;
    if (_resolveEx) _resolveEx(_poolTheta, slots, rule, state, calc, matchOpts);
  }

  // Copy on success (rare path — most tryMatch calls fail)
  const consumed = {};
  _poolConsumed.forEach((v, k) => { consumed[k] = v; });
  const theta = _poolTheta.slice(0, metavarCount);

  undoDiscard(topUndo);
  // `optimized` means the $-preserved shortcut was pooled — it drives the
  // skip-preserved-inserts branch in produce/explore. read reservations do
  // NOT set it: their patterns have no consequent copy to skip.
  const m = { rule, theta, slots, consumed, optimized: !!optPreserved };
  if (wantEvidence) m.persistentEvidence = evidenceOut;
  return m;
}

// ─── Method enum ────────────────────────────────────────────────────
//
// Canonical enumeration of provePersistent success methods. All provers
// (stateProvePersistent, proveNaive, proveWithFFI) emit `method` strings
// from this set when calling onProveSuccess / pushing evidence.
// Tests enforce that no other strings leak through.

const PROVE_METHOD = Object.freeze({
  FFI: 'ffi', STATE: 'state', COMPILED: 'compiled', CACHE: 'cache', CLAUSE: 'clause',
});
// Flat frozen list derived from the enum — one source of truth. Tests that
// want "any valid method string" iterate this; emitters use PROVE_METHOD.FOO.
const PROVE_METHODS = Object.freeze(Object.values(PROVE_METHOD));

// ─── State-lookup primitive ─────────────────────────────────────────
//
// Single source of truth for "scan state.persistent for a fact matching
// this pattern". Used by stateProvePersistent (generic baseline),
// proveNaive (LNL), and proveWithFFI (OPT). Encapsulates the tag-id
// resolution, group iteration, and undo-save/restore ritual so all three
// provers unify on the same matching semantics.
//
// Theta is mutated on success (new bindings from unification); on failure
// it is restored via undo. The caller is responsible for hook/evidence
// emission (they each have layer-specific profiling payloads).
//
// @returns matched fact hash (number) on success, null on failure.

function tryStateLookup(pattern, theta, slots, state) {
  const pPred = predHead(pattern);
  if (!pPred) return null;
  // the PATTERN's own head tag decides the group — never the global
  // name table (ambiguous across loaded programs; see groupKeyForPredTag)
  const pTagId = Store.tagId(pattern);
  const effectiveTagId = pTagId >= Store.PRED_BOUNDARY ? pTagId : Store.TAG.atom;
  if (effectiveTagId === undefined || state.persistent.groupLen(effectiveTagId) === 0) {
    return null;
  }
  const persGroup = state.persistent.group(effectiveTagId);
  for (let gi = 0; gi < persGroup.length; gi++) {
    const hn = persGroup[gi];
    const savedUndo = undoSave();
    if (_matchIdx(pattern, hn, theta, slots)) {
      undoDiscard(savedUndo);
      return hn;
    }
    undoRestore(theta, savedUndo);
  }
  return null;
}

// ─── Baseline persistent prover (generic layer) ─────────────────────
//
// The semantic floor of persistent proving: for each pattern, look up a
// matching persistent fact in state.persistent via unification. No clause
// resolution, no backward cache, no FFI. Every stronger prover (proveNaive,
// proveWithFFI) layers on top of this step by calling tryStateLookup first.
//
// Provided in the generic layer so EMPTY_MATCH_OPTS is self-sufficient —
// direct callers (tests, benchmarks) that don't wire a real prover get
// state-lookup semantics for free, and loli.js / consumers never need a
// hardcoded cross-layer fallback import.

/**
 * Baseline state-only persistent prover. Signature matches the
 * `provePersistent` contract: returns index of first unproved pattern
 * (=== patterns.length if all proved).
 *
 * Hook payload: `{ ground: true, hasFfi: false }` — after successful
 * state-lookup unification the proved goal is ground (state facts are
 * ground, unification binds all pattern vars), and no FFI was used.
 * Goal reported to hooks is POST-unification (the actual proved form).
 */
function stateProvePersistent(patterns, startIdx, theta, slots, state, _calc, evidenceOut, matchOpts) {
  const onProveSuccess = matchOpts && matchOpts.onProveSuccess;
  let idx = startIdx;
  while (idx < patterns.length) {
    const pattern = patterns[idx];
    const matchedFact = tryStateLookup(pattern, theta, slots, state);
    if (matchedFact === null) return idx;
    if (evidenceOut || onProveSuccess) {
      const goal = _subApplyIdx(pattern, theta, slots);
      if (evidenceOut) evidenceOut.push({ goal, method: PROVE_METHOD.STATE, fact: matchedFact });
      if (onProveSuccess) onProveSuccess(goal, PROVE_METHOD.STATE, { ground: true, hasFfi: false });
    }
    idx++;
  }
  return idx;
}

// ─── Protocol Factories ─────────────────────────────────────────────
// Each factory returns its layer's contribution to matchOpts — a record
// of fields. The composition root (index.js) spreads them flat and
// freezes. Conceptually: row-polymorphic record extension (assembly of
// disjoint records with stable shape).
//
// Each factory always returns the same keys (shape stability). Missing
// inputs default to the documented zero per field. This guarantees every
// matchOpts has identical hidden class (V8 monomorphism).

/** Generic layer protocol: mode flags + cross-cutting hooks + interface
 *  contracts consumed by the generic engine.
 *
 *  `provePersistent` is the interface contract: the generic layer consumes
 *  it, outer layers (lnl/opt) implement it, the composition root wires
 *  the chosen implementation in. Declaring it here makes the generic
 *  layer the owner of its own consumption boundary. The factory default
 *  is the generic-layer baseline `stateProvePersistent` (state lookup
 *  only) — never null — so every matchOpts is semantically complete.
 */
function buildGenericProtocol({
  optimizePreserved = false,
  evidence = false,
  canonicalize,
  onProveFail,
  onProveSuccess,
  provePersistent,
} = {}) {
  return {
    optimizePreserved,
    evidence,
    canonicalize: canonicalize || null,
    onProveFail: onProveFail || null,
    onProveSuccess: onProveSuccess || null,
    provePersistent: provePersistent || stateProvePersistent,
  };
}

/** Family layer protocol: the structural family's callbacks + connective
 *  context (for LNL: the linear/persistent distinction — persistent goal
 *  proving, dynamic-rule matching, drain, existential resolution).
 *
 *  `backchainUseFFI` default is `false` — the platonic empty record supplies
 *  no FFI provider. The production pragmatic default (FFI-on unless the
 *  caller explicitly opts out) lives at the composition root (`index.js`),
 *  not in the factory: policy decisions belong where the full execOpts is
 *  visible, not in a single-layer factory. */
function buildFamilyProtocol({ matchDynamicRule, resolveEx, drainDynamicRules, rc, backchainUseFFI = false } = {}) {
  return {
    matchDynamicRule: matchDynamicRule || null,
    resolveEx: resolveEx || null,
    drainDynamicRules: drainDynamicRules || null,
    connectives: rc || null,
    dynamicRuleTag: rc ? (rc.implication || null) : null,
    backchainUseFFI,
  };
}

/** Opt layer protocol: compiled fast-path callbacks. */
function buildOptProtocol({ execPS, execExStep, tryCCDispatch, useCompiledSteps = false } = {}) {
  return {
    execPS: execPS || null,
    execExStep: execExStep || null,
    tryCCDispatch: tryCCDispatch || null,
    useCompiledSteps,
  };
}

/** FFI context protocol: provider-specific data for FFI-accelerated proving.
 *
 *  Accepts `null | undefined | ffiCtx` uniformly via optional-chaining —
 *  single code path regardless of whether a provider is present. */
function buildFfiProtocol(ffiCtx) {
  return {
    ffiParsedModes: ffiCtx?.parsedModes ?? null,
    ffiMeta: ffiCtx?.meta ?? null,
    ffiGet: ffiCtx?.get ?? null,
    ffiIsGround: ffiCtx?.isFFIGround ?? null,
  };
}

/**
 * Assemble and freeze a matchOpts object from pre-spread protocol fields.
 * All matchOpts instances have identical shape (V8 monomorphic hidden class).
 */
function buildMatchOpts(fields) {
  return Object.freeze(fields);
}

// ─── Shape constants (single source of truth) ─────────────────────────
// Factories are the ground truth for which fields each layer owns.
// Derive shape by invoking each with empty input — the returned key set
// IS the factory's contract. Tests (layer-dag.test.js) and EMPTY_MATCH_OPTS
// read these to avoid duplication.

const GENERIC_FIELDS = Object.freeze(Object.keys(buildGenericProtocol()));
const FAMILY_FIELDS = Object.freeze(Object.keys(buildFamilyProtocol()));
const OPT_FIELDS = Object.freeze(Object.keys(buildOptProtocol()));
const FFI_FIELDS = Object.freeze(Object.keys(buildFfiProtocol(null)));

/**
 * Canonical empty default: the matchOpts with all fields present but all
 * callbacks null. Same hidden class as fully-populated matchOpts — preserves
 * V8 IC monomorphism. Used by direct callers (tests, benchmarks) that bypass
 * the orchestrator and want default no-op semantics. Not a fallback kludge:
 * the principled empty record that fills the default-parameter slot.
 */
const EMPTY_MATCH_OPTS = buildMatchOpts({
  ...buildGenericProtocol(),
  ...buildFamilyProtocol(),
  ...buildOptProtocol(),
  ...buildFfiProtocol(null),
});

export { getProfile, resetProfile, tryMatch, tryStateLookup, stateProvePersistent, PROVE_METHODS, PROVE_METHOD, buildGenericProtocol, buildFamilyProtocol, buildOptProtocol, buildFfiProtocol, buildMatchOpts, EMPTY_MATCH_OPTS, GENERIC_FIELDS, FAMILY_FIELDS, OPT_FIELDS, FFI_FIELDS };
export default { getProfile, resetProfile, tryMatch, tryStateLookup, stateProvePersistent, PROVE_METHODS, PROVE_METHOD, buildGenericProtocol, buildFamilyProtocol, buildOptProtocol, buildFfiProtocol, buildMatchOpts, EMPTY_MATCH_OPTS, GENERIC_FIELDS, FAMILY_FIELDS, OPT_FIELDS, FFI_FIELDS };
