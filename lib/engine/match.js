/**
 * Pattern matching, indexing, and persistent proving dispatch.
 *
 * Matching pipeline: FactSet-based state → pattern matching → persistent proving.
 * Contains:
 *   - Profiling instrumentation
 *   - Rule indexing (discIndex, fpDetect)
 *   - Pattern matching (tryMatch pipeline)
 *
 * Persistent proving, existential resolution, loli matching, and compiled
 * persistent steps live in their respective LNL layer modules:
 *   - lnl/persistent.js — clearBWCache, execPS
 *   - lnl/existential.js — resolveEx
 *   - lnl/loli.js — matchLoli
 *
 * State is a FactSet-based State object (lib/engine/fact-set.js).
 * State IS the index — no separate buildStateIndex needed.
 */

const Store = require('../kernel/store');
const { predHead } = require('../kernel/ast');
const { matchIndexed: _matchIdx, undoSave, undoRestore, undoDiscard } = require('../kernel/unify');
const { applyIndexed: _subApplyIdx } = require('../kernel/substitute');
const { deltaBypass } = require('./delta-bypass');

// ─── Layer module lazy accessors (for buildMatchOpts + re-exports) ───
// These provide backward-compatible access for callers that import
// provePersistent/matchLoli/resolveEx/etc. directly from match.js.
// After TODO_0206, callers should import from the source modules.
let _lnlPersistent = null, _lnlLoli = null, _lnlExistential = null, _optFfi = null;
function _getPersistent() { return _lnlPersistent || (_lnlPersistent = require('./lnl/persistent')); }
function _getLoli() { return _lnlLoli || (_lnlLoli = require('./lnl/loli')); }
function _getExistential() { return _lnlExistential || (_lnlExistential = require('./lnl/existential')); }
function _getOptFfi() { return _optFfi || (_optFfi = require('./opt/ffi')); }

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

/** Map discriminator ground value → [rule, ...] for O(1) lookup */
function discIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (!rule.discriminator) continue;
    const gv = rule.discriminator.groundValue;
    if (gv != null) {
      if (!index[gv]) index[gv] = [];
      index[gv].push(rule);
    }
  }
  return index;
}

/**
 * Auto-detect fingerprint configuration from compiled rules.
 * Finds dominant discriminator predicate and pointer predicate.
 * Two-pass (count discriminators, then find pointers) — runs once at startup.
 */
function fpDetect(rules) {
  const discCounts = {};
  for (const r of rules) {
    if (r.discriminator) {
      const key = r.discriminator.pred;
      discCounts[key] = (discCounts[key] || 0) + 1;
    }
  }

  let bestPred = null, bestCount = 0;
  for (const pred in discCounts) {
    if (discCounts[pred] > bestCount) {
      bestPred = pred;
      bestCount = discCounts[pred];
    }
  }
  if (!bestPred || bestCount < 2) return null;

  const sample = rules.find(r => r.discriminator && r.discriminator.pred === bestPred);
  const { groundPos, keyPos } = sample.discriminator;

  // Virtual discriminator: pointerPred and arrayPred stored directly
  if (sample.discriminator.type === 'virtual') {
    return {
      type: 'virtual',
      pred: bestPred,
      keyPos,
      groundPos,
      pointerPred: sample.discriminator.pointerPred,
      arrayPred: sample.discriminator.arrayPred
    };
  }

  // Auto-detect pointer predicate (unary pattern sharing a var with discriminator key)
  let pointerPred = null;
  for (const r of rules) {
    if (!r.discriminator || r.discriminator.pred !== bestPred) continue;
    for (const lp of (r.antecedent.linear || [])) {
      if (predHead(lp) !== bestPred) continue;
      const keyVar = Store.child(lp, keyPos);
      if (Store.tag(keyVar) !== 'metavar') continue;
      for (const lp2 of (r.antecedent.linear || [])) {
        if (lp2 === lp) continue;
        const pred2 = predHead(lp2);
        if (pred2 && Store.arity(lp2) === 1 && Store.child(lp2, 0) === keyVar) {
          pointerPred = pred2;
          break;
        }
      }
      if (pointerPred) break;
    }
    if (pointerPred) break;
  }

  // Self-pointer: unary discriminator where keyPos === groundPos (e.g., pc(0x0))
  // The predicate IS its own pointer — state lookup extracts value from same position
  if (!pointerPred && keyPos === groundPos) {
    pointerPred = bestPred;
  }

  return { pred: bestPred, keyPos, groundPos, pointerPred };
}

/**
 * Look up the fingerprint discriminator value from state using fpConfig.
 * Works for any program with a pointer predicate and discriminator predicate.
 */
// Default ILL lookupArrayValue — used when fpConfig.lookupArrayValue not provided.
// Lazy require to avoid import-time coupling when callback is injected.
let _illBinToInt = null;
function _defaultLookupArrayValue(keyValue, arrayHash) {
  if (!_illBinToInt) _illBinToInt = require('./ill/ffi/convert').binToInt;
  const idx = _illBinToInt(keyValue);
  if (idx === null) return null;
  const elems = Store.getArrayElements(arrayHash);
  if (elems) {
    if (idx < 0n || idx >= BigInt(elems.length)) return null;
    return elems[Number(idx)];
  }
  const { trieNav } = require('./ill/ffi/array');
  return trieNav(arrayHash, idx);
}

function fpValue(state, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return null;

  // Step 1: Get pointer fact (e.g., pc(VALUE) — must be exactly one)
  const pointerTagId = Store.TAG[fpConfig.pointerPred];
  if (pointerTagId === undefined) return null;
  const pointerGroup = state.linear.group(pointerTagId);
  if (pointerGroup.length !== 1) return null;
  if (Store.arity(pointerGroup[0]) < 1) return null;
  const keyValue = Store.child(pointerGroup[0], 0);

  // Virtual fingerprint: O(1) ARRAY_TABLE lookup or O(log N) trie navigation
  if (fpConfig.type === 'virtual') {
    const arrayTagId = Store.TAG[fpConfig.arrayPred];
    if (arrayTagId === undefined) return null;
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length !== 1) return null;
    const arrayHash = Store.child(arrayGroup[0], 0);
    const lookup = fpConfig.lookupArrayValue || _defaultLookupArrayValue;
    return lookup(keyValue, arrayHash);
  }

  // Step 2: O(1) lookup via secondary index (e.g., _byKey[pcValue] → code fact)
  if (state._byKey) {
    const fact = state._byKey[keyValue];
    if (fact && Store.arity(fact) > fpConfig.groundPos) {
      return Store.child(fact, fpConfig.groundPos);
    }
  }

  // Fallback: scan facts of discriminator predicate
  const discTagId = Store.TAG[fpConfig.pred];
  if (discTagId === undefined) return null;
  const discGroup = state.linear.group(discTagId);
  for (let i = 0; i < discGroup.length; i++) {
    const h = discGroup[i];
    if (Store.arity(h) <= fpConfig.keyPos) continue;
    if (Store.child(h, fpConfig.keyPos) !== keyValue) continue;
    return Store.child(h, fpConfig.groundPos);
  }
  return null;
}

// ─── Pattern Matching ───────────────────────────────────────────────

// Reusable work buffers (avoids allocation per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);

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
  const tagIdx = pred ? Store.TAG[pred] : -1;

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
    // Atom predicate: get atom group (caller filters by pred head match)
    candidates = state.groupForPred(pred);
  } else {
    // Wildcard pred: collect all linear facts
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
    const useCompiledSteps = matchOpts && matchOpts.useCompiledSteps;
    const hasHooks = matchOpts && (matchOpts.onProveSuccess || matchOpts.onProveFail);
    if (!evidenceOut && !hasHooks && useCompiledSteps) {
      const persSteps = rule.persistentSteps;
      if (persSteps) {
        while (persistentIdx < persistentList.length) {
          const step = persSteps[persistentIdx];
          if (!step) break;  // no compiled step → fall through to generic
          const r = _getOptFfi().execPS(step, theta);
          if (r === true) { persistentIdx++; madeProgress = true; continue; }
          if (r === false) break;  // FFI definitive/advisory failure — fall through to generic path
          break;  // null → needs generic path (non-ground input, etc.)
        }
      }
    }
    const proveFn = (matchOpts && matchOpts.provePersistent) || _getOptFfi().proveWithFFI;
    const newIdx = proveFn(persistentList, persistentIdx, theta, slots, state, calc, evidenceOut, matchOpts);
    if (newIdx > persistentIdx) madeProgress = true;
    persistentIdx = newIdx;

    if (!madeProgress && (rpLen > 0 || persistentIdx < persistentList.length)) {
      return -1;
    }
  }

  return persistentIdx;
}

/**
 * Try to match a rule against state.
 *
 * Orchestrates: setup → matchLinearAll → existential resolution → result.
 * Returns { rule, theta, slots, consumed, optimized } or null.
 */
function tryMatch(rule, state, calc, matchOpts) {
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
  const usePreserved = matchOpts && matchOpts.optimizePreserved && preserved && preserved.length > 0;
  if (usePreserved) {
    for (const h of preserved) {
      _poolPreservedCount.set(h, (_poolPreservedCount.get(h) || 0) + 1);
    }
  }

  const persistentList = rule.antecedent.persistent || [];
  const wantEvidence = matchOpts && matchOpts.evidence;
  const evidenceOut = wantEvidence ? [] : null;
  const result = matchLinearAll(rule, state, _poolTheta, slots, _poolConsumed, _poolReserved,
                                _poolPreservedCount, usePreserved, persistentList, calc, evidenceOut, matchOpts);

  if (result < 0) {
    undoRestore(_poolTheta, topUndo);
    return null;
  }

  // Resolve existential slots (always succeeds — binds to freshEvar on failure)
  if (rule.existentialSlots && rule.existentialSlots.length > 0) {
    const _resolveEx = (matchOpts && matchOpts.resolveEx) || _getExistential().resolveEx;
    _resolveEx(_poolTheta, slots, rule, state, calc, matchOpts);
  }

  // Copy on success (rare path — most tryMatch calls fail)
  const consumed = {};
  _poolConsumed.forEach((v, k) => { consumed[k] = v; });
  const theta = _poolTheta.slice(0, metavarCount);

  undoDiscard(topUndo);
  const m = { rule, theta, slots, consumed, optimized: !!usePreserved };
  if (wantEvidence) m.persistentEvidence = evidenceOut;
  return m;
}

/**
 * Build common matchOpts for forward/explore. Callers spread and add extras.
 */
function buildMatchOpts({ useFFI, evidence, rc, ffiCtx, canonicalize, onProveFail, onProveSuccess, backchainUseFFI, optimizePreserved, execExStep, matchLoli: matchLoliCb, resolveEx: resolveExCb, drainLolis: drainLolisCb }) {
  const opts = {
    optimizePreserved: optimizePreserved || undefined,
    evidence: evidence || undefined,
    useCompiledSteps: useFFI,
    dynamicRuleTag: rc.implication || null,
    matchDynamicRule: matchLoliCb || _getLoli().matchLoli,
    resolveEx: resolveExCb || _getExistential().resolveEx,
    connectives: rc,
    ffiParsedModes: ffiCtx ? ffiCtx.parsedModes : null,
    ffiMeta: ffiCtx ? ffiCtx.meta : null,
    ffiGet: ffiCtx ? ffiCtx.get : null,
    ffiIsGround: ffiCtx ? ffiCtx.isFFIGround : null,
    canonicalize,
    onProveFail,
    onProveSuccess,
    backchainUseFFI,
    execExStep: execExStep || null,
    drainLolis: drainLolisCb || null,
  };
  opts.provePersistent = useFFI
    ? _getOptFfi().proveWithFFI
    : (patterns, startIdx, theta, slots, state, calc, evidenceOut) =>
        _getPersistent().proveNaive(patterns, startIdx, theta, slots, state, calc, evidenceOut, opts);
  return opts;
}

module.exports = {
  // Profiling
  getProfile,
  resetProfile,
  // Rule indexing
  discIndex,
  fpDetect,
  fpValue,
  // Backward cache (re-exported via lazy accessor — callers should import from backward-cache.js directly)
  get clearBWCache() { return require('./backward-cache').clearBWCache; },
  // Persistent proving (re-exported via lazy accessor — callers should import from opt/ffi.js directly)
  get provePersistent() { return _getOptFfi().proveWithFFI; },
  get execPS() { return _getOptFfi().execPS; },
  get compilePS() { return _getOptFfi().compilePS; },
  // Existential resolution (re-exported via lazy accessor — callers should import from lnl/existential.js directly)
  get resolveEx() { return _getExistential().resolveEx; },
  // Pattern matching
  tryMatch,
  // Loli matching (re-exported via lazy accessor — callers should import from lnl/loli.js directly)
  get matchLoli() { return _getLoli().matchLoli; },
  // matchOpts factory
  buildMatchOpts,
};
