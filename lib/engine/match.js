/**
 * Pattern matching, indexing, and persistent proving.
 *
 * Matching pipeline: FactSet-based state → pattern matching → persistent proving.
 * Contains all matching-related functionality:
 *   - Profiling instrumentation
 *   - Rule indexing (buildDiscriminatorIndex)
 *   - Persistent proving (state lookup → backward prove [FFI | clauses])
 *   - Existential resolution
 *   - Pattern matching (tryMatch pipeline)
 *   - Loli continuation matching
 *
 * State is a FactSet-based State object (lib/engine/fact-set.js).
 * State IS the index — no separate buildStateIndex needed.
 */

const Store = require('../kernel/store');
const { getPredicateHead, collectExternalFreevars, proverBoundExternals } = require('../kernel/ast');
const { matchIndexed: _matchIdx, undoSave, undoRestore, undoDiscard } = require('../kernel/unify');
const { applyIndexed: _subApplyIdx } = require('../kernel/substitute');
const ffi = require('./ffi');
const { flattenTensor, expandConsequentChoices, collectMetavars } = require('./compile');
const { matchDeltaBypass } = require('./opt/delta-bypass');
const { freshEvar } = require('../kernel/fresh');
const { binlitTheory } = require('./ill/binlit-theory');

// ─── FFI control ────────────────────────────────────────────────────
// The _noFFI flag is deprecated — use matchOpts.provePersistent instead.
// Kept temporarily for backward compatibility with callers that haven't
// been updated yet. Will be removed once all callers thread matchOpts.

let _noFFI = true;
function setNoFFI(v) { _noFFI = !!v; }

// Tag ID cache for metavar checks
const _TAG_METAVAR = Store.TAG.metavar;

// ─── Binary Normalization ────────────────────────────────────────────
// Uses binlitTheory.canonicalize from ill/binlit-theory.js.
// Converts structural/hybrid binary (i/o/e chains with embedded binlits)
// to compact binlit form.

// ─── Backward proof cache (noFFI mode) ──────────────────────────────
// For deterministic predicates with known mode (input/output args),
// cache (pred, input_args...) → output_values. Avoids repeated O(N)
// backward clause resolution for the same inputs with different expected outputs.
// E.g., arr_get(BC, 931, <opcode>) — prove once, check cache 99 times.
//
// Soundness invariant: this cache is sound iff persistent context is monotonic
// (cached successes remain valid, failures may become stale). MUST be cleared
// at the start of each run/explore call — see forward.js and explore.js.

const _backwardCache = new Map();
// Monotonic counter for unique probe metavar names in backward cache.
// Prevents content-addressed aliasing: each probe gets fresh metavars
// so backward prover theta entries never leak across independent probes.
let _bwCacheProbeId = 0;
function clearBackwardCache() { _backwardCache.clear(); _bwCacheProbeId = 0; }
// Safety: clear backward cache when Store is reset (freevars become invalid).
Store.onClear(clearBackwardCache);

/**
 * Try to resolve a persistent goal via the backward proof cache.
 * Uses FFI mode metadata to identify input/output arg positions.
 *
 * @returns {Object|null|undefined}
 *   - undefined: not cacheable or cache miss (caller should prove normally)
 *   - null: cached failure (goal cannot be proved with these inputs)
 *   - { outputs: number[] }: cached success with output values
 */
function _tryBackwardCache(goal, slots, theta, calc, wantTerm) {
  const head = getPredicateHead(goal);
  if (!head) return undefined;

  const pm = ffi.parsedModes[head];
  if (!pm) return undefined;

  const arity = Store.arity(goal);
  if (arity === 0) return undefined;

  // Collect input args for cache key, output positions.
  // Store.put gives collision-free numeric key (content-addressed → unique u32).
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

  // Check cache
  const cached = _backwardCache.get(key);
  if (cached !== undefined) {
    if (cached === null) return null; // no solution exists

    const outputs = cached.outputs || cached; // support both old (array) and new ({ outputs, term }) format
    const term = cached.term;

    // If caller wants a term but cache entry has none, skip cache (re-prove with buildTerm)
    if (wantTerm && !term) {
      // Fall through to cache miss path to re-prove with buildTerm
    } else {
      // Verify/bind each output arg (direct accessors, no alloc)
      for (let oi = 0; oi < outputPositions.length; oi++) {
        const argHash = Store.child(goal, outputPositions[oi]);
        if (Store.isTerm(argHash) && Store.tagId(argHash) === _TAG_METAVAR) {
          // Metavar output — bind to cached value
          const slot = slots[argHash];
          if (slot !== undefined) theta[slot] = outputs[oi];
        } else {
          // Ground output — must match cached value
          if (argHash !== outputs[oi]) return null;
        }
      }
      return { outputs, term };
    }
  }

  // Cache miss — probe with fresh metavars for output positions
  const probeArgs = new Array(arity);
  const probeMetavars = [];
  for (let i = 0; i < arity; i++) probeArgs[i] = Store.child(goal, i);
  for (const oi of outputPositions) {
    const mv = Store.put('metavar', [`bwc_${_bwCacheProbeId++}`]);
    probeArgs[oi] = mv;
    probeMetavars.push(mv);
  }
  const probeGoal = Store.put(head, probeArgs);

  const backward = require('./prove');
  const result = backward.prove(probeGoal, calc.clauses, calc.definitions, {
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

  // prove.js returns ground theta (via _resolveSlots) — look up probe metavar bindings directly
  const thetaMap = new Map(result.theta);
  const outputValues = [];
  for (const mv of probeMetavars) {
    let val = thetaMap.get(mv);
    if (val === undefined) {
      // Try by name (metavar may have been aliased through unification chain)
      const mvName = Store.child(mv, 0);
      for (const [k, v] of thetaMap) {
        if (Store.isTerm(k) && Store.tagId(k) === _TAG_METAVAR && Store.child(k, 0) === mvName) {
          val = v; break;
        }
      }
    }
    outputValues.push(val !== undefined ? binlitTheory.canonicalize(val) : val);
  }

  const cacheEntry = wantTerm ? { outputs: outputValues, term: result.term } : outputValues;
  _backwardCache.set(key, cacheEntry);

  // Verify/bind against original goal's output args (direct accessors)
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

// ─── Profiling ──────────────────────────────────────────────────────

const PROFILE = typeof process !== 'undefined' && process.env.CALC_PERF_PROFILE === '1';
const TRACE_MATCHES = typeof process !== 'undefined' && process.env.CALC_TRACE_MATCHES === '1';
const profile = { matchTime: 0, matchCalls: 0, subTime: 0, subCalls: 0, proveTime: 0, proveCalls: 0 };
let _tmMatchCalls = 0;
const _tmLog = [];
function getTryMatchLog() { return _tmLog; }
function resetTryMatchLog() { _tmLog.length = 0; }
function getProfile() { return profile; }
function resetProfile() {
  profile.matchTime = profile.matchCalls = 0;
  profile.subTime = profile.subCalls = 0;
  profile.proveTime = profile.proveCalls = 0;
}

// JIT-friendly: early return when PROFILE=0 lets v8 inline/eliminate timing code.
function matchIdx(pattern, hash, theta, slots) {
  if (TRACE_MATCHES) _tmMatchCalls++;
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
function buildDiscriminatorIndex(rules) {
  const index = {};
  for (const rule of rules) {
    const gv = rule.discriminator && rule.discriminator.groundValue;
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
function detectFingerprintConfig(rules) {
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
      if (getPredicateHead(lp) !== bestPred) continue;
      const keyVar = Store.child(lp, keyPos);
      if (Store.tag(keyVar) !== 'metavar') continue;
      for (const lp2 of (r.antecedent.linear || [])) {
        if (lp2 === lp) continue;
        const pred2 = getPredicateHead(lp2);
        if (pred2 && Store.arity(lp2) === 1 && Store.child(lp2, 0) === keyVar) {
          pointerPred = pred2;
          break;
        }
      }
      if (pointerPred) break;
    }
    if (pointerPred) break;
  }

  return { pred: bestPred, keyPos, groundPos, pointerPred };
}

/**
 * Look up the fingerprint discriminator value from state using fpConfig.
 * Works for any program with a pointer predicate and discriminator predicate.
 *
 * @param {State} state - FactSet-based State object
 * @param {Object} fpConfig - Fingerprint config from detectFingerprintConfig
 * @returns {number|null} Fingerprint discriminator value or null
 */
const _binToInt = ffi.convert.binToInt;

function findFingerprintValue(state, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return null;

  // Step 1: Get pointer fact (e.g., pc(VALUE) — must be exactly one)
  const pointerTagId = Store.TAG[fpConfig.pointerPred];
  if (pointerTagId === undefined) return null;
  const pointerGroup = state.linear.group(pointerTagId);
  if (pointerGroup.length !== 1) return null;
  if (Store.arity(pointerGroup[0]) < 1) return null;
  const keyValue = Store.child(pointerGroup[0], 0);

  // Virtual fingerprint: O(1) ARRAY_TABLE lookup (no _byKey needed)
  if (fpConfig.type === 'virtual') {
    const arrayTagId = Store.TAG[fpConfig.arrayPred];
    if (arrayTagId === undefined) return null;
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length !== 1) return null;
    const arrayHash = Store.child(arrayGroup[0], 0);
    const elems = Store.getArrayElements(arrayHash);
    if (!elems) return null;
    const idx = _binToInt(keyValue);
    if (idx === null || idx < 0n || idx >= BigInt(elems.length)) return null;
    return elems[Number(idx)];
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

// ─── FFI Direct Bypass (re-exported from opt/ffi.js) ─────────────────

const { tryFFIDirect, provePersistentWithFFI } = require('./opt/ffi');


// ─── Backward Theta Resolution ──────────────────────────────────────

/**
// ─── Persistent Proving ─────────────────────────────────────────────

/**
 * Prove persistent patterns via state lookup → backward prove.
 * Naive version: state lookup → clause resolution (no FFI).
 *
 * @param {number[]} patterns - Persistent antecedent pattern hashes
 * @param {number} startIdx - Index to start proving from
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {State} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, types, backchainIndex } or null
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function provePersistentNaive(patterns, startIdx, theta, slots, state, calc, evidenceOut) {
  let idx = startIdx;
  while (idx < patterns.length) {
    const goal = subApplyIdx(patterns[idx], theta, slots);

    // 1. State lookup — check if fact already exists in state.persistent
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
            if (matchIdx(pattern, hn, theta, slots)) {
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

    // 2. Backward proof cache (noFFI only)
    if (_noFFI && calc && calc.clauses) {
      const wantTerm = !!evidenceOut;
      const cacheResult = _tryBackwardCache(goal, slots, theta, calc, wantTerm);
      if (cacheResult !== undefined) {
        if (cacheResult === null) {
          break; // cached: no solution
        }
        // Cache hit — bindings already applied by _tryBackwardCache
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: { success: true }, term: cacheResult.term });
        idx++;
        continue;
      }
    }

    // 3. Clause resolution
    if (calc && calc.clauses && calc.definitions) {
      // Check for external freevars (symbolic values from forward engine state,
      // e.g. _Sender). If present, we run the prover but reject results where
      // the prover bound external freevars (indicating it assumed specific values).
      const externals = collectExternalFreevars(goal, slots);

      const backward = require('./prove');
      const t0 = PROFILE ? performance.now() : 0;
      const wantTerm = !!evidenceOut; // Build proof terms when collecting evidence
      const result = backward.prove(goal, calc.clauses, calc.definitions, {
        maxDepth: _noFFI ? 20000 : 50,
        index: calc.backchainIndex,
        buildTerm: wantTerm,
        allBuckets: _noFFI,
        useFFI: !_noFFI
      });
      if (PROFILE) {
        profile.proveTime += performance.now() - t0;
        profile.proveCalls++;
      }
      if (result.success) {
        // Reject if the prover bound external freevars — the result depends
        // on arbitrary assumptions about symbolic constants (e.g. and(_Sender,
        // mask, Z) → prover binds _Sender=0, returns Z=0).
        if (externals && proverBoundExternals(result.theta, externals)) break;

        // prove.js returns ground theta (via _resolveSlots) — extract slot bindings directly
        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) {
            let val = rt[ri][1];
            if (_noFFI) val = binlitTheory.canonicalize(val);
            theta[slot] = val;
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

/**
 * Prove persistent patterns — dispatches to FFI-enhanced or naive.
 * Default: FFI-enhanced (current behavior). Use provePersistentNaive for bare profile.
 */
const provePersistentGoals = provePersistentWithFFI;

// ─── Existential Resolution ─────────────────────────────────────────

/**
 * Resolve existential variables in theta after matching.
 * Existential slots are consequent-only metavars (from ∃-quantified positions).
 *
 * Resolution via provePersistentGoals:
 * 1. State lookup → match against persistent facts
 * 2. Backward prove → FFI (optimization) | clauses
 * 3. All fail → freshEvar (symbolic witness, constraint accumulates in state)
 *
 * Always returns true — exists never blocks a rule from firing.
 */
function resolveExistentials(theta, slots, rule, state, calc, matchOpts) {
  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return true;

  // Collect existential goals in consequent-persistent order (preserves dependency chain).
  // existentialSlots are in Set insertion order which may NOT respect dependencies.
  // rule.consequent.persistent preserves the .ill syntax order which IS dependency order.
  const goalSet = new Set();
  for (const slot of rule.existentialSlots) {
    const sg = rule.existentialGoals[slot];
    if (sg) for (const g of sg) goalSet.add(g);
  }
  const goals = [];
  for (const p of (rule.consequent.persistent || [])) {
    if (goalSet.has(p)) goals.push(p);
  }

  // Prove goals via provePersistent callback (from matchOpts or fallback to legacy)
  if (goals.length > 0) {
    const proveFn = (matchOpts && matchOpts.provePersistent)
      ? matchOpts.provePersistent
      : (_noFFI ? provePersistentNaive : provePersistentGoals);
    proveFn(goals, 0, theta, slots, state, calc);
    // Don't check return value — even if some goals fail,
    // execution continues. Unresolved slots get freshEvar below.
  }

  // Remaining unbound slots → freshEvar (symbolic witness, constraint accumulates)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;  // Always succeeds — exists never blocks the rule
}

// ─── Compiled Persistent Step Execution ──────────────────────────────

const _ffiIsGround = ffi.convert.isGround;
const _ffiParsedModes = ffi.parsedModes;

// Pre-allocated argument buffer for compiled persistent steps.
// V8: literal for packed SMI. Arity assertion same as _ffiArgs above.
const _psArgs = [0, 0, 0, 0];
for (const key in _ffiParsedModes) {
  if (_ffiParsedModes[key].length > 4) {
    throw new Error(`FFI '${key}' arity ${_ffiParsedModes[key].length} exceeds _psArgs buffer size 4`);
  }
}

/**
 * Execute a compiled persistent step spec against theta.
 * Spec is { ffiFn, argSpecs, arity, multiModal, _slots }.
 * Returns true (proved), false (definitive failure), or null (needs generic fallback).
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
    const slots = spec._slots;
    for (let fi = 0; fi < ft.length; fi++) {
      const s = slots[ft[fi][0]];
      if (s !== undefined) theta[s] = ft[fi][1];
    }
    return true;
  }
  if (result && !result.success && !result.reason) return false;
  return null;
}

// ─── Pattern Matching ───────────────────────────────────────────────

// Reusable work buffers (avoids allocation per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);

// Pooled Maps for tryMatch (cleared on each call, copied on success)
const _poolConsumed = new Map();
const _poolReserved = new Map();
// Max metavar slots per rule. 64 covers observed max (~32).
// Assertion in tryMatch guards against silent overflow.
const MAX_SLOTS = 64;
const _poolTheta = new Array(MAX_SLOTS);
const _poolPreservedCount = new Map();

/**
 * Match one linear pattern against state facts.
 * Dispatches across three strategies in order:
 *   A. Delta bypass — direct child extraction for flat delta patterns
 *   B. Secondary index — O(1) lookup for fingerprint predicate
 *   C. General matching — full unification against all indexed candidates
 *
 * State is a FactSet-based State object. Candidates come from
 * state.linear.group(tagIdx) instead of a separate stateIndex.
 *
 * Mutates theta/consumed/reserved on success. Returns true if matched.
 */
function matchOnePattern(pattern, origPos, rule, state, theta, slots,
                         consumed, reserved, preservedCount, usePreserved) {
  const meta = rule.linearMeta[pattern];
  const pred = meta.pred;
  const isPreserved = usePreserved && (preservedCount.get(pattern) || 0) > 0;
  const tagIdx = pred ? Store.TAG[pred] : -1;

  // Strategy A: Delta bypass — direct child extraction for flat delta patterns
  if (matchDeltaBypass(pattern, origPos, rule, state, theta,
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
 *   remaining = antecedent linear patterns
 *   persistentIdx = 0
 *
 *   while remaining patterns or unproved persistent goals:
 *     Phase 1 — Match linear patterns against Δ:
 *       For each pattern p in remaining:
 *         if p has unbound persistent deps → defer(p)
 *         else → matchOnePattern(p, Δ, θ)
 *           dispatches: delta bypass → secondary index → general unification
 *     Phase 2 — Prove persistent goals:
 *       Compiled FFI fast path (persistentSteps) → generic provePersistentGoals
 *       (FFI → state lookup → backward clause resolution)
 *     if no progress and work remains → fail
 *
 * Termination: each iteration either binds a pattern/goal (progress)
 * or fails. Maximum iterations bounded by |Γ_lin| + |Γ_pers| + 10.
 *
 * Returns persistentIdx (>= 0) on success, -1 on failure.
 */
function matchAllLinear(rule, state, theta, slots, consumed, reserved,
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

      if (!matchOnePattern(pattern, origPos, rule, state, theta, slots,
                            consumed, reserved, preservedCount, usePreserved)) {
        return -1;
      }
      madeProgress = true;
    }

    rpLen = deferredLen;

    // Phase 2: Prove persistent patterns.
    // When collecting evidence: skip the compiled FFI fast path (persistentSteps)
    // because executePersistentStep doesn't record HOW the goal was proved — it
    // just returns true/false. Fall through to provePersistent which captures
    // evidence per goal. This is consistent with "FFI is optimization" — when we
    // need proof terms, we use the slower but evidence-producing path.
    const useCompiledSteps = matchOpts && matchOpts.useCompiledSteps;
    if (!evidenceOut && useCompiledSteps) {
      const persSteps = rule.persistentSteps;
      if (persSteps) {
        while (persistentIdx < persistentList.length) {
          const step = persSteps[persistentIdx];
          if (!step) break;  // no compiled step → fall through to generic
          const r = executePersistentStep(step, theta);
          if (r === true) { persistentIdx++; madeProgress = true; continue; }
          if (r === false) break;  // FFI advisory failure — fall through to generic path
          break;  // null → needs generic path (non-ground input, etc.)
        }
      }
    }
    const proveFn = (matchOpts && matchOpts.provePersistent)
      ? matchOpts.provePersistent
      : (_noFFI ? provePersistentNaive : provePersistentGoals);
    const newIdx = proveFn(persistentList, persistentIdx, theta, slots, state, calc, evidenceOut);
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
 * Orchestrates: setup → matchAllLinear → existential resolution → result.
 * Returns { rule, theta, slots, consumed, optimized } or null.
 */
function tryMatch(rule, state, calc, matchOpts) {
  const _tmStart = TRACE_MATCHES ? _tmMatchCalls : 0;

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
  const result = matchAllLinear(rule, state, _poolTheta, slots, _poolConsumed, _poolReserved,
                                _poolPreservedCount, usePreserved, persistentList, calc, evidenceOut, matchOpts);

  if (result < 0) {
    if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
    undoRestore(_poolTheta, topUndo);
    return null;
  }

  // Resolve existential slots (always succeeds — binds to freshEvar on failure)
  if (rule.existentialSlots && rule.existentialSlots.length > 0) {
    resolveExistentials(_poolTheta, slots, rule, state, calc, matchOpts);
  }

  // Copy on success (rare path — most tryMatch calls fail)
  const consumed = {};
  _poolConsumed.forEach((v, k) => { consumed[k] = v; });
  const theta = _poolTheta.slice(0, metavarCount);

  if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: true });
  undoDiscard(topUndo);
  const m = { rule, theta, slots, consumed, optimized: !!usePreserved };
  if (wantEvidence) m.persistentEvidence = evidenceOut;
  return m;
}

// ─── Unified Loli Matching ──────────────────────────────────────────

/**
 * Try to fire a loli(trigger, {body}) fact from linear state.
 *
 * Loli facts are produced by rule consequents (e.g., guard -o {result}).
 * Firing one is an ILL derivation: loli_l(fact, antecedent_proof, continuation).
 * Unlike compiled rules (persistent clauses in gamma), lolis are LINEAR —
 * consumed from delta, no copy wrapper in the proof term.
 *
 * Trigger forms:
 *   - Linear trigger: match atoms/predicates against state.linear
 *   - Persistent trigger (!P): prove via state/FFI/backward
 *   - Mixed (tensor of linear + persistent): both phases
 *
 * When matchOpts.evidence is true, returns real theta/slots/persistentEvidence
 * plus loliHash — everything buildGuidedTerm needs for the loli_l proof term.
 * When evidence not requested, theta/slots are empty (zero allocation overhead).
 *
 * Key insight: loli triggers are always ground (produced by prior rule firings
 * after full substitution). Theta bindings are vacuous in practice, but the
 * builder still needs persistent evidence for !-trigger goals.
 *
 * Returns a match object compatible with explore()/applyMatch(), or null.
 */
function matchLoli(h, state, calc, matchOpts) {
  const trigger = Store.child(h, 0);
  const body = Store.child(h, 1);
  const compTag = calc?.roles?.computation || 'monad';
  const bodyInner = Store.tag(body) === compTag ? Store.child(body, 0) : body;

  // Flatten trigger into linear + persistent components
  const { linear: linearTriggers, persistent: persistentTriggers } = flattenTensor(trigger);

  // Build metavar slots for trigger + body
  const allVars = new Set();
  collectMetavars(trigger, allVars);
  collectMetavars(bodyInner, allVars);
  const slots = {};
  let slotIdx = 0;
  for (const v of allVars) slots[v] = slotIdx++;
  const theta = new Array(slotIdx);

  const topUndo = undoSave();
  const consumed = { [h]: 1 };

  // Phase 1: Match linear trigger patterns against state.linear
  for (let ti = 0; ti < linearTriggers.length; ti++) {
    const pattern = linearTriggers[ti];
    const pred = getPredicateHead(pattern);
    const trigTagId = pred ? Store.TAG[pred] : -1;
    let found = false;

    // Get candidates from the right group
    const candidates = trigTagId >= 0
      ? state.linear.group(trigTagId)
      : state.groupForPred(pred);

    for (let ci = 0; ci < candidates.length; ci++) {
      const fact = candidates[ci];
      if (fact === h) continue;  // Don't match the loli against itself
      const factTag = trigTagId >= 0 ? trigTagId : Store.tagId(fact);
      const factCount = state.linear.count(factTag, fact);
      if (factCount <= 0) continue;
      // Check if already consumed by an earlier trigger pattern
      if (consumed[fact] && factCount - (consumed[fact] || 0) <= 0) continue;
      if (getPredicateHead(fact) !== pred) continue;

      const saved = undoSave();
      if (matchIdx(pattern, fact, theta, slots)) {
        undoDiscard(saved);
        consumed[fact] = (consumed[fact] || 0) + 1;
        found = true;
        break;
      }
      undoRestore(theta, saved);
    }
    if (!found) {
      undoRestore(theta, topUndo);
      return null;
    }
  }

  // Phase 2: Prove persistent trigger patterns
  const wantEvidence = matchOpts && matchOpts.evidence;
  const evidenceOut = wantEvidence ? [] : null;
  if (persistentTriggers.length > 0) {
    const proveFn = (matchOpts && matchOpts.provePersistent)
      ? matchOpts.provePersistent
      : (_noFFI ? provePersistentNaive : provePersistentGoals);
    const proved = proveFn(
      persistentTriggers, 0, theta, slots, state, calc, evidenceOut
    );
    if (proved < persistentTriggers.length) {
      undoRestore(theta, topUndo);
      return null;
    }
  }

  // Instantiate body with matched bindings
  const instantiated = subApplyIdx(bodyInner, theta, slots);
  undoDiscard(topUndo);

  // Expand choices in body (handles oplus/with in loli body)
  const produced = flattenTensor(instantiated);
  const consequentAlts = expandConsequentChoices(produced);
  const name = 'loli:' + (getPredicateHead(trigger) || 'trigger');

  const result = {
    rule: {
      name,
      consequent: produced,
      consequentAlts,
      preserved: null,
      compiledConseqLinear: null,
      compiledConseqPersistent: null,
    },
    theta: wantEvidence ? theta.slice(0, slotIdx) : [],
    slots: wantEvidence ? slots : {},
    consumed,
    optimized: false,
  };
  if (wantEvidence) {
    result.persistentEvidence = evidenceOut;
    result.loliHash = h;
  }
  return result;
}

module.exports = {
  // Profiling
  getProfile,
  resetProfile,
  getTryMatchLog,
  resetTryMatchLog,
  // Rule indexing
  buildDiscriminatorIndex,
  detectFingerprintConfig,
  findFingerprintValue,
  // FFI control
  setNoFFI,
  clearBackwardCache,
  // Persistent proving
  provePersistentGoals,
  provePersistentNaive,
  tryFFIDirect,
  executePersistentStep,
  // Existential resolution
  resolveExistentials,
  // Pattern matching
  tryMatch,
  // Loli matching
  matchLoli,
};
