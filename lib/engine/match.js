/**
 * Pattern matching, indexing, and persistent proving.
 *
 * Matching pipeline: state indexing → pattern matching → persistent proving.
 * Contains all matching-related functionality:
 *   - Profiling instrumentation
 *   - State/rule indexing (buildStateIndex, buildDiscriminatorIndex)
 *   - Persistent proving (state lookup → backward prove [FFI | clauses])
 *   - Existential resolution
 *   - Pattern matching (tryMatch pipeline)
 *   - Loli continuation matching
 */

const Store = require('../kernel/store');
const { isPredTag, getPredicateHead } = require('../kernel/ast');
const { matchIndexed: _matchIdx, undoSave, undoRestore, undoDiscard } = require('../kernel/unify');
const { applyIndexed: _subApplyIdx } = require('../kernel/substitute');
const ffi = require('./ffi');
const { flattenTensor, expandConsequentChoices, collectMetavars } = require('./compile');
const { freshEvar } = require('../kernel/fresh');

// ─── Profiling ──────────────────────────────────────────────────────

const PROFILE = process.env.CALC_PROFILE === '1';
const TRACE_MATCHES = process.env.CALC_TRACE_MATCHES === '1';
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

// ─── State Indexing ─────────────────────────────────────────────────

/**
 * Build index from state facts, grouped by predicate head.
 * Optional secondary index for fingerprint predicate.
 * Optional persistent predicate set for O(1) state lookup guard.
 */
function buildStateIndex(linear, fpConfig, persistent) {
  const byPred = {};
  const byKey = fpConfig ? {} : null;
  const fpPred = fpConfig ? fpConfig.pred : null;
  const fpKeyPos = fpConfig ? fpConfig.keyPos : -1;

  const loliTagId = Store.TAG.loli;
  byPred._loli = [];

  for (const hStr of Object.keys(linear)) {
    const h = Number(hStr);
    const pred = getPredicateHead(h);
    if (pred) {
      if (!byPred[pred]) byPred[pred] = [];
      byPred[pred].push(h);
      if (pred === fpPred && Store.arity(h) > fpKeyPos) {
        byKey[Store.child(h, fpKeyPos)] = h;
      }
    } else if (Store.tagId(h) === loliTagId) {
      byPred._loli.push(h);
    } else {
      if (!byPred['*']) byPred['*'] = [];
      byPred['*'].push(h);
    }
  }

  byPred._byKey = byKey;
  byPred._fpPred = fpPred;
  byPred._fpKeyPos = fpKeyPos;

  // Build persistent predicate set for O(1) state lookup guard.
  // Lazy-growing: only adds, never removes. False positives OK (extra scan),
  // false negatives NOT OK (missed state lookup → correctness bug).
  if (persistent) {
    const preds = new Set();
    for (const h in persistent) {
      const p = getPredicateHead(Number(h));
      if (p) preds.add(p);
    }
    byPred._persistentPreds = preds;
  }

  return byPred;
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

  // Auto-detect pointer predicate (unary pattern sharing a var with discriminator key)
  let pointerPred = null;
  for (const r of rules) {
    if (!r.discriminator || r.discriminator.pred !== bestPred) continue;
    for (const lp of (r.antecedent.linear || [])) {
      if (getPredicateHead(lp) !== bestPred) continue;
      const keyVar = Store.child(lp, keyPos);
      if (Store.tag(keyVar) !== 'freevar') continue;
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
 * @param {Object} stateIndex - Output of buildStateIndex()
 * @param {Object} fpConfig - Fingerprint config from detectFingerprintConfig
 * @returns {number|null} Fingerprint discriminator value or null
 */
function findFingerprintValue(stateIndex, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return null;

  // Step 1: Get pointer fact (e.g., pc(VALUE) — must be exactly one)
  const pointerFacts = stateIndex[fpConfig.pointerPred];
  if (!pointerFacts || pointerFacts.length !== 1) return null;
  if (Store.arity(pointerFacts[0]) < 1) return null;
  const keyValue = Store.child(pointerFacts[0], 0);

  // Step 2: O(1) lookup via secondary index (e.g., _byKey[pcValue] → code fact)
  if (stateIndex._byKey) {
    const fact = stateIndex._byKey[keyValue];
    if (fact && Store.arity(fact) > fpConfig.groundPos) {
      return Store.child(fact, fpConfig.groundPos);
    }
  }

  // Fallback: scan facts of discriminator predicate
  const discFacts = stateIndex[fpConfig.pred];
  if (!discFacts) return null;
  for (const h of discFacts) {
    if (Store.arity(h) <= fpConfig.keyPos) continue;
    if (Store.child(h, fpConfig.keyPos) !== keyValue) continue;
    return Store.child(h, fpConfig.groundPos);
  }
  return null;
}

// ─── FFI Direct Bypass ──────────────────────────────────────────────

const _ffiMeta = ffi.defaultMeta;
const _ffiParsedModes = {};
for (const key in _ffiMeta) {
  _ffiParsedModes[key] = ffi.mode.parseMode(_ffiMeta[key].mode);
}
const _ffiArgs = [0, 0, 0, 0];

/** Try FFI directly, bypassing full prove() machinery */
function tryFFIDirect(goal) {
  const goalTag = Store.tag(goal);
  if (!goalTag) return null;

  let head;
  if (isPredTag(goalTag)) head = goalTag;
  else if (goalTag === 'atom') head = Store.child(goal, 0);
  else return null;

  const meta = _ffiMeta[head];
  if (!meta) return null;
  const fn = ffi.get(meta.ffi);
  if (!fn) return null;

  const modes = _ffiParsedModes[head];
  const goalArity = Store.arity(goal);
  if (goalArity !== modes.length) return null;

  for (let i = 0; i < goalArity; i++) {
    const c = Store.child(goal, i);
    if (!meta.multiModal && modes[i] === '+' && !ffi.convert.isGround(c)) return null;
    _ffiArgs[i] = c;
  }

  const result = fn(_ffiArgs);
  // FFI failure with reason (mode_mismatch, conversion_failed, division_by_zero)
  // is non-definitive — fall back to state lookup / backward proving.
  // Failures WITHOUT reason (e.g. neq(5,5)) are definitive mathematical "no".
  if (result && !result.success && result.reason) return null;
  return result;
}

// ─── Persistent Proving ─────────────────────────────────────────────

/**
 * Prove persistent patterns via state lookup → backward prove [FFI | clauses].
 * Shared by tryMatch (compiled rules) and matchLoli (loli continuations).
 *
 * Two-level resolution:
 *   1. State lookup — match pattern against state.persistent facts
 *   2. Backward prove — compute via:
 *      2a. FFI (O(1) optimization for arithmetic predicates)
 *      2b. Clause resolution (full backward chaining)
 *
 * @param {number[]} patterns - Persistent antecedent pattern hashes
 * @param {number} startIdx - Index to start proving from
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object} state - { linear, persistent }
 * @param {Object|null} calc - { clauses, types, backwardIndex } or null
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function provePersistentGoals(patterns, startIdx, theta, slots, state, calc) {
  // Use pre-built predicate set from stateIndex (O(1) guard).
  // Falls back to lazy-build if not available (e.g., direct calls without stateIndex).
  let persistentPreds = (state.index && state.index._persistentPreds) || null;

  let idx = startIdx;
  while (idx < patterns.length) {

    // 1. State lookup — check if fact already exists in state.persistent
    {
      const pattern = patterns[idx];
      const pPred = getPredicateHead(pattern);

      // Lazy fallback: build predicate set if not provided by stateIndex
      if (persistentPreds === null) {
        persistentPreds = new Set();
        for (const h in state.persistent) {
          const p = getPredicateHead(Number(h));
          if (p) persistentPreds.add(p);
        }
      }

      // Only scan if predicate is actually present in state (O(1) guard)
      if (persistentPreds.has(pPred)) {
        let foundInState = false;
        for (const h in state.persistent) {
          const hn = Number(h);
          if (getPredicateHead(hn) !== pPred) continue;
          const savedUndo = undoSave();
          if (matchIdx(pattern, hn, theta, slots)) {
            foundInState = true;
            undoDiscard(savedUndo);
            break;
          }
          undoRestore(theta, savedUndo);
        }
        if (foundInState) {
          idx++;
          continue;
        }
      }
    }

    // 2. Backward prove — compute new facts
    const goal = subApplyIdx(patterns[idx], theta, slots);

    // 2a. FFI (O(1) optimization of backward proving)
    const ffiResult = tryFFIDirect(goal);
    if (ffiResult) {
      if (ffiResult.success) {
        const ft = ffiResult.theta;
        for (let fi = 0; fi < ft.length; fi++) {
          const slot = slots[ft[fi][0]];
          if (slot !== undefined) theta[slot] = ft[fi][1];
        }
        idx++;
        continue;
      }
      break; // FFI says false — definitive failure
    }

    // 2b. Clause resolution
    if (calc && calc.clauses && calc.types) {
      const backward = require('./prove');
      const t0 = PROFILE ? performance.now() : 0;
      const result = backward.prove(goal, calc.clauses, calc.types, {
        maxDepth: 50,
        index: calc.backwardIndex
      });
      if (PROFILE) {
        profile.proveTime += performance.now() - t0;
        profile.proveCalls++;
      }
      if (result.success) {
        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) theta[slot] = rt[ri][1];
        }
        idx++;
        continue;
      }
    }
    break;
  }
  return idx;
}

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
function resolveExistentials(theta, slots, rule, state, calc) {
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

  // Prove goals via two-level fallback (state lookup → backward prove [FFI | clauses])
  if (goals.length > 0) {
    provePersistentGoals(goals, 0, theta, slots, state, calc);
    // Don't check return value — even if some goals fail,
    // execution continues. Unresolved slots get freshEvar below.
  }

  // Remaining unbound slots → freshEvar (symbolic witness, constraint accumulates)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;  // Always succeeds — exists never blocks the rule
}

// ─── Pattern Matching ───────────────────────────────────────────────

// Reusable work buffers (avoids allocation per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);
const _deltaWritten = new Array(8);

/**
 * Match one linear pattern against state facts.
 * Dispatches across three strategies in order:
 *   A. Delta bypass — direct child extraction for flat delta patterns
 *   B. Secondary index — O(1) lookup for fingerprint predicate
 *   C. General matching — full unification against all indexed candidates
 *
 * Mutates theta/consumed/reserved on success. Returns true if matched.
 */
function matchOnePattern(pattern, origPos, rule, index, state, theta, slots,
                         consumed, reserved, preservedCount, usePreserved) {
  const meta = rule.linearMeta[pattern];
  const pred = meta.pred;
  const isPreserved = usePreserved && preservedCount[pattern] > 0;

  // Strategy A: Delta bypass — direct child extraction for flat delta patterns
  const role = rule.patternRoles[origPos];
  if (role && role.type === 'delta' && role.flat && !isPreserved) {
    const bindings = role.bindings;
    const gc = role.groundChecks;
    const candidates = index[pred] || [];
    for (const h of candidates) {
      const available = (state.linear[h] || 0) - (consumed[h] || 0) - (reserved[h] || 0);
      if (available <= 0) continue;

      if (gc.length > 0) {
        let gcOk = true;
        for (let gi = 0; gi < gc.length; gi++) {
          if (Store.child(h, gc[gi].pos) !== gc[gi].value) { gcOk = false; break; }
        }
        if (!gcOk) continue;
      }

      let writtenCount = 0;
      let bindOk = true;
      for (let bi = 0; bi < bindings.length; bi++) {
        const val = Store.child(h, bindings[bi].pos);
        const slot = bindings[bi].slot;
        const existing = theta[slot];
        if (existing !== undefined) {
          if (existing !== val) { bindOk = false; break; }
        } else {
          theta[slot] = val;
          _deltaWritten[writtenCount++] = slot;
        }
      }

      if (bindOk) {
        consumed[h] = (consumed[h] || 0) + 1;
        return true;
      }

      for (let wi = 0; wi < writtenCount; wi++) theta[_deltaWritten[wi]] = undefined;
    }
  }

  // Strategy B: Secondary index O(1) lookup for fingerprint predicate
  if (pred === index._fpPred && index._byKey && meta.secondaryKeyPattern !== null) {
    const keyValue = subApplyIdx(meta.secondaryKeyPattern, theta, slots);
    const codeFact = index._byKey[keyValue];
    if (codeFact) {
      const available = (state.linear[codeFact] || 0) - (consumed[codeFact] || 0) - (reserved[codeFact] || 0);
      if (available > 0) {
        const savedUndo = undoSave();
        if (matchIdx(pattern, codeFact, theta, slots)) {
          if (isPreserved) {
            reserved[codeFact] = (reserved[codeFact] || 0) + 1;
            preservedCount[pattern]--;
          } else {
            consumed[codeFact] = (consumed[codeFact] || 0) + 1;
          }
          return true;
        }
        undoRestore(theta, savedUndo);
      }
    }
  }

  // Strategy C: General matching against all indexed candidates
  let candidates;
  if (pred) {
    candidates = index[pred] || [];
  } else {
    candidates = index['*'] || Object.keys(state.linear).map(Number);
  }

  for (const h of candidates) {
    const available = (state.linear[h] || 0) - (consumed[h] || 0) - (reserved[h] || 0);
    if (available <= 0) continue;

    const savedUndo = undoSave();
    if (matchIdx(pattern, h, theta, slots)) {
      if (isPreserved) {
        reserved[h] = (reserved[h] || 0) + 1;
        preservedCount[pattern]--;
      } else {
        consumed[h] = (consumed[h] || 0) + 1;
      }
      return true;
    }
    undoRestore(theta, savedUndo);
  }

  return false;
}

/**
 * Match all linear patterns via worklist, interleaved with persistent proving.
 * Defers patterns whose persistent dependencies aren't yet bound.
 *
 * Returns persistentIdx (>= 0) on success, -1 on failure.
 */
function matchAllLinear(rule, index, state, theta, slots, consumed, reserved,
                        preservedCount, usePreserved, persistentList, calc) {
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

      if (!matchOnePattern(pattern, origPos, rule, index, state, theta, slots,
                            consumed, reserved, preservedCount, usePreserved)) {
        return -1;
      }
      madeProgress = true;
    }

    rpLen = deferredLen;

    // Phase 2: Prove persistent patterns (state lookup → backward prove [FFI | clauses])
    const newIdx = provePersistentGoals(persistentList, persistentIdx, theta, slots, state, calc);
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
  const consumed = {};
  const reserved = {};
  const index = state.index || buildStateIndex(state.linear);

  const topUndo = undoSave();
  const { metavarSlots: slots, metavarCount } = rule;
  const theta = new Array(metavarCount);

  const preservedCount = {};
  const preserved = rule.preserved;
  const usePreserved = matchOpts && matchOpts.optimizePreserved && preserved && preserved.length > 0;
  if (usePreserved) {
    for (const h of preserved) {
      preservedCount[h] = (preservedCount[h] || 0) + 1;
    }
  }

  const persistentList = rule.antecedent.persistent || [];
  const result = matchAllLinear(rule, index, state, theta, slots, consumed, reserved,
                                preservedCount, usePreserved, persistentList, calc);

  if (result < 0) {
    if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
    undoRestore(theta, topUndo);
    return null;
  }

  // Resolve existential slots (always succeeds — binds to freshEvar on failure)
  if (rule.existentialSlots && rule.existentialSlots.length > 0) {
    resolveExistentials(theta, slots, rule, state, calc);
  }

  if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: true });
  undoDiscard(topUndo);
  return { rule, theta, slots, consumed, optimized: !!usePreserved };
}

// ─── Unified Loli Matching ──────────────────────────────────────────

/**
 * Try to fire a loli(trigger, {body}) from state using the shared
 * persistent proving pipeline. Handles all trigger forms:
 *   - Linear trigger: match against state.linear
 *   - Persistent trigger (!P): prove via state/FFI/backward
 *   - Mixed (tensor of linear + persistent): both phases
 *
 * Returns a match object compatible with explore()/applyMatch(), or null.
 */
function matchLoli(h, state, calc) {
  const trigger = Store.child(h, 0);
  const body = Store.child(h, 1);
  const bodyInner = Store.tag(body) === 'monad' ? Store.child(body, 0) : body;

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
    let found = false;
    for (const factStr of Object.keys(state.linear)) {
      const fact = Number(factStr);
      if (fact === h) continue;  // Don't match the loli against itself
      if (state.linear[fact] <= 0) continue;
      // Check if already consumed by an earlier trigger pattern
      if (consumed[fact] && state.linear[fact] - (consumed[fact] || 0) <= 0) continue;
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
  if (persistentTriggers.length > 0) {
    const proved = provePersistentGoals(persistentTriggers, 0, theta, slots, state, calc);
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

  return {
    rule: {
      name,
      consequent: produced,
      consequentAlts,
      preserved: null,
      compiledConseqLinear: null,
      compiledConseqPersistent: null,
    },
    theta: [],
    slots: {},
    consumed,
    optimized: false,
  };
}

/** Find first fireable loli continuation (for committed-choice run) */
function matchFirstLoli(state, calc, stateIndex) {
  // Use _loli index bucket if available (O(1) vs O(n) key scan)
  if (stateIndex && stateIndex._loli) {
    for (const h of stateIndex._loli) {
      const m = matchLoli(h, state, calc);
      if (m) return m;
    }
    return null;
  }
  // Fallback: scan all keys (when no stateIndex provided)
  const loliTagId = Store.TAG.loli;
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) !== loliTagId) continue;
    const m = matchLoli(h, state, calc);
    if (m) return m;
  }
  return null;
}

module.exports = {
  // Profiling
  getProfile,
  resetProfile,
  getTryMatchLog,
  resetTryMatchLog,
  // State indexing
  buildStateIndex,
  // Rule indexing
  buildDiscriminatorIndex,
  detectFingerprintConfig,
  findFingerprintValue,
  // Persistent proving
  provePersistentGoals,
  tryFFIDirect,
  // Existential resolution
  resolveExistentials,
  // Pattern matching
  tryMatch,
  // Loli matching
  matchLoli,
  matchFirstLoli,
};
