/**
 * Forward Chaining Engine — runtime matching and execution.
 *
 * Multiset rewriting with committed choice (no backtracking).
 * Runs until quiescence (no rules can fire).
 *
 * State: { linear: { hash: count }, persistent: { hash: true } }
 *
 * Architecture:
 *   compile.js  — rule preparation (compileRule)
 *   forward.js  — matching + execution (tryMatch, findMatch, applyMatch, run)
 *   rule-analysis.js — static analysis (deltas, pattern roles)
 *   disc-tree.js — discrimination tree indexing
 */

const Store = require('../kernel/store');
const { NON_PRED_TAGS, getPredicateHead } = require('../kernel/ast');
const { matchIndexed: _matchIdx, undoSave, undoRestore, undoDiscard } = require('../kernel/unify');
const { applyIndexed: _subApplyIdx, subCompiled } = require('../kernel/substitute');
const ffi = require('./ffi');
const { compileRule, flattenTensor, unwrapMonad, expandItem, expandConsequentChoices, collectMetavars } = require('./compile');
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
 */
function buildStateIndex(linear, fpConfig) {
  const byPred = {};
  const byKey = fpConfig ? {} : null;
  const fpPred = fpConfig ? fpConfig.pred : null;
  const fpKeyPos = fpConfig ? fpConfig.keyPos : -1;

  for (const hStr of Object.keys(linear)) {
    const h = Number(hStr);
    const pred = getPredicateHead(h);
    if (pred) {
      if (!byPred[pred]) byPred[pred] = [];
      byPred[pred].push(h);
      if (pred === fpPred && Store.arity(h) > fpKeyPos) {
        byKey[Store.child(h, fpKeyPos)] = h;
      }
    } else {
      if (!byPred['*']) byPred['*'] = [];
      byPred['*'].push(h);
    }
  }

  byPred._byKey = byKey;
  byPred._fpPred = fpPred;
  byPred._fpKeyPos = fpKeyPos;
  byPred.codeByPC = byKey;
  return byPred;
}

// ─── Rule Indexing ──────────────────────────────────────────────────

/** Group rules by trigger predicates */
function buildRuleIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.triggerPreds && rule.triggerPreds.length > 0) {
      for (const pred of rule.triggerPreds) {
        if (!index[pred]) index[pred] = [];
        index[pred].push(rule);
      }
    } else {
      if (!index['*']) index['*'] = [];
      index['*'].push(rule);
    }
  }
  return index;
}

/** Map discriminator ground value → rule for O(1) lookup */
function buildOpcodeIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.opcodeHash) index[rule.opcodeHash] = rule;
  }
  return index;
}

/**
 * Auto-detect fingerprint configuration from compiled rules.
 * Finds dominant discriminator predicate and pointer predicate.
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

/** EVM strategy: PC → code → opcode → rule in O(1) */
function evmStrategy(stateIndex, opcodeIndex) {
  const pcFacts = stateIndex['pc'];
  if (!pcFacts || pcFacts.length !== 1) return null;

  const pcHash = pcFacts[0];
  if (Store.arity(pcHash) < 1) return null;
  const pcValue = Store.child(pcHash, 0);

  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;

  for (const codeHash of codeFacts) {
    if (Store.arity(codeHash) < 2) continue;
    if (Store.child(codeHash, 0) !== pcValue) continue;
    const rule = opcodeIndex[Store.child(codeHash, 1)];
    if (rule) return rule;
  }
  return null;
}

// ─── Persistent Proving ─────────────────────────────────────────────

/**
 * Prove persistent patterns via FFI → state lookup → backward chaining.
 * Shared by tryMatch (compiled rules) and matchLoli (loli continuations).
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
  let idx = startIdx;
  while (idx < patterns.length) {
    const goal = subApplyIdx(patterns[idx], theta, slots);

    // 1. Try FFI directly
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

    // 2. Check persistent state facts (pattern matching, not instantiated goal)
    {
      const pattern = patterns[idx];
      const pPred = getPredicateHead(pattern);
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

    // 3. Backward chaining fallback
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
  if (!NON_PRED_TAGS.has(goalTag)) head = goalTag;
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

// ─── Existential Resolution ─────────────────────────────────────────

/**
 * Resolve existential variables in theta after matching.
 * Existential slots are consequent-only metavars (from ∃-quantified positions).
 *
 * For each unbound existential slot:
 * 1. If it has associated persistent goals, try FFI resolution
 * 2. If FFI fails or no goals, bind to freshEvar
 */
function resolveExistentials(theta, slots, rule, state, calc) {
  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return;

  for (const slot of rule.existentialSlots) {
    if (theta[slot] !== undefined) continue; // already bound

    const goals = rule.existentialGoals[slot];
    if (goals && goals.length > 0) {
      let resolved = false;
      for (const pattern of goals) {
        // Substitute known bindings into the goal pattern
        const goal = subApplyIdx(pattern, theta, slots);

        // Try FFI direct
        const ffiResult = tryFFIDirect(goal);
        if (ffiResult && ffiResult.success) {
          // Extract output bindings from FFI result
          const ft = ffiResult.theta;
          if (ft) {
            for (let fi = 0; fi < ft.length; fi++) {
              const s = slots[ft[fi][0]];
              if (s !== undefined && theta[s] === undefined) theta[s] = ft[fi][1];
            }
          }
          if (theta[slot] !== undefined) { resolved = true; break; }
        }
        if (ffiResult && !ffiResult.success) {
          // Definitive FFI failure — bind to fresh evar
          theta[slot] = freshEvar();
          resolved = true;
          break;
        }
      }
      if (resolved) continue;
    }

    // No goal or all failed — bind to fresh evar
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
}

// ─── Pattern Matching ───────────────────────────────────────────────

// Reusable work buffers (avoids allocation per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);
const _deltaWritten = new Array(8);

/**
 * Try to match a rule against state.
 *
 * Worklist algorithm:
 * 1. Match linear patterns against state facts (with delta bypass, secondary index, general matching)
 * 2. Prove persistent patterns (FFI direct → backward chaining fallback)
 * 3. Deferred patterns wait for persistent outputs, then retry
 *
 * Returns { rule, theta, slots, consumed, optimized } or null.
 */
function tryMatch(rule, state, calc, matchOpts) {
  const _tmStart = TRACE_MATCHES ? _tmMatchCalls : 0;
  const consumed = {};
  const reserved = {};
  const index = state.index || buildStateIndex(state.linear);

  // Theta: indexed array, slots[metavarHash] → slot index
  const topUndo = undoSave();
  const { linearMeta, metavarSlots: slots, metavarCount } = rule;
  const theta = new Array(metavarCount);

  // Preserved patterns: reserve but don't consume
  const preservedCount = {};
  const usePreserved = matchOpts && matchOpts.optimizePreserved && rule.analysis;
  if (usePreserved) {
    for (const h of rule.analysis.preserved) {
      preservedCount[h] = (preservedCount[h] || 0) + 1;
    }
  }

  const persistentList = rule.antecedent.persistent || [];
  const linearPats = rule.antecedent.linear || [];
  const patternRoles = rule.patternRoles;
  let rpLen = linearPats.length;
  for (let i = 0; i < rpLen; i++) {
    _workPatterns[i] = linearPats[i];
    _workPositions[i] = i;
  }

  let persistentIdx = 0;
  let iterations = 0;
  const maxIterations = rpLen + persistentList.length + 10;

  while (rpLen > 0 || persistentIdx < persistentList.length) {
    if (++iterations > maxIterations) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      undoRestore(theta, topUndo);
      return null;
    }

    let madeProgress = false;

    // Phase 1: Match linear patterns
    let deferredLen = 0;
    for (let pi = 0; pi < rpLen; pi++) {
      const pattern = _workPatterns[pi];
      const origPos = _workPositions[pi];
      const meta = linearMeta[pattern];

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

      const pred = meta.pred;
      const isPreserved = usePreserved && preservedCount[pattern] > 0;

      // Strategy A: Delta bypass — direct child extraction for flat delta patterns
      const role = patternRoles[origPos];
      if (role && role.type === 'delta' && role.flat && !isPreserved) {
        const bindings = role.bindings;
        const gc = role.groundChecks;
        const candidates = index[pred] || [];
        let found = false;
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
            found = true;
            madeProgress = true;
            break;
          }

          for (let wi = 0; wi < writtenCount; wi++) theta[_deltaWritten[wi]] = undefined;
        }
        if (found) continue;
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
              madeProgress = true;
              continue;
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

      let found = false;
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
          found = true;
          madeProgress = true;
          break;
        }
        undoRestore(theta, savedUndo);
      }

      if (!found) {
        if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
        undoRestore(theta, topUndo);
        return null;
      }
    }

    rpLen = deferredLen;

    // Phase 2: Prove persistent patterns (FFI → state lookup → backward chaining)
    {
      const newIdx = provePersistentGoals(persistentList, persistentIdx, theta, slots, state, calc);
      if (newIdx > persistentIdx) madeProgress = true;
      persistentIdx = newIdx;
    }

    if (!madeProgress && (rpLen > 0 || persistentIdx < persistentList.length)) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      undoRestore(theta, topUndo);
      return null;
    }
  }

  if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: true });
  undoDiscard(topUndo);
  return { rule, theta, slots, consumed, optimized: !!usePreserved };
}

// ─── Match Selection ────────────────────────────────────────────────

const _findMatchState = { linear: null, persistent: null, index: null };

/** Find first matching rule (committed choice) */
function findMatch(state, rules, calc, matchOpts) {
  const stateIndex = buildStateIndex(state.linear, rules.fpConfig || null);
  _findMatchState.linear = state.linear;
  _findMatchState.persistent = state.persistent;
  _findMatchState.index = stateIndex;

  const ruleList = rules.rules || rules;
  const opcodeIndex = rules.opcodeIndex || null;

  // Strategy 1: EVM O(1) lookup
  if (opcodeIndex) {
    const heuristicRule = evmStrategy(stateIndex, opcodeIndex);
    if (heuristicRule) {
      const m = tryMatch(heuristicRule, _findMatchState, calc, matchOpts);
      if (m) return m;
    }
  }

  // Strategy 2: Predicate filtering + try all
  for (const rule of ruleList) {
    const triggers = rule.triggerPreds;
    if (triggers && triggers.length > 0) {
      let allPresent = true;
      for (let i = 0; i < triggers.length; i++) {
        const arr = stateIndex[triggers[i]];
        if (!arr || arr.length === 0) { allPresent = false; break; }
      }
      if (!allPresent) continue;
    }
    const m = tryMatch(rule, _findMatchState, calc, matchOpts);
    if (m) return m;
  }
  return null;
}

// ─── Apply Match ────────────────────────────────────────────────────

/** Apply match result: consume resources, produce new ones */
function applyMatch(state, { rule, theta, slots, consumed, optimized }) {
  const newLinear = { ...state.linear };
  for (const hStr in consumed) {
    const hash = Number(hStr);
    newLinear[hash] -= consumed[hStr];
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  let skipCount = null;
  if (optimized && rule.analysis) {
    skipCount = {};
    for (const h of rule.analysis.preserved) {
      skipCount[h] = (skipCount[h] || 0) + 1;
    }
  }
  const skipUsed = {};

  const cLinear = rule.compiledConseqLinear;
  const linPats = rule.consequent.linear || [];
  for (let i = 0; i < linPats.length; i++) {
    const pattern = linPats[i];
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    const recipe = cLinear && cLinear[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(pattern, theta, slots);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  const cPersistent = rule.compiledConseqPersistent;
  const persPats = rule.consequent.persistent || [];
  for (let i = 0; i < persPats.length; i++) {
    const recipe = cPersistent && cPersistent[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(persPats[i], theta, slots);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

// ─── Unified Loli Matching ──────────────────────────────────────────

/**
 * Try to fire a loli(trigger, {body}) from state using the shared
 * persistent proving pipeline. Handles all trigger forms:
 *   - Linear trigger: match against state.linear
 *   - Persistent trigger (!P): prove via FFI/state/backward
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

  // Expand choices in body (handles plus/with in loli body)
  const produced = flattenTensor(instantiated);
  const consequentAlts = expandConsequentChoices(produced);
  const name = 'loli:' + (getPredicateHead(trigger) || 'trigger');

  return {
    rule: {
      name,
      consequent: produced,
      consequentAlts,
      analysis: null,
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
function matchFirstLoli(state, calc) {
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tag(h) !== 'loli') continue;
    const m = matchLoli(h, state, calc);
    if (m) return m;
  }
  return null;
}

// ─── Main Loop ──────────────────────────────────────────────────────

/** Run forward chaining until quiescence */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  const useEvmStrategy = opts.useEvmStrategy !== false;
  const optimizePreserved = opts.optimizePreserved !== false;
  let steps = 0;

  const ruleIndex = buildRuleIndex(rules);
  const opcodeIndex = useEvmStrategy ? buildOpcodeIndex(rules) : null;
  const fpConfig = detectFingerprintConfig(rules);
  const indexedRules = { rules, ruleIndex, opcodeIndex, fpConfig };
  const matchOpts = optimizePreserved ? { optimizePreserved: true } : undefined;

  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  while (steps < maxSteps) {
    let m = findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      // Try to fire a loli continuation from state
      m = matchFirstLoli(state, calc);
      if (!m) return { state, quiescent: true, steps, trace };
    }
    if (trace) trace.push(`[${steps}] ${m.rule.name}`);
    if (m.rule.existentialSlots && m.rule.existentialSlots.length > 0) {
      resolveExistentials(m.theta, m.slots, m.rule, state, calc);
    }
    state = applyMatch(state, m);
    steps++;
  }

  return { state, quiescent: false, steps, trace };
}

function createState(linear = {}, persistent = {}) {
  return { linear, persistent };
}

module.exports = {
  // Compilation (re-exported from compile.js)
  compileRule,
  flattenTensor,
  unwrapMonad,
  expandItem,
  expandConsequentChoices,
  // Indexing
  buildRuleIndex,
  buildStateIndex,
  buildOpcodeIndex,
  evmStrategy,
  detectFingerprintConfig,
  // Matching
  tryMatch,
  findMatch,
  // Loli continuations (unified matching)
  matchLoli,
  matchFirstLoli,
  provePersistentGoals,
  // Existential resolution
  resolveExistentials,
  // Execution
  applyMatch,
  run,
  createState,
  // Shared utility (from ast.js)
  getPredicateHead,
  // Profiling
  getProfile,
  resetProfile,
  getTryMatchLog,
  resetTryMatchLog
};
