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
const { compileRule, flattenTensor, unwrapMonad, expandItem, expandConsequentChoices } = require('./compile');

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
    if (modes[i] === '+' && !ffi.convert.isGround(c)) return null;
    _ffiArgs[i] = c;
  }

  return fn(_ffiArgs);
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

    // Phase 2: Prove persistent patterns (FFI → backward chaining)
    while (persistentIdx < persistentList.length) {
      const goal = subApplyIdx(persistentList[persistentIdx], theta, slots);

      // Try FFI directly
      const ffiResult = tryFFIDirect(goal);
      if (ffiResult) {
        if (ffiResult.success) {
          const ft = ffiResult.theta;
          for (let fi = 0; fi < ft.length; fi++) {
            const slot = slots[ft[fi][0]];
            if (slot !== undefined) theta[slot] = ft[fi][1];
          }
          persistentIdx++;
          madeProgress = true;
          continue;
        }
        break; // FFI says false — definitive failure
      }

      // Fallback: backward proving
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
          persistentIdx++;
          madeProgress = true;
          continue;
        }
      }
      break;
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
    const m = findMatch(state, indexedRules, calc, matchOpts);
    if (!m) return { state, quiescent: true, steps, trace };
    if (trace) trace.push(`[${steps}] ${m.rule.name}`);
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
