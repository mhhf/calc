/**
 * Forward Chaining Engine
 *
 * Multiset rewriting with committed choice (no backtracking).
 * Runs until quiescence (no rules can fire).
 *
 * State: { linear: { hash: count }, persistent: { hash: true } }
 * Rules: precompiled from MDE with { antecedent, consequent }
 */

const Store = require('../../kernel/store');
const { NON_PRED_TAGS } = require('../../kernel/ast');
const { match: _match } = require('../../kernel/unify');
const { apply: _subApply } = require('../../kernel/substitute');
const ffi = require('../../engine/ffi');

// Profiling (enabled via CALC_PROFILE env var)
const PROFILE = process.env.CALC_PROFILE === '1';
const TRACE_MATCHES = process.env.CALC_TRACE_MATCHES === '1';
const profile = {
  matchTime: 0, matchCalls: 0,
  subTime: 0, subCalls: 0,
  proveTime: 0, proveCalls: 0,
};
// Per-tryMatch instrumentation (enabled via CALC_TRACE_MATCHES=1)
let _tmMatchCalls = 0;
const _tmLog = [];  // { rule, matchCalls, success }
function getTryMatchLog() { return _tmLog; }
function resetTryMatchLog() { _tmLog.length = 0; }

function match(pattern, hash, theta) {
  if (TRACE_MATCHES) _tmMatchCalls++;
  if (!PROFILE) return _match(pattern, hash, theta);
  const t0 = performance.now();
  const result = _match(pattern, hash, theta);
  profile.matchTime += performance.now() - t0;
  profile.matchCalls++;
  return result;
}

function subApply(hash, theta) {
  if (!PROFILE) return _subApply(hash, theta);
  const t0 = performance.now();
  const result = _subApply(hash, theta);
  profile.subTime += performance.now() - t0;
  profile.subCalls++;
  return result;
}

function getProfile() { return profile; }
function resetProfile() {
  profile.matchTime = profile.matchCalls = 0;
  profile.subTime = profile.subCalls = 0;
  profile.proveTime = profile.proveCalls = 0;
}

/**
 * Get the predicate head of a formula for indexing. O(1).
 * Flat: {tag: 'code', children: [PC, OP]} → 'code'
 * Atom: {tag: 'atom', children: ['x']} → 'x'
 *
 * @param {number} h - Hash of formula
 * @returns {string|null}
 */
function getPredicateHead(h) {
  const t = Store.tag(h);
  if (!t) return null;
  if (!NON_PRED_TAGS.has(t)) return t;
  if (t === 'atom') return Store.child(h, 0);
  return null;
}

/**
 * Build index from state linear facts
 * Groups facts by their predicate head for O(1) lookup
 *
 * Also builds secondary index for 'code' facts by PC value:
 *   codeByPC[pcValueHash] = codeFactHash
 * This enables O(1) lookup when matching 'code PC OPCODE' patterns.
 *
 * @param {{ [hash: number]: number }} linear
 * @returns {{ byPred: { [predicate: string]: number[] }, codeByPC: { [pcHash: number]: number } }}
 */
function buildStateIndex(linear) {
  const byPred = {};
  const codeByPC = {};

  for (const hStr of Object.keys(linear)) {
    const h = Number(hStr);
    const pred = getPredicateHead(h);
    if (pred) {
      if (!byPred[pred]) byPred[pred] = [];
      byPred[pred].push(h);

      // For code facts, also index by PC value
      // Flat: {tag: 'code', children: [PC, OPCODE]}
      if (pred === 'code') {
        if (Store.arity(h) >= 2) {
          codeByPC[Store.child(h, 0)] = h;
        }
      }
    } else {
      // Fallback: add to special '*' bucket for unindexable facts
      if (!byPred['*']) byPred['*'] = [];
      byPred['*'].push(h);
    }
  }

  // Return object with both indices, but also spread byPred for backward compatibility
  const index = { ...byPred, codeByPC };
  return index;
}

/**
 * Flatten tensor spine into list of formulas
 * Extracts: linear resources and !-wrapped persistent facts
 *
 * Linear: must be consumed exactly once
 * Persistent: can be used any number of times (marked with !)
 *
 * @param {number} h - Hash of tensor expression
 * @returns {{ linear: number[], persistent: number[] }}
 */
function flattenTensor(h) {
  const linear = [];
  const persistent = [];

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;

    if (t === 'tensor') {
      walk(Store.child(hash, 0));
      walk(Store.child(hash, 1));
    } else if (t === 'bang') {
      persistent.push(Store.child(hash, 0));
    } else {
      linear.push(hash);
    }
  }

  walk(h);
  return { linear, persistent };
}

/**
 * Extract monad body (unwrap {A} -> A)
 * @param {number} h
 * @returns {number}
 */
function unwrapMonad(h) {
  if (Store.tag(h) === 'monad') return Store.child(h, 0);
  return h;
}

/**
 * Extract the second argument from a flat predicate. O(1).
 * {tag: 'code', children: [PC, OPCODE]} → OPCODE
 *
 * @param {number} h - Pattern hash
 * @returns {number|null} - Second argument hash or null
 */
function extractSecondArg(h) {
  const t = Store.tag(h);
  if (!t || NON_PRED_TAGS.has(t)) return null;
  return Store.arity(h) >= 2 ? Store.child(h, 1) : null;
}

/**
 * Check if a hash is a ground term (no freevars)
 * Ground terms can be used as keys in opcode index
 *
 * @param {number} h - Hash to check
 * @returns {boolean}
 */
function isGround(h) {
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'freevar') return false;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && !isGround(c)) return false;
  }
  return true;
}

/**
 * Compile forward rule for efficient matching
 *
 * Input: hash of `A * B * !C -o { D * E }`
 * Output: { antecedent: { linear: [...], persistent: [...] },
 *           consequent: { linear: [...], persistent: [...] },
 *           triggerPreds: string[],
 *           opcodeHash: number|null }
 *
 * @param {{ hash: number, antecedent: number, consequent: number }} rule
 * @returns {Object} Compiled rule
 */
function compileRule(rule) {
  const anteFlat = flattenTensor(rule.antecedent);
  const conseqBody = unwrapMonad(rule.consequent);
  const conseqFlat = flattenTensor(conseqBody);

  // Extract trigger predicates from linear antecedents for rule indexing
  const triggerPreds = [];
  let opcodeHash = null;

  for (const h of (anteFlat.linear || [])) {
    const pred = getPredicateHead(h);
    if (pred && !triggerPreds.includes(pred)) {
      triggerPreds.push(pred);
    }
    if (pred === 'code' && !opcodeHash) {
      const arg2 = extractSecondArg(h);
      if (arg2 && isGround(arg2)) {
        opcodeHash = arg2;
      }
    }
  }

  // Precompute persistent output vars (freevars in last arg of persistent patterns)
  const persistentOutputVars = new Set();
  for (const p of (anteFlat.persistent || [])) {
    for (const v of collectOutputVars(p)) {
      persistentOutputVars.add(v);
    }
  }

  // Precompute per-linear-pattern metadata (eliminates Store.get walks in tryMatch)
  const linearMeta = new Map();
  for (const p of (anteFlat.linear || [])) {
    if (linearMeta.has(p)) continue;
    const pred = getPredicateHead(p);
    const freevars = collectFreevars(p);
    const persistentDeps = new Set();
    for (const v of freevars) {
      if (persistentOutputVars.has(v)) persistentDeps.add(v);
    }
    // For code patterns: extract PC sub-pattern for codeByPC O(1) lookup
    let pcSubPattern = null;
    if (pred === 'code') {
      if (Store.arity(p) >= 2) {
        pcSubPattern = Store.child(p, 0);
      }
    }
    linearMeta.set(p, { pred, freevars, persistentDeps, pcSubPattern });
  }

  return {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: conseqFlat,
    triggerPreds,
    opcodeHash,
    persistentOutputVars,
    linearMeta
  };
}

/**
 * Build rule index by trigger predicates
 * Groups rules by predicates they care about for O(1) lookup
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ [predicate: string]: Object[] }}
 */
function buildRuleIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.triggerPreds && rule.triggerPreds.length > 0) {
      for (const pred of rule.triggerPreds) {
        if (!index[pred]) index[pred] = [];
        index[pred].push(rule);
      }
    } else {
      // Rules with no indexable predicates go to '*' bucket
      if (!index['*']) index['*'] = [];
      index['*'].push(rule);
    }
  }
  return index;
}

/**
 * Build opcode index for EVM-style rule selection
 * Maps opcode binary hash directly to rule for O(1) lookup
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ [opcodeHash: number]: Object }}
 */
function buildOpcodeIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.opcodeHash) {
      index[rule.opcodeHash] = rule;
    }
  }
  return index;
}

/**
 * EVM strategy: Use PC→code→opcode for O(1) rule selection
 *
 * For EVM execution, the PC uniquely determines which rule fires:
 * 1. PC points to address X
 * 2. code X OPCODE tells us the opcode
 * 3. Opcode maps directly to rule
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object} stateIndex - State facts indexed by predicate
 * @param {Object} opcodeIndex - opcodeHash → rule mapping
 * @returns {Object|null} - The matching rule, or null if strategy doesn't apply
 */
function evmStrategy(state, stateIndex, opcodeIndex) {
  // 1. Get PC fact (must be exactly one)
  const pcFacts = stateIndex['pc'];
  if (!pcFacts || pcFacts.length !== 1) return null;

  // 2. Extract PC value: {tag: 'pc', children: [VALUE]}
  const pcHash = pcFacts[0];
  if (Store.arity(pcHash) < 1) return null;
  const pcValue = Store.child(pcHash, 0);

  // 3. Find code fact at this PC: code PC OPCODE
  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;

  for (const codeHash of codeFacts) {
    if (Store.arity(codeHash) < 2) continue;

    const codePC = Store.child(codeHash, 0);
    const opcodeHash = Store.child(codeHash, 1);

    if (codePC !== pcValue) continue;

    // 4. Look up rule by opcode
    const rule = opcodeIndex[opcodeHash];
    if (rule) return rule;
  }

  return null;
}

/**
 * Collect all freevars in a pattern
 * @param {number} h - Pattern hash
 * @returns {Set<number>}
 */
function collectFreevars(h) {
  const vars = new Set();

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === 'freevar') {
      vars.add(hash);
      return;
    }
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (typeof c === 'number') walk(c);
    }
  }

  walk(h);
  return vars;
}

/**
 * Collect OUTPUT freevars from a persistent pattern
 *
 * Convention: For patterns like inc(PC, PC') or plus(A, B, C),
 * the LAST argument is the output (result), others are inputs.
 *
 * @param {number} h - Persistent pattern hash
 * @returns {Set<number>}
 */
function collectOutputVars(h) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;

  const a = Store.arity(h);
  if (NON_PRED_TAGS.has(t) || a === 0) return vars;
  for (const v of collectFreevars(Store.child(h, a - 1))) {
    vars.add(v);
  }
  return vars;
}

// FFI metadata cache (avoid repeated object lookups)
const _ffiMeta = ffi.defaultMeta;

/**
 * Try FFI directly for a goal, bypassing the full prove() machinery.
 * Returns FFI result or null if no FFI is available.
 *
 * @param {number} goal - Goal term hash (already substituted)
 * @returns {{ success: boolean, theta?: Array }|null}
 */
function tryFFIDirect(goal) {
  const goalTag = Store.tag(goal);
  if (!goalTag) return null;

  let head;
  if (!NON_PRED_TAGS.has(goalTag)) head = goalTag;
  else if (goalTag === 'atom') head = Store.child(goal, 0);
  else return null;

  const meta = _ffiMeta[head];
  if (!meta) return null;

  const goalChildren = Store.children(goal);
  if (!ffi.mode.checkMode(goalChildren, meta.mode)) return null;

  const fn = ffi.get(meta.ffi);
  if (!fn) return null;

  return fn(goalChildren);
}

/**
 * Check if a pattern depends on variables that will be output by persistent patterns
 * @param {number} h - Pattern hash
 * @param {Set<number>} persistentOutputVars - Variables that persistent patterns will bind
 * @param {Array} theta - Current substitution
 * @returns {boolean}
 */
function dependsOnPersistentOutput(h, persistentOutputVars, theta) {
  const boundVars = new Set(theta.map(([v]) => v));
  const patternVars = collectFreevars(h);

  for (const v of patternVars) {
    // If this var is a persistent output var AND not yet bound, defer
    if (persistentOutputVars.has(v) && !boundVars.has(v)) {
      return true;
    }
  }
  return false;
}

/**
 * Try to match a rule against state with interleaved matching
 *
 * Uses worklist algorithm: try to match patterns, defer those that depend on
 * persistent output variables, use persistent proving to bind those vars, repeat.
 *
 * @param {Object} rule - Compiled rule
 * @param {Object} state - { linear, persistent, index }
 * @param {Object} calc - { clauses, types } for backward proving
 * @returns {{ rule, theta, consumed } | null}
 */
function tryMatch(rule, state, calc) {
  const _tmStart = TRACE_MATCHES ? _tmMatchCalls : 0;
  let theta = [];
  const consumed = {};

  // Build index if not already present
  const index = state.index || buildStateIndex(state.linear);

  // Use precomputed metadata from compileRule (zero Store.get walks for pattern analysis)
  const { persistentOutputVars, linearMeta } = rule;

  const persistentList = rule.antecedent.persistent || [];

  // All resources in antecedent are linear (consumed when matched)
  let resourcePatterns = [...(rule.antecedent.linear || [])];

  let persistentIdx = 0;
  let iterations = 0;
  const maxIterations = resourcePatterns.length + persistentList.length + 10;

  while (resourcePatterns.length > 0 || persistentIdx < persistentList.length) {
    iterations++;
    if (iterations > maxIterations) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      return null;
    }

    let madeProgress = false;

    // Try to match resource patterns
    const deferred = [];
    for (const pattern of resourcePatterns) {
      const meta = linearMeta.get(pattern);

      // Defer if pattern depends on persistent output vars not yet bound
      if (meta.persistentDeps.size > 0) {
        let hasUnbound = false;
        for (const v of meta.persistentDeps) {
          if (!theta.some(([bv]) => bv === v)) { hasUnbound = true; break; }
        }
        if (hasUnbound) {
          deferred.push(pattern);
          continue;
        }
      }

      const pred = meta.pred;

      // Special case: 'code PC OPCODE' pattern with codeByPC index
      if (pred === 'code' && index.codeByPC && meta.pcSubPattern !== null) {
        const pcValue = subApply(meta.pcSubPattern, theta);
        const codeFact = index.codeByPC[pcValue];
        if (codeFact) {
          const count = state.linear[codeFact] || 0;
          const available = count - (consumed[codeFact] || 0);
          if (available > 0) {
            const newTheta = match(pattern, codeFact, [...theta]);
            if (newTheta !== null) {
              consumed[codeFact] = (consumed[codeFact] || 0) + 1;
              theta = newTheta;
              madeProgress = true;
              continue;
            }
          }
        }
      }

      // Get candidate facts from index
      let candidates;
      if (pred) {
        // Known predicate: only facts with matching head can unify
        candidates = index[pred] || [];
      } else {
        // Unindexable pattern (variable/connective): must check all facts
        candidates = index['*'] || Object.keys(state.linear).map(Number);
      }

      // Try to match against indexed candidates
      let found = false;
      for (const h of candidates) {
        const count = state.linear[h] || 0;
        const available = count - (consumed[h] || 0);
        if (available <= 0) continue;

        const newTheta = match(pattern, h, [...theta]);
        if (newTheta !== null) {
          consumed[h] = (consumed[h] || 0) + 1;
          theta = newTheta;
          found = true;
          madeProgress = true;
          break;
        }
      }

      if (!found) {
        if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
        return null;
      }
    }

    resourcePatterns = deferred;

    // Try persistent patterns
    while (persistentIdx < persistentList.length) {
      const pPattern = persistentList[persistentIdx];
      const goal = subApply(pPattern, theta);

      // Try FFI directly (bypasses full prove() machinery)
      const ffiResult = tryFFIDirect(goal);
      if (ffiResult) {
        if (ffiResult.success) {
          theta = [...theta, ...ffiResult.theta];
          persistentIdx++;
          madeProgress = true;
          continue;
        }
        // FFI available but returned false (e.g. neq(5,5)) — definitive failure
        break;
      }

      // Fallback to full backward proving (no FFI for this predicate)
      if (calc && calc.clauses && calc.types) {
        const backward = require('../../engine/prove');
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
          theta = [...theta, ...result.theta];
          persistentIdx++;
          madeProgress = true;
          continue;
        }
      }

      break;
    }

    if (!madeProgress && (resourcePatterns.length > 0 || persistentIdx < persistentList.length)) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      return null;
    }
  }

  if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: true });
  return { rule, theta, consumed };
}

/**
 * Find first matching rule (committed choice)
 *
 * Uses multiple optimization strategies:
 * 1. EVM strategy (optional): PC→code→opcode for O(1) rule selection
 * 2. State index: facts grouped by predicate for fast pattern matching
 * 3. Strict filtering: only try rules where ALL trigger predicates exist in state
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object[]} rules - Compiled rules (or { rules, ruleIndex, opcodeIndex } for cached)
 * @param {Object} calc - { clauses, types } for backward proving
 * @returns {{ rule, theta, consumed } | null}
 */
function findMatch(state, rules, calc) {
  // Build state index once
  const stateIndex = buildStateIndex(state.linear);
  const indexedState = { ...state, index: stateIndex };

  // Get rule list and optional opcode index
  const ruleList = rules.rules || rules;
  const opcodeIndex = rules.opcodeIndex || null;

  // Strategy 1: EVM opcode-based O(1) lookup
  // If we have an opcode index and PC+code facts, try exact rule first
  if (opcodeIndex && Object.keys(opcodeIndex).length > 0) {
    const heuristicRule = evmStrategy(state, stateIndex, opcodeIndex);
    if (heuristicRule) {
      const m = tryMatch(heuristicRule, indexedState, calc);
      if (m) return m;
      // Strategy suggested a rule but it didn't match - fall through to general
    }
  }

  // Strategy 2: Strict predicate filtering
  // Get predicates present in state (with non-empty fact lists)
  const statePredicateSet = new Set(
    Object.entries(stateIndex)
      .filter(([, hashes]) => hashes.length > 0)
      .map(([pred]) => pred)
  );

  // Only try rules where ALL trigger predicates exist in state
  const orderedCandidates = ruleList.filter(rule => {
    const triggers = rule.triggerPreds || [];
    if (triggers.length === 0) return true;
    return triggers.every(pred => statePredicateSet.has(pred));
  });

  for (const rule of orderedCandidates) {
    const m = tryMatch(rule, indexedState, calc);
    if (m) return m;
  }
  return null;
}

/**
 * Apply match: consume resources, produce new ones
 *
 * @param {Object} state - { linear, persistent }
 * @param {{ rule, theta, consumed }} m - Match result
 * @returns {Object} New state
 */
function applyMatch(state, { rule, theta, consumed }) {
  // Remove consumed linear resources
  const newLinear = { ...state.linear };
  for (const [h, count] of Object.entries(consumed)) {
    const hash = Number(h);
    newLinear[hash] -= count;
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  // Add produced linear resources (apply substitution)
  for (const pattern of (rule.consequent.linear || [])) {
    const h = subApply(pattern, theta);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  for (const pattern of (rule.consequent.persistent || [])) {
    const h = subApply(pattern, theta);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

/**
 * Run forward chaining until quiescence
 *
 * @param {Object} state - { linear: { hash: count }, persistent: { hash: true } }
 * @param {Object[]} rules - Compiled rules
 * @param {Object} opts - { maxSteps, trace, calc, useEvmStrategy }
 * @returns {{ state, quiescent: boolean, steps: number, trace?: string[] }}
 */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  const useEvmStrategy = opts.useEvmStrategy !== false; // enabled by default
  let steps = 0;

  // Build indices once for all steps
  const ruleIndex = buildRuleIndex(rules);
  const opcodeIndex = useEvmStrategy ? buildOpcodeIndex(rules) : null;
  const indexedRules = { rules, ruleIndex, opcodeIndex };

  // Build backward prover index once (2x speedup)
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('../../engine/prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  while (steps < maxSteps) {
    const m = findMatch(state, indexedRules, calc);
    if (!m) {
      return { state, quiescent: true, steps, trace };
    }

    if (trace) {
      trace.push(`[${steps}] ${m.rule.name}`);
    }

    state = applyMatch(state, m);
    steps++;
  }

  return { state, quiescent: false, steps, trace };
}

/**
 * Create initial state from multisets
 *
 * @param {{ [hash: number]: number }} linear
 * @param {{ [hash: number]: boolean }} persistent
 */
function createState(linear = {}, persistent = {}) {
  return { linear, persistent };
}

module.exports = {
  compileRule,
  flattenTensor,
  unwrapMonad,
  buildRuleIndex,
  buildStateIndex,
  buildOpcodeIndex,
  evmStrategy,
  tryMatch,
  findMatch,
  applyMatch,
  run,
  createState,
  getPredicateHead,
  // Profiling (enable with CALC_PROFILE=1)
  getProfile,
  resetProfile,
  // Per-tryMatch tracing (enable with CALC_TRACE_MATCHES=1)
  getTryMatchLog,
  resetTryMatchLog
};
