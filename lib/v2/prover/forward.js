/**
 * Forward Chaining Engine
 *
 * Multiset rewriting with committed choice (no backtracking).
 * Runs until quiescence (no rules can fire).
 *
 * State: { linear: { hash: count }, persistent: { hash: true } }
 * Rules: precompiled from MDE with { antecedent, consequent }
 */

const Store = require('../kernel/store');
const Context = require('./focused/context');
const { match: _match } = require('../kernel/unify');
const { apply: _subApply } = require('../kernel/substitute');

// Profiling (enabled via CALC_PROFILE env var)
const PROFILE = process.env.CALC_PROFILE === '1';
const profile = {
  matchTime: 0, matchCalls: 0,
  subTime: 0, subCalls: 0,
  proveTime: 0, proveCalls: 0,
};

function match(pattern, hash, theta) {
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
 * Get the predicate head of a formula for indexing
 * E.g., (app pc X) → "pc", (app (app code X) Y) → "code"
 * Returns null for non-indexable patterns (freevars, etc.)
 *
 * @param {number} h - Hash of formula
 * @returns {string|null}
 */
function getPredicateHead(h) {
  const node = Store.get(h);
  if (!node) return null;

  if (node.tag === 'app') {
    // Recurse into left child to find the head
    const leftHead = getPredicateHead(node.children[0]);
    if (leftHead) return leftHead;
    // If left is an atom, that's our head
    const left = Store.get(node.children[0]);
    if (left?.tag === 'atom') return left.children[0];
  } else if (node.tag === 'atom') {
    return node.children[0];
  }

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
      // code PC OPCODE is (app (app (atom code) PC) OPCODE)
      if (pred === 'code') {
        const node = Store.get(h);
        if (node && node.tag === 'app') {
          const left = Store.get(node.children[0]);
          if (left && left.tag === 'app') {
            const pcValue = left.children[1];
            codeByPC[pcValue] = h;
          }
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
    const node = Store.get(hash);
    if (!node) return;

    if (node.tag === 'tensor') {
      // In tensor(A, B), walk both children
      walk(node.children[0]);
      walk(node.children[1]);
    } else if (node.tag === 'bang') {
      // !X is persistent (unrestricted)
      persistent.push(node.children[0]);
    } else {
      // Leaf formula - linear resource
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
  const node = Store.get(h);
  if (node?.tag === 'monad') return node.children[0];
  return h;
}

/**
 * Extract the second argument from a pattern like (app (app (atom pred) ARG1) ARG2)
 * Used to get the opcode from code patterns: code PC OPCODE → returns OPCODE hash
 *
 * @param {number} h - Pattern hash
 * @returns {number|null} - Second argument hash or null
 */
function extractSecondArg(h) {
  const node = Store.get(h);
  if (!node || node.tag !== 'app') return null;
  // node is (app LEFT ARG2), where LEFT is (app (atom pred) ARG1)
  const left = Store.get(node.children[0]);
  if (!left || left.tag !== 'app') return null;
  // Return ARG2 (the second argument)
  return node.children[1];
}

/**
 * Check if a hash is a ground term (no freevars)
 * Ground terms can be used as keys in opcode index
 *
 * @param {number} h - Hash to check
 * @returns {boolean}
 */
function isGround(h) {
  const node = Store.get(h);
  if (!node) return true;
  if (node.tag === 'freevar') return false;
  for (const c of node.children) {
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
  // A rule can fire if ANY of its linear antecedents matches a state fact
  const triggerPreds = [];
  let opcodeHash = null;

  for (const h of (anteFlat.linear || [])) {
    const pred = getPredicateHead(h);
    if (pred && !triggerPreds.includes(pred)) {
      triggerPreds.push(pred);
    }
    // For EVM-style rules: extract opcode from 'code PC OPCODE' pattern
    // The opcode is ground (no freevars) and uniquely identifies the rule
    if (pred === 'code' && !opcodeHash) {
      const arg2 = extractSecondArg(h);
      if (arg2 && isGround(arg2)) {
        opcodeHash = arg2;
      }
    }
  }

  return {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: conseqFlat,
    triggerPreds,  // Predicates that can trigger this rule
    opcodeHash     // For EVM: the opcode binary hash (enables O(1) rule lookup)
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

  // 2. Extract PC value: pc is (app (atom pc) VALUE)
  const pcHash = pcFacts[0];
  const pcNode = Store.get(pcHash);
  if (!pcNode || pcNode.tag !== 'app') return null;
  const pcValue = pcNode.children[1];

  // 3. Find code fact at this PC: code PC OPCODE
  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;

  for (const codeHash of codeFacts) {
    const codeNode = Store.get(codeHash);
    if (!codeNode || codeNode.tag !== 'app') continue;

    // codeNode is (app (app (atom code) PC) OPCODE)
    const left = Store.get(codeNode.children[0]);
    if (!left || left.tag !== 'app') continue;

    // Check if this code fact's PC matches our PC value
    const codePC = left.children[1];
    if (codePC !== pcValue) continue;

    // Found it! Extract opcode
    const opcodeHash = codeNode.children[1];

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
    const node = Store.get(hash);
    if (!node) return;
    if (node.tag === 'freevar') {
      vars.add(hash);
      return;
    }
    for (const c of node.children) {
      if (typeof c === 'number') walk(c);
    }
  }

  walk(h);
  return vars;
}

/**
 * Collect OUTPUT freevars from a persistent pattern
 *
 * Convention: For patterns like (inc PC PC') or (plus A B C),
 * the LAST argument is the output (result), others are inputs.
 *
 * @param {number} h - Persistent pattern hash
 * @returns {Set<number>}
 */
function collectOutputVars(h) {
  const vars = new Set();

  // Find the rightmost app chain and get its last argument
  function getLastArg(hash) {
    const node = Store.get(hash);
    if (!node) return null;
    if (node.tag === 'app') {
      // In (app (app ... A) B), B is the rightmost argument
      const rightArg = node.children[1];
      return rightArg;
    }
    return null;
  }

  // Walk to find the last argument, which is the output
  const lastArg = getLastArg(h);
  if (lastArg !== null) {
    // Collect all freevars in the last argument
    for (const v of collectFreevars(lastArg)) {
      vars.add(v);
    }
  }

  return vars;
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
  let theta = [];
  const consumed = {};

  // Build index if not already present
  const index = state.index || buildStateIndex(state.linear);

  // Collect variables that will be output by persistent patterns
  // These are freevars in OUTPUT positions (typically the last argument)
  const persistentOutputVars = new Set();
  for (const p of (rule.antecedent.persistent || [])) {
    for (const v of collectOutputVars(p)) {
      persistentOutputVars.add(v);
    }
  }

  const persistentList = [...(rule.antecedent.persistent || [])];

  // All resources in antecedent are linear (consumed when matched)
  let resourcePatterns = [...(rule.antecedent.linear || [])];

  let persistentIdx = 0;
  let iterations = 0;
  const maxIterations = resourcePatterns.length + persistentList.length + 10;

  while (resourcePatterns.length > 0 || persistentIdx < persistentList.length) {
    iterations++;
    if (iterations > maxIterations) return null;

    let madeProgress = false;

    // Try to match resource patterns
    const deferred = [];
    for (const pattern of resourcePatterns) {
      // Defer if pattern depends on persistent output vars not yet bound
      if (dependsOnPersistentOutput(pattern, persistentOutputVars, theta)) {
        deferred.push(pattern);
        continue;
      }

      // Get predicate head for indexed lookup
      const pred = getPredicateHead(pattern);

      // Special case: 'code PC OPCODE' pattern with codeByPC index
      // If PC is already bound, we can do O(1) lookup instead of O(n) scan
      if (pred === 'code' && index.codeByPC) {
        // Pattern is (app (app (atom code) PC_PATTERN) OPCODE_PATTERN)
        const patternNode = Store.get(pattern);
        if (patternNode && patternNode.tag === 'app') {
          const leftPattern = Store.get(patternNode.children[0]);
          if (leftPattern && leftPattern.tag === 'app') {
            const pcPattern = leftPattern.children[1];
            // Apply substitution to get bound PC value
            const pcValue = subApply(pcPattern, theta);
            // Look up code fact at this PC
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
                  continue; // Move to next pattern
                }
              }
            }
            // Direct lookup failed, fall through to general matching
          }
        }
      }

      // Get candidate facts from index (or all facts if no index hit)
      let candidates;
      if (pred && index[pred]) {
        candidates = index[pred];
      } else if (index['*']) {
        // Fallback to unindexable bucket + specific predicate if exists
        candidates = [...(index['*'] || []), ...(pred && index[pred] ? index[pred] : [])];
      } else {
        // No index available, fall back to all facts
        candidates = Object.keys(state.linear).map(Number);
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
        // Pattern didn't match any resource - fail
        return null;
      }
    }

    resourcePatterns = deferred;

    // Try persistent patterns if we have bound vars they need
    while (persistentIdx < persistentList.length) {
      const pPattern = persistentList[persistentIdx];

      // Apply current substitution
      const goal = subApply(pPattern, theta);

      // Check if goal still has unbound input vars
      // For patterns like (inc PC PC'), PC should be bound but PC' will be output
      // We can try proving even with output vars unbound

      if (calc && calc.clauses && calc.types) {
        const backward = require('../../mde/prove');
        const t0 = PROFILE ? performance.now() : 0;
        // Use cached index if available (built once per run)
        const result = backward.prove(goal, calc.clauses, calc.types, {
          maxDepth: 50,
          index: calc.backwardIndex  // cached index from run()
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

      // Couldn't prove this pattern yet - maybe need more bindings
      break;
    }

    // If no progress was made and we still have patterns, we're stuck
    if (!madeProgress && (resourcePatterns.length > 0 || persistentIdx < persistentList.length)) {
      return null;
    }
  }

  return {
    rule,
    theta,
    consumed
  };
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
    const backward = require('../../mde/prove');
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
  // Profiling (enable with CALC_PROFILE=1)
  getProfile,
  resetProfile
};
