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
 * Compile forward rule for efficient matching
 *
 * Input: hash of `A * B * !C -o { D * E }`
 * Output: { antecedent: { linear: [...], persistent: [...] },
 *           consequent: { linear: [...], persistent: [...] } }
 *
 * @param {{ hash: number, antecedent: number, consequent: number }} rule
 * @returns {Object} Compiled rule
 */
function compileRule(rule) {
  const anteFlat = flattenTensor(rule.antecedent);
  const conseqBody = unwrapMonad(rule.consequent);
  const conseqFlat = flattenTensor(conseqBody);

  return {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: conseqFlat
  };
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
 * @param {Object} state - { linear, persistent }
 * @param {Object} calc - { clauses, types } for backward proving
 * @returns {{ rule, theta, consumed } | null}
 */
function tryMatch(rule, state, calc) {
  let theta = [];
  const consumed = {};

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

      // Try to match against state
      let found = false;
      for (const [hStr, count] of Object.entries(state.linear)) {
        const h = Number(hStr);
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
        const result = backward.prove(goal, calc.clauses, calc.types, { maxDepth: 50 });
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
 * @param {Object} state - { linear, persistent }
 * @param {Object[]} rules - Compiled rules
 * @param {Object} calc - { clauses, types } for backward proving
 * @returns {{ rule, theta, consumed } | null}
 */
function findMatch(state, rules, calc) {
  for (const rule of rules) {
    const m = tryMatch(rule, state, calc);
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
 * @param {Object} opts - { maxSteps, trace, calc }
 * @returns {{ state, quiescent: boolean, steps: number, trace?: string[] }}
 */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  let steps = 0;

  while (steps < maxSteps) {
    const m = findMatch(state, rules, calc);
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
  findMatch,
  applyMatch,
  run,
  createState,
  // Profiling (enable with CALC_PROFILE=1)
  getProfile,
  resetProfile
};
