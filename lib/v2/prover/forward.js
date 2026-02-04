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
const { match } = require('../kernel/unify');
const { apply: subApply } = require('../kernel/substitute');

/**
 * Flatten tensor spine into list of formulas
 * Extracts: linear resources and !-wrapped persistent facts
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
      walk(node.children[0]);
      walk(node.children[1]);
    } else if (node.tag === 'bang') {
      persistent.push(node.children[0]);
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
 * Try to match a single antecedent pattern against state
 *
 * @param {number[]} patterns - Linear patterns to match
 * @param {{ [hash: number]: number }} state - Available resources
 * @param {Array} theta - Current substitution
 * @returns {{ consumed: Object, theta: Array } | null}
 */
function matchLinear(patterns, state, theta) {
  const consumed = {};

  for (const pattern of patterns) {
    let found = false;

    // Try each resource in state
    for (const h of Object.keys(state)) {
      const hash = Number(h);
      const available = (state[hash] || 0) - (consumed[hash] || 0);
      if (available <= 0) continue;

      // Try to unify pattern with resource
      const newTheta = match(pattern, hash, [...theta]);
      if (newTheta !== null) {
        consumed[hash] = (consumed[hash] || 0) + 1;
        theta = newTheta;
        found = true;
        break;
      }
    }

    if (!found) return null;
  }

  return { consumed, theta };
}

/**
 * Match persistent patterns via backward chaining
 *
 * For `!foo X` patterns, we use backward proof search to find X.
 * Falls back to state.persistent for simple ground patterns.
 *
 * @param {number[]} patterns - Persistent patterns to solve
 * @param {Object} calc - { clauses, types } for backward proving (optional)
 * @param {{ [hash: number]: boolean }} statePersistent - State persistent facts
 * @param {Array} theta - Current substitution
 * @returns {Array | null} Updated theta or null
 */
function matchPersistent(patterns, calc, statePersistent, theta) {
  for (const pattern of patterns) {
    // Apply current substitution to pattern
    const goal = subApply(pattern, theta);

    let found = false;

    // First try backward proving if calc is available
    if (calc && calc.clauses && calc.types) {
      const backward = require('../../mde/prove');
      const result = backward.prove(goal, calc.clauses, calc.types, { maxDepth: 50 });
      if (result.success) {
        theta = [...theta, ...result.theta];
        found = true;
      }
    }

    // Fall back to matching against state.persistent
    if (!found && statePersistent) {
      for (const h of Object.keys(statePersistent)) {
        const hash = Number(h);
        const newTheta = match(goal, hash, [...theta]);
        if (newTheta !== null) {
          theta = newTheta;
          found = true;
          break;
        }
      }
    }

    if (!found) return null;
  }

  return theta;
}

/**
 * Try to match a rule against state
 *
 * @param {Object} rule - Compiled rule
 * @param {Object} state - { linear, persistent }
 * @param {Object} calc - { clauses, types } for backward proving
 * @returns {{ rule, theta, consumed } | null}
 */
function tryMatch(rule, state, calc) {
  // Start with empty substitution
  let theta = [];

  // Match linear patterns first (they instantiate variables)
  const linearResult = matchLinear(rule.antecedent.linear, state.linear, theta);
  if (linearResult === null) return null;
  theta = linearResult.theta;

  // Then prove persistent patterns via backward chaining or state lookup
  theta = matchPersistent(rule.antecedent.persistent, calc, state.persistent, theta);
  if (theta === null) return null;

  return {
    rule,
    theta,
    consumed: linearResult.consumed
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

  // Add produced resources (apply substitution)
  for (const pattern of rule.consequent.linear) {
    const h = subApply(pattern, theta);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  for (const pattern of rule.consequent.persistent) {
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
  createState
};
