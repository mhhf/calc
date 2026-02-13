/**
 * Execution Tree Exploration
 *
 * Explores all forward chaining executions up to a depth bound.
 * Returns a tree of all reachable states.
 *
 * Tree structure:
 *   { type: 'leaf', state }           - quiescent (no rules fire)
 *   { type: 'branch', state, children } - nondeterministic choice
 *   { type: 'bound', state }          - depth limit reached
 *
 * Limitation: Enumerates rule-level nondeterminism only.
 * Multiple ways to match the same rule (different resource selections)
 * are not enumerated - only the first valid selection per rule.
 */

const {
  tryMatch,
  applyMatch,
  buildStateIndex,
  buildRuleIndex
} = require('./forward.js');

/**
 * Find all rules that can fire in current state
 * Returns array of matches (one per rule that can fire)
 */
function findAllMatches(state, rules, calc) {
  const stateIndex = buildStateIndex(state.linear);
  const indexedState = { ...state, index: stateIndex };
  const ruleList = rules.rules || rules;

  const matches = [];
  for (const rule of ruleList) {
    const m = tryMatch(rule, indexedState, calc);
    if (m) matches.push(m);
  }
  return matches;
}

/**
 * Explore all execution paths up to depth bound
 */
function explore(state, rules, opts = {}) {
  const maxDepth = opts.maxDepth ?? 100;
  const calc = opts.calc ?? null;

  // Pre-build rule index
  const indexedRules = rules.rules ? rules : { rules };

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('../../mde/prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  function go(state, depth) {
    if (depth >= maxDepth) {
      return { type: 'bound', state };
    }

    const matches = findAllMatches(state, indexedRules, calc);

    if (matches.length === 0) {
      return { type: 'leaf', state };
    }

    const children = matches.map(m => ({
      rule: m.rule.name,
      child: go(applyMatch(state, m), depth + 1)
    }));

    return { type: 'branch', state, children };
  }

  return go(state, 0);
}

// Tree utilities

function countLeaves(tree) {
  if (tree.type === 'leaf' || tree.type === 'bound') return 1;
  return tree.children.reduce((sum, c) => sum + countLeaves(c.child), 0);
}

function getAllLeaves(tree) {
  if (tree.type === 'leaf' || tree.type === 'bound') return [tree];
  return tree.children.flatMap(c => getAllLeaves(c.child));
}

function maxDepth(tree, d = 0) {
  if (tree.type === 'leaf' || tree.type === 'bound') return d;
  return Math.max(...tree.children.map(c => maxDepth(c.child, d + 1)));
}

function countNodes(tree) {
  if (tree.type === 'leaf' || tree.type === 'bound') return 1;
  return 1 + tree.children.reduce((sum, c) => sum + countNodes(c.child), 0);
}

module.exports = {
  explore,
  findAllMatches,
  countLeaves,
  getAllLeaves,
  maxDepth,
  countNodes
};
