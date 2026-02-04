/**
 * Backward Chaining Prover for MDE Clauses
 *
 * Simple depth-first search with unification.
 * No focusing (MDE clauses don't have polarity).
 */

const Store = require('../v2/kernel/store');
const { unify } = require('../v2/kernel/unify');
const { apply: subApply } = require('../v2/kernel/substitute');

/**
 * Prove a goal using backward chaining
 *
 * @param {number} goal - Goal hash to prove
 * @param {Map} clauses - Map of name → { hash, premises }
 * @param {Map} types - Map of name → hash (axioms/facts)
 * @param {Object} opts - { maxDepth, trace }
 * @returns {{ success: boolean, theta?: Array, trace?: string[] }}
 */
function prove(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const trace = opts.trace ? [] : null;

  function search(g, theta, depth) {
    if (depth > maxDepth) return null;

    const indent = trace ? '  '.repeat(depth) : '';
    if (trace) trace.push(`${indent}Goal: ${formatTerm(g)}`);

    // Apply current substitution to goal
    const goalInst = subApply(g, theta);

    // Try to unify against types (axioms/facts)
    for (const [name, typeHash] of types) {
      // Freshen the type to avoid variable capture
      const freshType = freshenTerm(typeHash, depth, 'a');
      const newTheta = unify(freshType, goalInst);
      if (newTheta !== null) {
        // Merge with existing theta
        const merged = mergeTheta(theta, newTheta);
        if (merged !== null) {
          if (trace) trace.push(`${indent}  ✓ Matched axiom: ${name}`);
          return merged;
        }
      }
    }

    // Try to unify against clause heads
    for (const [name, clause] of clauses) {
      // Fresh copy of clause (rename variables)
      const { head, premises } = freshenClause(clause, depth);

      const newTheta = unify(head, goalInst);
      if (newTheta === null) continue;

      // Merge with existing theta
      const merged = mergeTheta(theta, newTheta);
      if (merged === null) continue;

      if (trace) trace.push(`${indent}  Trying clause: ${name}`);

      // Prove all premises
      let currentTheta = merged;
      let allPremisesProved = true;

      for (const premise of premises) {
        const premiseInst = subApply(premise, currentTheta);
        const result = search(premiseInst, currentTheta, depth + 1);

        if (result === null) {
          allPremisesProved = false;
          break;
        }
        currentTheta = result;
      }

      if (allPremisesProved) {
        if (trace) trace.push(`${indent}  ✓ Clause ${name} succeeded`);
        return currentTheta;
      }
    }

    if (trace) trace.push(`${indent}  ✗ No matching clause`);
    return null;
  }

  const result = search(goal, [], 0);

  return {
    success: result !== null,
    theta: result,
    trace
  };
}

/**
 * Merge two substitutions
 */
function mergeTheta(theta1, theta2) {
  // Simple merge - could check consistency
  return [...theta1, ...theta2];
}

/**
 * Freshen a single term
 */
function freshenTerm(h, depth, prefix = '') {
  const suffix = `_${prefix}d${depth}`;
  const renamed = new Map();

  function freshen(hash) {
    const node = Store.get(hash);
    if (!node) return hash;

    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(hash)) {
          renamed.set(hash, Store.intern('freevar', [name + suffix]));
        }
        return renamed.get(hash);
      }
      return hash;
    }

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const newC = freshen(c);
        if (newC !== c) changed = true;
        return newC;
      }
      return c;
    });

    if (!changed) return hash;
    return Store.intern(node.tag, newChildren);
  }

  return freshen(h);
}

/**
 * Freshen clause variables (add depth suffix to avoid capture)
 */
function freshenClause(clause, depth) {
  const suffix = `_d${depth}`;
  const renamed = new Map();

  function freshen(h) {
    const node = Store.get(h);
    if (!node) return h;

    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        // It's a metavar - rename it
        if (!renamed.has(h)) {
          renamed.set(h, Store.intern('freevar', [name + suffix]));
        }
        return renamed.get(h);
      }
      return h;
    }

    // Recurse on children
    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const newC = freshen(c);
        if (newC !== c) changed = true;
        return newC;
      }
      return c;
    });

    if (!changed) return h;
    return Store.intern(node.tag, newChildren);
  }

  return {
    head: freshen(clause.hash),
    premises: clause.premises.map(p => freshen(p))
  };
}

/**
 * Format term for display
 */
function formatTerm(h, depth = 0) {
  if (depth > 5) return '...';
  const node = Store.get(h);
  if (!node) return '?';

  if (node.tag === 'atom') return node.children[0];
  if (node.tag === 'freevar') return node.children[0];

  if (node.tag === 'app') {
    const [fn, arg] = node.children;
    return `${formatTerm(fn, depth + 1)} ${formatTermParen(arg, depth + 1)}`;
  }

  return node.tag;
}

function formatTermParen(h, depth) {
  const node = Store.get(h);
  if (!node) return '?';
  if (node.tag === 'atom' || node.tag === 'freevar') return formatTerm(h, depth);
  return `(${formatTerm(h, depth)})`;
}

/**
 * Extract solution from substitution
 * Returns map of original variable names to their values
 */
function extractSolution(theta, goal) {
  const solution = {};

  // Find all metavars in original goal
  function findVars(h, vars) {
    const node = Store.get(h);
    if (!node) return;
    if (node.tag === 'freevar' && node.children[0]?.startsWith('_')) {
      vars.add(h);
    }
    for (const c of node.children) {
      if (typeof c === 'number') findVars(c, vars);
    }
  }

  const goalVars = new Set();
  findVars(goal, goalVars);

  // Fully apply substitution (transitive closure)
  function fullyApply(h) {
    // Keep applying until fixed point
    let current = h;
    let changed = true;
    let iterations = 0;
    while (changed && iterations < 100) {
      changed = false;
      iterations++;
      current = subApply(current, theta);
      // Check if still has unresolved vars that might be in theta
      const node = Store.get(current);
      if (node?.tag === 'freevar') {
        for (const [v, val] of theta) {
          if (v === current) {
            current = val;
            changed = true;
            break;
          }
        }
      }
    }
    return current;
  }

  // Apply substitution and extract results
  for (const varHash of goalVars) {
    const varName = Store.get(varHash)?.children[0];
    if (!varName) continue;

    const value = fullyApply(varHash);

    // Format the value
    solution[varName.slice(1)] = formatTerm(value); // Remove leading _
  }

  return solution;
}

module.exports = { prove, extractSolution, formatTerm };
