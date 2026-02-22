/**
 * Backward Chaining Prover for MDE Clauses
 *
 * Depth-first search with unification and first-argument indexing.
 * Supports FFI (Foreign Function Interface) for computational predicates.
 */

const Store = require('../kernel/store');
const { isPredTag, getPredicateHead: getHead } = require('../kernel/ast');
const { unify } = require('../kernel/unify');
const { apply: subApply } = require('../kernel/substitute');
const ffi = require('./ffi');

/**
 * Get first argument's outermost constructor. O(1).
 * Flat: {tag: 'plus', children: [i(X), Y, Z]} → 'i'
 */
function getFirstArgCtor(hash) {
  const node = Store.get(hash);
  if (!node) return null;

  // Flat predicate: first arg is children[0]
  if (!isPredTag(node.tag) || node.children.length === 0) return null;
  const firstArg = node.children[0];

  // Classify the first argument
  const argNode = Store.get(firstArg);
  if (!argNode) return null;
  if (argNode.tag === 'atom') return argNode.children[0];
  if (argNode.tag === 'freevar') return '_';
  if (isPredTag(argNode.tag)) return argNode.tag;
  if (argNode.tag === 'binlit') {
    const v = argNode.children[0];
    if (v === 0n) return 'e';
    return v % 2n === 1n ? 'i' : 'o';
  }
  return null;
}

/**
 * Build two-level index: head → firstArgCtor → [items]
 * O(n * arity) where n = total items
 */
function buildIndex(clauses, types) {
  const idx = { types: {}, clauses: {} };

  for (const [name, hash] of types) {
    const head = getHead(hash);
    if (!head) continue;
    const fa = getFirstArgCtor(hash) || '_';
    (idx.types[head] ||= {})[fa] ||= [];
    idx.types[head][fa].push([name, hash]);
  }

  for (const [name, clause] of clauses) {
    const head = getHead(clause.hash);
    if (!head) continue;
    const fa = getFirstArgCtor(clause.hash) || '_';
    (idx.clauses[head] ||= {})[fa] ||= [];
    idx.clauses[head][fa].push([name, clause]);
  }

  return idx;
}

/**
 * Get candidate types and clauses for a goal. O(1).
 * Returns items from specific bucket + catch-all bucket.
 */
function getCandidates(idx, goalHash) {
  const head = getHead(goalHash);
  if (!head) return { types: [], clauses: [] };

  const fa = getFirstArgCtor(goalHash) || '_';
  const ti = idx.types[head] || {};
  const ci = idx.clauses[head] || {};

  return {
    types: [...(ti[fa] || []), ...(fa !== '_' ? ti['_'] || [] : [])],
    clauses: [...(ci[fa] || []), ...(fa !== '_' ? ci['_'] || [] : [])],
  };
}

// ============================================================================
// FFI DISPATCH
// ============================================================================

/**
 * Get all arguments of a term. O(1).
 * Flat: {tag: 'plus', children: [a, b, c]} → [a, b, c]
 */
function getArgs(hash) {
  const node = Store.get(hash);
  if (!node) return [];
  if (isPredTag(node.tag)) return node.children;
  return [];
}

/**
 * Try FFI for a goal before clause search
 *
 * @param {number} goal - Goal term hash (already substituted)
 * @param {Object} ffiMeta - FFI metadata for predicates
 * @returns {{ success: boolean, theta?: Array }|null} - null if no FFI
 */
function tryFFI(goal, ffiMeta) {
  const head = getHead(goal);
  if (!head) return null;

  const meta = ffiMeta[head];
  if (!meta || !meta.ffi) return null;

  const args = getArgs(goal);

  // Check mode
  if (!ffi.mode.checkMode(args, meta.mode)) {
    return null;  // Mode mismatch → fall back to clauses
  }

  // Dispatch to FFI function
  const fn = ffi.get(meta.ffi);
  if (!fn) {
    return null;
  }

  return fn(args);
}

// ============================================================================
// PROOF SEARCH
// ============================================================================

/**
 * Prove a goal using backward chaining with indexing
 *
 * @param {number} goal - Goal hash to prove
 * @param {Map} clauses - Map of name → { hash, premises }
 * @param {Map} types - Map of name → hash (axioms/facts)
 * @param {Object} opts - { maxDepth, trace, index, ffiMeta, useFFI }
 * @returns {{ success: boolean, theta?: Array, trace?: string[] }}
 */
function prove(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const trace = opts.trace ? [] : null;
  const idx = opts.index || buildIndex(clauses, types);
  const useFFI = opts.useFFI !== false; // Default: true
  const ffiMeta = opts.ffiMeta || (useFFI ? ffi.defaultMeta : {});

  let freshCounter = 0;

  function search(g, theta, depth) {
    if (depth > maxDepth) return null;

    const goalInst = subApply(g, theta);

    // Try FFI first (before clause search)
    if (useFFI) {
      const ffiResult = tryFFI(goalInst, ffiMeta);
      if (ffiResult && ffiResult.success) {
        const indent = trace ? '  '.repeat(depth) : '';
        if (trace) trace.push(`${indent}FFI: ${getHead(goalInst)} ✓`);
        return [...theta, ...ffiResult.theta];
      }
    }

    const { types: candTypes, clauses: candClauses } = getCandidates(idx, goalInst);

    const indent = trace ? '  '.repeat(depth) : '';
    if (trace) trace.push(`${indent}Goal: ${formatTerm(goalInst)} [${candTypes.length}t/${candClauses.length}c]`);

    // Try types (axioms)
    for (const [name, typeHash] of candTypes) {
      const freshType = freshenTerm(typeHash, freshCounter++, 'a');
      const newTheta = unify(freshType, goalInst);
      if (newTheta !== null) {
        const merged = [...theta, ...newTheta];
        if (trace) trace.push(`${indent}  ✓ ${name}`);
        return merged;
      }
    }

    // Try clauses
    for (const [name, clause] of candClauses) {
      const { head, premises } = freshenClause(clause, freshCounter++);
      const newTheta = unify(head, goalInst);
      if (newTheta === null) continue;

      if (trace) trace.push(`${indent}  → ${name}`);

      let currentTheta = [...theta, ...newTheta];
      let ok = true;

      for (const premise of premises) {
        const result = search(subApply(premise, currentTheta), currentTheta, depth + 1);
        if (result === null) { ok = false; break; }
        currentTheta = result;
      }

      if (ok) {
        if (trace) trace.push(`${indent}  ✓ ${name}`);
        return currentTheta;
      }
    }

    if (trace) trace.push(`${indent}  ✗`);
    return null;
  }

  const result = search(goal, [], 0);
  return { success: result !== null, theta: result, trace };
}

// ============================================================================
// FRESHENING - Rename variables to avoid capture
// ============================================================================

function freshenTerm(h, counter, prefix = '') {
  const suffix = `_${prefix}${counter}`;
  const renamed = new Map();

  function go(hash) {
    const node = Store.get(hash);
    if (!node) return hash;

    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(hash)) {
          renamed.set(hash, Store.put('freevar', [name + suffix]));
        }
        return renamed.get(hash);
      }
      return hash;
    }

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });

    return changed ? Store.put(node.tag, newChildren) : hash;
  }

  return go(h);
}

function freshenClause(clause, counter) {
  const suffix = `_c${counter}`;
  const renamed = new Map();

  function go(h) {
    const node = Store.get(h);
    if (!node) return h;

    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(h)) {
          renamed.set(h, Store.put('freevar', [name + suffix]));
        }
        return renamed.get(h);
      }
      return h;
    }

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });

    return changed ? Store.put(node.tag, newChildren) : h;
  }

  return {
    head: go(clause.hash),
    premises: clause.premises.map(go)
  };
}

// ============================================================================
// UTILITIES
// ============================================================================

function formatTerm(h, depth = 0) {
  if (depth > 5) return '...';
  const node = Store.get(h);
  if (!node) return '?';
  if (node.tag === 'atom') return node.children[0];
  if (node.tag === 'freevar') return node.children[0];
  if (node.tag === 'binlit') return `0b${node.children[0].toString(2)}`;
  // Flat predicate or connective with children
  if (node.children.length === 0) return node.tag;
  const args = node.children.map(c =>
    typeof c === 'number' ? formatTerm(c, depth + 1) : String(c)
  ).join(' ');
  return `${node.tag} ${args}`;
}

function extractSolution(theta, goal) {
  const solution = {};
  const goalVars = new Set();

  (function findVars(h) {
    const node = Store.get(h);
    if (!node) return;
    if (node.tag === 'freevar' && node.children[0]?.startsWith('_')) {
      goalVars.add(h);
    }
    for (const c of node.children) {
      if (typeof c === 'number') findVars(c);
    }
  })(goal);

  function fullyApply(h) {
    let current = h;
    for (let i = 0; i < 100; i++) {
      const prev = current;
      current = subApply(current, theta);
      const node = Store.get(current);
      if (node?.tag === 'freevar') {
        for (const [v, val] of theta) {
          if (v === current) { current = val; break; }
        }
      }
      if (current === prev) break;
    }
    return current;
  }

  for (const varHash of goalVars) {
    const varName = Store.get(varHash)?.children[0];
    if (varName) {
      solution[varName.slice(1)] = formatTerm(fullyApply(varHash));
    }
  }

  return solution;
}

module.exports = { prove, extractSolution, formatTerm, buildIndex, getCandidates };
