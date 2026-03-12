/**
 * Backward Chaining Prover for MDE Clauses
 *
 * Depth-first search with unification and first-argument indexing.
 * Supports FFI (Foreign Function Interface) for computational predicates.
 * Phase 3b: optional proof term construction via buildTerm option.
 */

const Store = require('../kernel/store');
const { isPredTag, getPredicateHead: getHead, buildRightTensor } = require('../kernel/ast');
const { unify } = require('../kernel/unify');
const { apply: subApply } = require('../kernel/substitute');
const ffi = require('./ffi');

/**
 * Get first argument's outermost constructor. O(1).
 * Flat: {tag: 'plus', children: [i(X), Y, Z]} → 'i'
 */
function getFirstArgHead(hash) {
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
    const fa = getFirstArgHead(hash) || '_';
    (idx.types[head] ||= {})[fa] ||= [];
    idx.types[head][fa].push([name, hash]);
  }

  for (const [name, clause] of clauses) {
    const head = getHead(clause.hash);
    if (!head) continue;
    const fa = getFirstArgHead(clause.hash) || '_';
    (idx.clauses[head] ||= {})[fa] ||= [];
    idx.clauses[head][fa].push([name, clause]);
  }

  return idx;
}

/**
 * Get candidate types and clauses for a goal. O(1).
 * Returns items from specific bucket + catch-all bucket.
 */
function getCandidates(idx, goalHash, allBuckets) {
  const head = getHead(goalHash);
  if (!head) return { types: [], clauses: [] };

  const fa = getFirstArgHead(goalHash) || '_';
  const ti = idx.types[head] || {};
  const ci = idx.clauses[head] || {};

  // When first arg is wildcard (freevar) and allBuckets enabled,
  // return ALL buckets (needed for noFFI clause-only resolution)
  if (fa === '_' && allBuckets) {
    const allTypes = [], allClauses = [];
    for (const k in ti) for (const item of ti[k]) allTypes.push(item);
    for (const k in ci) for (const item of ci[k]) allClauses.push(item);
    return { types: allTypes, clauses: allClauses };
  }

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
// PROOF TERM CONSTRUCTION
// ============================================================================

/**
 * Build a right-associated tensor_r spine from leaf proof terms.
 * @param {Object[]} terms - Leaf GenericTerm nodes
 * @returns {Object} GenericTerm — right-associated tensor_r tree
 */
function buildTensorRSpine(terms) {
  if (terms.length === 0) return { rule: 'one_r', principal: null, subterms: [] };
  if (terms.length === 1) return terms[0];
  let acc = terms[terms.length - 1];
  for (let i = terms.length - 2; i >= 0; i--) {
    acc = { rule: 'tensor_r', principal: null, subterms: [terms[i], acc] };
  }
  return acc;
}

/**
 * Build a clause proof term from ground components.
 *
 * Reconstructs: copy(groundLoli, loli_l(antProof, monad_l(id(Q))))
 * where groundLoli = loli(tensor(!P₁,...,!Pₖ), monad(Q))
 *
 * @param {number[]} groundPrems - Ground premise hashes (fully substituted)
 * @param {Object[]} premTerms - Proof terms for each premise
 * @param {number} groundHead - Ground head hash (the goal Q)
 * @returns {Object} GenericTerm — complete clause proof term
 */
function buildClauseTerm(groundPrems, premTerms, groundHead) {
  // Reconstruct ground loli: loli(tensor(!P₁,...,!Pₖ), monad(Q))
  const bangGroundPrems = groundPrems.map(p => Store.put('bang', [p]));
  const groundAnt = buildRightTensor(bangGroundPrems);
  const groundMonad = Store.put('monad', [groundHead]);
  const groundLoli = Store.put('loli', [groundAnt, groundMonad]);

  // Antecedent proof: right-associated tensor_r of promotion(premTerm) nodes
  const wrappedPrems = premTerms.map(pt =>
    ({ rule: 'promotion', principal: null, subterms: [pt] }));
  const antProof = buildTensorRSpine(wrappedPrems);

  // Continuation: monad_l unwraps, id resolves goal
  const monadBody = { rule: 'monad_l', principal: groundMonad, subterms: [
    { rule: 'id', principal: groundHead, subterms: [] }
  ]};
  const loliApp = { rule: 'loli_l', principal: groundLoli,
                    subterms: [antProof, monadBody] };
  return { rule: 'copy', principal: groundLoli, subterms: [loliApp] };
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
 * @param {Object} opts - { maxDepth, trace, index, ffiMeta, useFFI, buildTerm }
 * @returns {{ success: boolean, theta?: Array, trace?: string[], term?: Object }}
 */
function prove(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const trace = opts.trace ? [] : null;
  const idx = opts.index || buildIndex(clauses, types);
  const useFFI = opts.useFFI !== false; // Default: true
  const ffiMeta = opts.ffiMeta || (useFFI ? ffi.defaultMeta : {});
  const buildTerm = !!opts.buildTerm;
  const allBuckets = !!opts.allBuckets;

  let freshCounter = 0;

  /**
   * Search for a proof of goal g under substitution theta.
   *
   * @returns {{ theta: Array, term: Object|null }|null} - null on failure
   */
  // Transitive apply: resolve non-idempotent theta (DFS accumulation produces chains:
  // _J → o(_Y), _Y → i(_X), _X → 0x1). Build a Map for O(1) lookup, then
  // recursively resolve each freevar to its fully-ground value.
  let _thetaMap = null;
  let _thetaMapLen = -1;

  // Chase a freevar through the theta map iteratively (path compression).
  // Returns the ultimate non-freevar value, or the last unbound freevar.
  function _chaseFreevar(h) {
    let cur = h;
    while (true) {
      const v = _thetaMap.get(cur);
      if (v === undefined) { if (cur !== h) _thetaMap.set(h, cur); return cur; }
      if (!Store.isTerm(v) || Store.tag(v) !== 'freevar') {
        // v is a non-freevar — path-compress h directly to v
        if (cur !== h) _thetaMap.set(h, v);
        return v;
      }
      cur = v;
    }
  }

  function _resolveHash(startH) {
    // Iterative post-order traversal to avoid stack overflow on deep theta chains.
    // Each frame: [hash, childIndex, childResults, changed]
    const stack = [[startH, -1, null, false]];
    let result = startH;

    while (stack.length > 0) {
      const frame = stack[stack.length - 1];
      let h = frame[0];

      // Phase: initial entry (childIndex === -1)
      if (frame[1] === -1) {
        if (!Store.isTerm(h)) { result = h; stack.pop(); continue; }
        const tag = Store.tag(h);
        if (!tag) { result = h; stack.pop(); continue; }
        if (tag === 'freevar') {
          h = _chaseFreevar(h);
          if (!Store.isTerm(h) || Store.tag(h) === 'freevar') { result = h; stack.pop(); continue; }
          // h is now a non-freevar value — resolve its structure
          frame[0] = h;
        }
        const tag2 = Store.tag(h);
        if (tag2 === 'atom' || tag2 === 'binlit' || tag2 === 'strlit' || tag2 === 'charlit') {
          result = h; stack.pop(); continue;
        }
        if (tag2 === 'arrlit') {
          const elems = Store.getArrayElements(h);
          if (!elems || elems.length === 0) { result = h; stack.pop(); continue; }
          frame[1] = 0; frame[2] = new Uint32Array(elems.length); frame[3] = false;
          // Push first element
          stack.push([elems[0], -1, null, false]);
          continue;
        }
        const arity = Store.arity(h);
        if (arity === 0) { result = h; stack.pop(); continue; }
        frame[1] = 0; frame[2] = new Array(arity); frame[3] = false;
        // Push first child
        const c0 = Store.child(h, 0);
        if (Store.isTermChild(c0)) {
          stack.push([c0, -1, null, false]);
        } else {
          frame[2][0] = c0; frame[1] = 1;
          if (arity > 1) {
            const c1 = Store.child(h, 1);
            if (Store.isTermChild(c1)) { stack.push([c1, -1, null, false]); }
            else { frame[2][1] = c1; frame[1] = 2; }
          }
        }
        continue;
      }

      // Phase: collecting child results
      const tag2 = Store.tag(h);
      if (tag2 === 'arrlit') {
        const elems = Store.getArrayElements(h);
        const idx = frame[1];
        // Store result from previous child
        frame[2][idx] = result;
        if (result !== elems[idx]) frame[3] = true;
        const next = idx + 1;
        if (next < elems.length) {
          frame[1] = next;
          stack.push([elems[next], -1, null, false]);
          continue;
        }
        result = frame[3] ? Store.putArray(frame[2]) : h;
        stack.pop();
        continue;
      }

      // Regular term children
      const arity = Store.arity(h);
      const idx = frame[1];
      const origChild = Store.child(h, idx);
      if (Store.isTermChild(origChild)) {
        frame[2][idx] = result;
        if (result !== origChild) frame[3] = true;
      }
      const next = idx + 1;
      if (next < arity) {
        frame[1] = next;
        const cn = Store.child(h, next);
        if (Store.isTermChild(cn)) {
          stack.push([cn, -1, null, false]);
        } else {
          frame[2][next] = cn;
          frame[1] = next + 1;
          if (next + 1 < arity) {
            const cn2 = Store.child(h, next + 1);
            if (Store.isTermChild(cn2)) { stack.push([cn2, -1, null, false]); }
            else { frame[2][next + 1] = cn2; frame[1] = next + 2; }
          }
        }
        if (frame[1] < arity) continue;
      }
      result = frame[3] ? Store.put(tag2, frame[2]) : h;
      stack.pop();
    }

    // Memoize: if startH was a freevar, cache the fully resolved result
    if (Store.isTerm(startH) && Store.tag(startH) === 'freevar' && result !== startH) {
      _thetaMap.set(startH, result);
    }
    return result;
  }

  function deepApply(h, th) {
    if (th.length === 0) return h;
    // Rebuild map only when theta grows
    if (_thetaMapLen !== th.length) {
      _thetaMap = new Map();
      for (let i = 0; i < th.length; i++) _thetaMap.set(th[i][0], th[i][1]);
      _thetaMapLen = th.length;
    }
    return _resolveHash(h);
  }

  function search(g, theta, depth) {
    if (depth > maxDepth) return null;

    const goalInst = deepApply(g, theta);

    // Try FFI first (before clause search)
    if (useFFI) {
      const ffiResult = tryFFI(goalInst, ffiMeta);
      if (ffiResult && ffiResult.success) {
        const indent = trace ? '  '.repeat(depth) : '';
        if (trace) trace.push(`${indent}FFI: ${getHead(goalInst)} ✓`);
        return {
          theta: [...theta, ...ffiResult.theta],
          term: buildTerm ? { rule: 'ffi', principal: null, subterms: [] } : null
        };
      }
    }

    const { types: candTypes, clauses: candClauses } = getCandidates(idx, goalInst, allBuckets);

    const indent = trace ? '  '.repeat(depth) : '';
    if (trace) trace.push(`${indent}Goal: ${formatTerm(goalInst)} [${candTypes.length}t/${candClauses.length}c]`);

    // Try types (axioms) — fact found directly in gamma
    for (const [name, typeHash] of candTypes) {
      const freshType = freshenTerm(typeHash, freshCounter++, 'a');
      const newTheta = unify(freshType, goalInst);
      if (newTheta !== null) {
        const merged = [...theta, ...newTheta];
        if (trace) trace.push(`${indent}  ✓ ${name}`);
        return {
          theta: merged,
          term: buildTerm ? {
            rule: 'copy', principal: goalInst,
            subterms: [{ rule: 'id', principal: goalInst, subterms: [] }]
          } : null
        };
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
      const premTerms = [];

      for (const premise of premises) {
        const r = search(deepApply(premise, currentTheta), currentTheta, depth + 1);
        if (r === null) { ok = false; break; }
        currentTheta = r.theta;
        if (buildTerm) premTerms.push(r.term);
      }

      if (ok) {
        if (trace) trace.push(`${indent}  ✓ ${name}`);
        const groundHead = subApply(head, currentTheta);
        const groundPrems = premises.map(p => subApply(p, currentTheta));
        return {
          theta: currentTheta,
          term: buildTerm ? buildClauseTerm(groundPrems, premTerms, groundHead) : null
        };
      }
    }

    if (trace) trace.push(`${indent}  ✗`);
    return null;
  }

  const result = search(goal, [], 0);
  return {
    success: result !== null,
    theta: result ? result.theta : null,
    term: result ? result.term : null,
    trace
  };
}

// ============================================================================
// FRESHENING - Rename variables to avoid capture
// ============================================================================

/** Create a freshening function that renames _-prefixed freevars with a unique suffix. */
function makeFreshener(counter, prefix) {
  const suffix = `_${prefix}${counter}`;
  const renamed = new Map();

  return function freshen(h) {
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
        const nc = freshen(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });

    return changed ? Store.put(node.tag, newChildren) : h;
  };
}

function freshenTerm(h, counter, prefix = '') {
  return makeFreshener(counter, prefix)(h);
}

function freshenClause(clause, counter) {
  const f = makeFreshener(counter, 'c');
  return { head: f(clause.hash), premises: clause.premises.map(f) };
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

module.exports = { prove, formatTerm, buildIndex, getCandidates };
