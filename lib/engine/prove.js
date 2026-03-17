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

// Normalize binary constructor chains (i/o/e) to compact binlit form.
// Prevents hash divergence between forward engine (which normalizes) and
// clause resolution (which builds constructor chains via substitution).
function normalizeBinRec(h) {
  if (!Store.isTerm(h)) return h;
  const tag = Store.tag(h);
  if (!tag) return h;
  // Convert i/o/e constructor chains → compact binlit
  if (tag === 'i' || tag === 'o') {
    const v = ffi.convert.binToInt(h);
    if (v !== null) return ffi.convert.intToBin(v);
  }
  // atom 'e' is binary zero — normalize to binlit(0n)
  if (tag === 'atom') {
    const v = ffi.convert.binToInt(h);
    if (v !== null) return ffi.convert.intToBin(v);
    return h;
  }
  if (tag === 'binlit' || tag === 'strlit' || tag === 'charlit' || tag === 'freevar') return h;
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) {
      const rc = normalizeBinRec(c);
      nc.push(rc);
      if (rc !== c) changed = true;
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(tag, nc) : h;
}

/**
 * Get first argument's outermost constructor. O(1).
 * Flat: {tag: 'plus', children: [i(X), Y, Z]} → 'i'
 */
/**
 * Get first argument's outermost constructor for indexing. O(1).
 * Uses direct Store accessors (tag/child/arity) to avoid object allocation.
 */
function getFirstArgHead(hash) {
  if (!Store.isTerm(hash)) return null;
  const t = Store.tag(hash);
  if (!t || !isPredTag(t) || Store.arity(hash) === 0) return null;
  const firstArg = Store.child(hash, 0);
  if (!Store.isTerm(firstArg)) return null;

  // Classify the first argument by tag
  const argTag = Store.tag(firstArg);
  if (argTag === 'atom') return Store.child(firstArg, 0);
  if (argTag === 'freevar') return '_';
  if (isPredTag(argTag)) return argTag;
  if (argTag === 'binlit') {
    const v = Store.child(firstArg, 0);
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
 * Get all arguments of a predicate term. O(arity).
 * Uses direct accessors to avoid Store.get() object allocation.
 */
function getArgs(hash) {
  if (!Store.isTerm(hash)) return [];
  const t = Store.tag(hash);
  if (!t || !isPredTag(t)) return [];
  const a = Store.arity(hash);
  const args = new Array(a);
  for (let i = 0; i < a; i++) args[i] = Store.child(hash, i);
  return args;
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

  // Tag ID for freevar (stable, pre-registered).
  const _FV_TAG = Store.TAG.freevar;

  // Chase a freevar through the theta map iteratively (path compression).
  // Returns the ultimate non-freevar value, or the last unbound freevar.
  function _chaseFreevar(h) {
    let cur = h;
    while (true) {
      const v = _thetaMap.get(cur);
      if (v === undefined) { if (cur !== h) _thetaMap.set(h, cur); return cur; }
      if (!Store.isTerm(v) || Store.tagId(v) !== _FV_TAG) {
        // v is a non-freevar — path-compress h directly to v
        if (cur !== h) _thetaMap.set(h, v);
        return v;
      }
      cur = v;
    }
  }

  // Leaf tag bitset for _resolveHash (numeric, no string alloc)
  const _RH_LEAF = new Uint8Array(256);
  _RH_LEAF[Store.TAG.atom] = 1;
  _RH_LEAF[Store.TAG.binlit] = 1;
  _RH_LEAF[Store.TAG.strlit] = 1;
  _RH_LEAF[Store.TAG.charlit] = 1;
  const _RH_ARRLIT = Store.TAG.arrlit;

  /**
   * Resolve a term through the theta map: chase freevars iteratively,
   * then recurse into bounded term structure.
   *
   * Hybrid design: freevar chains are unbounded (10,000+ from backward proofs)
   * and use iterative _chaseFreevar. Term structure is bounded by the calculus
   * (max arity 4, depth < 20), safe for recursion.
   */
  function _resolveHash(startH) {
    const result = _resolveRec(startH);
    // Memoize: if startH was a freevar, cache the fully resolved result
    if (Store.isTerm(startH) && Store.tagId(startH) === _FV_TAG && result !== startH) {
      _thetaMap.set(startH, result);
    }
    return result;
  }

  function _resolveRec(h) {
    if (!Store.isTerm(h)) return h;
    let tid = Store.tagId(h);

    // Freevar: chase iteratively (unbounded chain), then resolve the target
    if (tid === _FV_TAG) {
      h = _chaseFreevar(h);
      if (!Store.isTerm(h) || Store.tagId(h) === _FV_TAG) return h;
      tid = Store.tagId(h);
    }

    // Leaf: no children to recurse into
    if (_RH_LEAF[tid]) return h;

    // Arrlit: resolve each element
    if (tid === _RH_ARRLIT) {
      const elems = Store.getArrayElements(h);
      if (!elems || elems.length === 0) return h;
      let changed = false;
      const newElems = new Uint32Array(elems.length);
      for (let i = 0; i < elems.length; i++) {
        const r = _resolveRec(elems[i]);
        newElems[i] = r;
        if (r !== elems[i]) changed = true;
      }
      return changed ? Store.putArray(newElems) : h;
    }

    // Compound term: resolve each child (arity bounded by calculus, max 4)
    const a = Store.arity(h);
    if (a === 0) return h;
    let changed = false;
    const nc = new Array(a);
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (Store.isTermChild(c)) {
        const r = _resolveRec(c);
        nc[i] = r;
        if (r !== c) changed = true;
      } else {
        nc[i] = c;
      }
    }
    return changed ? Store.put(Store.tag(h), nc) : h;
  }

  function deepApply(h, th) {
    if (th.length === 0) return h;
    // Incremental map maintenance: append only new entries when theta grows.
    // Theta is append-only during successful search (DFS accumulation).
    // On backtrack, theta shrinks — detect via length decrease → full rebuild.
    if (th.length > _thetaMapLen) {
      // Growth: append only new entries (O(delta) instead of O(|theta|))
      if (!_thetaMap) _thetaMap = new Map();
      for (let i = Math.max(0, _thetaMapLen); i < th.length; i++) {
        _thetaMap.set(th[i][0], th[i][1]);
      }
      _thetaMapLen = th.length;
    } else if (th.length < _thetaMapLen) {
      // Shrink (backtrack): full rebuild (rare — search backtracks to try next clause)
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
        const groundGoal = normalizeBinRec(subApply(goalInst, merged));
        return {
          theta: merged,
          term: buildTerm ? {
            rule: 'copy', principal: groundGoal,
            subterms: [{ rule: 'id', principal: groundGoal, subterms: [] }]
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
        const groundHead = normalizeBinRec(subApply(head, currentTheta));
        const groundPrems = premises.map(p => normalizeBinRec(subApply(p, currentTheta)));
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

/**
 * Create a freshening function that renames _-prefixed freevars with a unique suffix.
 * Uses direct Store accessors (tag/child/arity) to avoid Store.get() object allocation.
 */
function makeFreshener(counter, prefix) {
  const suffix = `_${prefix}${counter}`;
  const renamed = new Map();

  return function freshen(h) {
    if (!Store.isTerm(h)) return h;
    const t = Store.tag(h);
    if (!t) return h;

    if (t === 'freevar') {
      const name = Store.child(h, 0);
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(h)) {
          renamed.set(h, Store.put('freevar', [name + suffix]));
        }
        return renamed.get(h);
      }
      return h;
    }

    const a = Store.arity(h);
    if (a === 0) return h;
    let changed = false;
    const newChildren = new Array(a);
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (typeof c === 'number') {
        const nc = freshen(c);
        newChildren[i] = nc;
        if (nc !== c) changed = true;
      } else {
        newChildren[i] = c;
      }
    }
    return changed ? Store.put(t, newChildren) : h;
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
