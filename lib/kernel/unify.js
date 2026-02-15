/**
 * Unification for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 *
 * Supports ephemeral expansion for compact primitive literals:
 * - binlit(n) can be pattern-matched against (i X), (o X), e
 * - strlit(s) can be pattern-matched against cons(H, T), nil
 */

const Store = require('./store');
const { occurs } = require('./substitute');

// ============================================================================
// EPHEMERAL EXPANSION FOR PRIMITIVES
// ============================================================================

/**
 * Try to unify a pattern against a binlit term via ephemeral expansion
 *
 * binlit(10n) vs (o X) → X = binlit(5n)
 * binlit(0n) vs e → success
 * binlit(7n) vs (i X) → X = binlit(3n)
 *
 * @param {number} pattern - Pattern term hash
 * @param {number} term - binlit term hash
 * @param {Array} G - Goal list to push new constraints to
 * @returns {boolean} Whether ephemeral expansion succeeded
 */
function unifyBinlit(pattern, term, G) {
  if (Store.tag(term) !== 'binlit') return false;
  const value = Store.child(term, 0);

  const ptag = Store.tag(pattern);
  if (!ptag) return false;

  // Pattern: e (zero)
  if (ptag === 'atom' && Store.child(pattern, 0) === 'e') {
    return value === 0n;
  }

  // Pattern: binlit (direct comparison)
  if (ptag === 'binlit') {
    return Store.child(pattern, 0) === value;
  }

  // Flat: i(X) or o(X)
  if ((ptag === 'i' || ptag === 'o') && Store.arity(pattern) === 1) {
    const tailPattern = Store.child(pattern, 0);
    if (ptag === 'o') {
      if (value === 0n || value % 2n !== 0n) return false;
      G.push([tailPattern, Store.put('binlit', [value / 2n])]);
      return true;
    }
    if (ptag === 'i') {
      if (value % 2n !== 1n) return false;
      G.push([tailPattern, Store.put('binlit', [value / 2n])]);
      return true;
    }
  }

  return false;
}

/**
 * Try to unify a pattern against a strlit term via ephemeral expansion
 *
 * strlit("hello") vs cons(H, T) → H = charlit('h'), T = strlit("ello")
 * strlit("") vs nil → success
 *
 * @param {number} pattern - Pattern term hash
 * @param {number} term - strlit term hash
 * @param {Array} G - Goal list to push new constraints to
 * @returns {boolean} Whether ephemeral expansion succeeded
 */
function unifyStrlit(pattern, term, G) {
  if (Store.tag(term) !== 'strlit') return false;
  const str = Store.child(term, 0);

  const ptag = Store.tag(pattern);
  if (!ptag) return false;

  // Pattern: nil (empty string)
  if (ptag === 'atom' && Store.child(pattern, 0) === 'nil') {
    return str === '';
  }

  // Pattern: strlit (direct comparison)
  if (ptag === 'strlit') {
    return Store.child(pattern, 0) === str;
  }

  // Flat: cons(H, T)
  if (ptag === 'cons' && Store.arity(pattern) === 2) {
    if (str === '') return false;
    const firstChar = Store.put('charlit', [str.charCodeAt(0)]);
    const restStr = Store.put('strlit', [str.slice(1)]);
    G.push([Store.child(pattern, 0), firstChar]);
    G.push([Store.child(pattern, 1), restStr]);
    return true;
  }

  return false;
}

/**
 * Check if term is a metavar (unification variable)
 * Metavars are freevars whose name starts with underscore
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const isMetavar = h => {
  if (Store.tag(h) !== 'freevar') return false;
  const name = Store.child(h, 0);
  return typeof name === 'string' && name.startsWith('_');
};

/**
 * Check if term is a regular freevar (not a metavar)
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const isFreevar = h => {
  if (Store.tag(h) !== 'freevar') return false;
  const name = Store.child(h, 0);
  return typeof name === 'string' && !name.startsWith('_');
};

/**
 * Alias for isMetavar (backwards compat)
 */
const isVar = isMetavar;

/**
 * Get the variable name from a freevar term
 * @param {number} h - Freevar hash
 * @returns {string|undefined}
 */
const getVarName = h => {
  if (Store.tag(h) !== 'freevar') return undefined;
  return Store.child(h, 0);
};

// ============================================================================
// UNION-FIND UNIFICATION
// ============================================================================

/**
 * Union-Find data structure for unification
 * Supports path compression for O(α(n)) operations
 */
class UnionFind {
  constructor() {
    this.parent = new Map();  // var → (var | ground term)
  }

  /**
   * Find the canonical representative of a term
   * @param {number} v - Term hash
   * @returns {number} Canonical representative
   */
  find(v) {
    if (!this.parent.has(v)) return v;

    const p = this.parent.get(v);

    // If parent is not a metavar, it's the ground binding
    if (Store.tag(p) !== 'freevar' || !Store.child(p, 0)?.startsWith('_')) {
      return p;
    }

    // Path compression: make v point directly to root
    const root = this.find(p);
    if (root !== p) {
      this.parent.set(v, root);
    }
    return root;
  }

  /**
   * Union two terms (bind var to term)
   * @param {number} v - Variable hash
   * @param {number} term - Term to bind to
   */
  union(v, term) {
    const rv = this.find(v);
    this.parent.set(rv, term);
  }

  /**
   * Convert to theta list for compatibility
   * @returns {Array<[number, number]>}
   */
  toTheta() {
    const theta = [];
    const processed = new Set();

    for (const [v] of this.parent) {
      if (processed.has(v)) continue;

      const root = this.find(v);
      if (root !== v) {
        theta.push([v, root]);
      }
      processed.add(v);
    }

    return theta;
  }
}

/**
 * Occurs check within union-find context
 * @param {number} v - Variable to check for
 * @param {number} h - Term to check in
 * @param {UnionFind} uf - Union-find structure
 * @returns {boolean}
 */
function occursInUF(v, h, uf) {
  const resolved = uf.find(h);
  if (v === resolved) return true;

  const a = Store.arity(resolved);
  for (let i = 0; i < a; i++) {
    const c = Store.child(resolved, i);
    if (Store.isTermChild(c) && occursInUF(v, c, uf)) return true;
  }
  return false;
}

/**
 * Unify two terms using union-find
 * Complexity: O(K × α(K) × M) ≈ O(K × M) where K = bindings, M = term size
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @param {Object} opts - Options { deferOccursCheck: boolean }
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unifyUF = (a, b, opts = {}) => {
  const deferOccursCheck = opts.deferOccursCheck || false;
  const uf = new UnionFind();
  const G = [[a, b]];
  const deferredChecks = [];  // For deferred occurs check

  while (G.length) {
    const [t0raw, t1raw] = G.pop();

    // Resolve through union-find
    const t0 = uf.find(t0raw);
    const t1 = uf.find(t1raw);

    // Equal after resolution - nothing to do
    if (t0 === t1) continue;

    // Metavar on left - bind it
    if (isMetavar(t0)) {
      if (deferOccursCheck) {
        // Defer occurs check to end
        deferredChecks.push([t0, t1]);
      } else {
        // Eager occurs check
        if (occursInUF(t0, t1, uf)) return null;
      }
      uf.union(t0, t1);
      continue;
    }

    // Metavar on right - swap and retry
    if (isMetavar(t1)) {
      G.push([t1, t0]);
      continue;
    }

    // Both are freevars (not metavars) - must have same name
    if (isFreevar(t0) && isFreevar(t1)) {
      if (getVarName(t0) !== getVarName(t1)) return null;
      continue;
    }

    // Get tags for structural comparison
    const tag0 = Store.tag(t0);
    const tag1 = Store.tag(t1);

    // Both must be valid nodes
    if (!tag0 || !tag1) return null;

    // Ephemeral expansion for binlit
    if (tag0 === 'binlit' || tag1 === 'binlit') {
      // binlit vs binlit: direct value comparison
      if (tag0 === 'binlit' && tag1 === 'binlit') {
        if (Store.child(t0, 0) !== Store.child(t1, 0)) return null;
        continue;
      }
      // Pattern vs binlit: ephemeral expansion
      const [pat, lit] = tag0 === 'binlit' ? [t1, t0] : [t0, t1];
      if (!unifyBinlit(pat, lit, G)) return null;
      continue;
    }

    // Ephemeral expansion for strlit
    if (tag0 === 'strlit' || tag1 === 'strlit') {
      // strlit vs strlit: direct value comparison
      if (tag0 === 'strlit' && tag1 === 'strlit') {
        if (Store.child(t0, 0) !== Store.child(t1, 0)) return null;
        continue;
      }
      // Pattern vs strlit: ephemeral expansion
      const [pat, lit] = tag0 === 'strlit' ? [t1, t0] : [t0, t1];
      if (!unifyStrlit(pat, lit, G)) return null;
      continue;
    }

    // Charlit: direct value comparison only
    if (tag0 === 'charlit' || tag1 === 'charlit') {
      if (tag0 !== 'charlit' || tag1 !== 'charlit') return null;
      if (Store.child(t0, 0) !== Store.child(t1, 0)) return null;
      continue;
    }

    // Same tag and arity - decompose
    const arity0 = Store.arity(t0);
    if (tag0 === tag1 && arity0 === Store.arity(t1)) {
      for (let i = 0; i < arity0; i++) {
        const c0 = Store.child(t0, i);
        const c1 = Store.child(t1, i);
        if (Store.isTermChild(c0) && Store.isTermChild(c1)) {
          G.push([c0, c1]);
        } else if (c0 !== c1) {
          return null;
        }
      }
      continue;
    }

    // Different structure - fail
    return null;
  }

  // Deferred occurs check at end (if enabled)
  if (deferOccursCheck) {
    for (const [v, term] of deferredChecks) {
      if (occursInUF(v, term, uf)) return null;
    }
  }

  return uf.toTheta();
};

/**
 * Unify two terms, returning MGU substitution or null
 * Uses union-find for better performance
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unify = (a, b) => unifyUF(a, b, { deferOccursCheck: false });

/**
 * One-way matching: pattern matches term
 * @param {number} pattern - Pattern hash (may contain metavars)
 * @param {number} term - Term hash (ground)
 * @param {Array<[number, number]>} initialTheta - Initial substitution to extend
 * @returns {Array<[number, number]>|null} Substitution or null
 */
// Module-level flat worklist (match is iterative and non-reentrant on hot path).
//
// WARNING — NON-REENTRANT: _Gp/_Gt are shared mutable state. match() must NEVER
// be called from within another match() call. This is safe because:
//   1. match() is purely iterative (worklist loop, no recursion)
//   2. match() only calls Store read functions and Store.put (no callbacks)
//   3. The backward prover uses unify() (separate code path), not match()
//   4. Forward chaining is single-threaded with no async boundaries
//
// If a future prover needs reentrant matching, it must either:
//   - Use unify() instead (pair-based, no shared state)
//   - Allocate a local worklist (opt out of this optimization)
//   - Guard with: if (_matchActive) throw new Error('match is non-reentrant')
let _Gp = new Array(64);  // pattern side
let _Gt = new Array(64);  // term side

const match = (pattern, term, initialTheta = []) => {
  _Gp[0] = pattern; _Gt[0] = term;
  let gLen = 1;
  let theta = initialTheta;

  while (gLen > 0) {
    gLen--;
    const p = _Gp[gLen], t = _Gt[gLen];

    // Equal - nothing to do
    if (p === t) continue;

    // Pattern is a metavar - bind it
    if (isVar(p)) {
      // Check for consistent binding (manual loop avoids closure allocation)
      let existingVal = undefined;
      for (let ti = 0; ti < theta.length; ti++) {
        if (theta[ti][0] === p) { existingVal = theta[ti][1]; break; }
      }
      if (existingVal !== undefined && existingVal !== t) return null;
      if (existingVal === undefined) { theta.push([p, t]); }
      continue;
    }

    // Get tags for structural comparison
    const tp = Store.tag(p);
    const tt = Store.tag(t);

    if (!tp || !tt) return null;

    // Same tag and arity - decompose
    const ap = Store.arity(p);
    if (tp === tt && ap === Store.arity(t)) {
      // Grow if needed (rare, amortized)
      if (gLen + ap > _Gp.length) {
        const newSize = _Gp.length * 2;
        const ngp = new Array(newSize);
        const ngt = new Array(newSize);
        for (let j = 0; j < gLen; j++) { ngp[j] = _Gp[j]; ngt[j] = _Gt[j]; }
        _Gp = ngp; _Gt = ngt;
      }
      for (let i = 0; i < ap; i++) {
        const cp = Store.child(p, i);
        const ct = Store.child(t, i);
        if (Store.isTermChild(cp) && Store.isTermChild(ct)) {
          _Gp[gLen] = cp; _Gt[gLen] = ct; gLen++;
        } else if (cp !== ct) {
          return null;
        }
      }
      continue;
    }

    // Ephemeral expansion for binlit in match (inlined to avoid pair allocation)
    if (tt === 'binlit') {
      const value = Store.child(t, 0);
      const ptag = tp;

      if (ptag === 'atom' && Store.child(p, 0) === 'e') {
        if (value !== 0n) return null;
        continue;
      }
      if (ptag === 'binlit') {
        if (Store.child(p, 0) !== value) return null;
        continue;
      }
      if ((ptag === 'i' || ptag === 'o') && Store.arity(p) === 1) {
        const tailPattern = Store.child(p, 0);
        if (ptag === 'o') {
          if (value === 0n || value % 2n !== 0n) return null;
          _Gp[gLen] = tailPattern; _Gt[gLen] = Store.put('binlit', [value / 2n]); gLen++;
          continue;
        }
        if (ptag === 'i') {
          if (value % 2n !== 1n) return null;
          _Gp[gLen] = tailPattern; _Gt[gLen] = Store.put('binlit', [value / 2n]); gLen++;
          continue;
        }
      }
      return null;
    }

    // Different structure - fail
    return null;
  }

  return theta;
};

// ============================================================================
// INDEXED MATCH — Stage 6 de Bruijn theta (O(1) metavar lookup)
// ============================================================================

/**
 * Module-level undo stack for indexed match.
 * Tracks which theta slots were written, enabling O(k) rollback on failure
 * where k = bindings since last save point (typically 1-3).
 *
 * Same non-reentrant safety guarantees as _Gp/_Gt above.
 * See doc/research/de-bruijn-indexed-matching.md.
 */
let _undoStack = new Uint8Array(32);
let _undoLen = 0;

/**
 * One-way matching with indexed theta (Stage 6 de Bruijn).
 *
 * Instead of scanning flat theta [v0,t0,v1,t1,...] for each metavar,
 * uses compile-time slot assignment for O(1) lookup: theta[slots[v]].
 *
 * Shares _Gp/_Gt worklist with match() (same non-reentrant constraints).
 * Caller must save/restore _undoLen for failure rollback.
 *
 * @param {number} pattern - Pattern hash (may contain metavars)
 * @param {number} term - Term hash (ground)
 * @param {Array} theta - Indexed theta array (theta[slot] = value)
 * @param {Object} slots - { [metavarHash]: slotIndex } from compileRule
 * @returns {boolean} true on success (theta modified), false on failure
 */
const matchIndexed = (pattern, term, theta, slots) => {
  _Gp[0] = pattern; _Gt[0] = term;
  let gLen = 1;

  while (gLen > 0) {
    gLen--;
    const p = _Gp[gLen], t = _Gt[gLen];

    if (p === t) continue;

    // Pattern is a metavar — O(1) indexed lookup
    if (isVar(p)) {
      const slot = slots[p];
      const existing = theta[slot];
      if (existing !== undefined) {
        if (existing !== t) return false;
      } else {
        theta[slot] = t;
        _undoStack[_undoLen++] = slot;
      }
      continue;
    }

    const tp = Store.tag(p);
    const tt = Store.tag(t);
    if (!tp || !tt) return false;

    // Same tag and arity — decompose
    const ap = Store.arity(p);
    if (tp === tt && ap === Store.arity(t)) {
      if (gLen + ap > _Gp.length) {
        const newSize = _Gp.length * 2;
        const ngp = new Array(newSize);
        const ngt = new Array(newSize);
        for (let j = 0; j < gLen; j++) { ngp[j] = _Gp[j]; ngt[j] = _Gt[j]; }
        _Gp = ngp; _Gt = ngt;
      }
      for (let i = 0; i < ap; i++) {
        const cp = Store.child(p, i);
        const ct = Store.child(t, i);
        if (Store.isTermChild(cp) && Store.isTermChild(ct)) {
          _Gp[gLen] = cp; _Gt[gLen] = ct; gLen++;
        } else if (cp !== ct) {
          return false;
        }
      }
      continue;
    }

    // Ephemeral expansion for binlit
    if (tt === 'binlit') {
      const value = Store.child(t, 0);
      if (tp === 'atom' && Store.child(p, 0) === 'e') {
        if (value !== 0n) return false;
        continue;
      }
      if (tp === 'binlit') {
        if (Store.child(p, 0) !== value) return false;
        continue;
      }
      if ((tp === 'i' || tp === 'o') && Store.arity(p) === 1) {
        const tailPattern = Store.child(p, 0);
        if (tp === 'o') {
          if (value === 0n || value % 2n !== 0n) return false;
          _Gp[gLen] = tailPattern; _Gt[gLen] = Store.put('binlit', [value / 2n]); gLen++;
          continue;
        }
        if (tp === 'i') {
          if (value % 2n !== 1n) return false;
          _Gp[gLen] = tailPattern; _Gt[gLen] = Store.put('binlit', [value / 2n]); gLen++;
          continue;
        }
      }
      return false;
    }

    return false;
  }

  return true;
};

/** Save current undo position (call before matchIndexed). */
const undoSave = () => _undoLen;

/** Restore theta slots written since savedLen (call on matchIndexed failure). */
const undoRestore = (theta, savedLen) => {
  while (_undoLen > savedLen) theta[_undoStack[--_undoLen]] = undefined;
};

/** Discard undo entries without restoring theta (call on matchIndexed success). */
const undoDiscard = (savedLen) => { _undoLen = savedLen; };

module.exports = {
  unify,
  match,
  matchIndexed,
  undoSave,
  undoRestore,
  undoDiscard,
  isVar,
  isMetavar,
  isFreevar,
  getVarName,
  // Ephemeral expansion helpers (for testing)
  unifyBinlit,
  unifyStrlit
};
