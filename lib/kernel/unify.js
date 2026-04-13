/**
 * Unification for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 *
 * Cross-tag matching for compact literal types (binlit, strlit) is handled
 * by equational theories via the theory API (eq-theory.js). The matchers
 * dispatch through a precomputed _rewriteFromTag[tagId] lookup table.
 *
 * arrlit ↔ acons/ae stays inline because Store.put('acons', [h, arrlit(t)])
 * normalizes to arrlit([h, ...t]), making the rewrite API unusable.
 */

const Store = require('./store');
const { TAG } = Store;
const { occurs } = require('./substitute');
const { defaultTheories, buildTheoryLookup } = require('./eq-theory');

// Hot-path tag ID caches for arrlit expansion and charlit primitive children
const TAG_ARRLIT = TAG.arrlit;
const TAG_ACONS = TAG.acons;
const TAG_CHARLIT = TAG.charlit;

// ── Equational theory dispatch ───────────────────────────────────────
// O(1) lookup: tagId → theory. Rebuilt via setTheories().
let _theories = defaultTheories;
let _rewriteFromTag = buildTheoryLookup(defaultTheories);

/**
 * Register equational theories for all matchers in this module.
 * Rebuilds the O(1) dispatch lookup table.
 * Called by the engine at startup (e.g., adding ILL's binlitTheory).
 */
function setTheories(theories) {
  _theories = theories;
  _rewriteFromTag = buildTheoryLookup(theories);
}

/** Legacy arrlit helper — stays inline due to Store normalization. */
function unifyArrlit(pattern, term, G) {
  if (Store.tag(term) !== 'arrlit') return false;
  const elems = Store.getArrayElements(term);
  const ptag = Store.tag(pattern);
  if (!ptag) return false;
  if (ptag === 'atom' && Store.child(pattern, 0) === 'ae') return elems.length === 0;
  if (ptag === 'acons' && Store.arity(pattern) === 2) {
    if (elems.length === 0) return false;
    G.push([Store.child(pattern, 0), elems[0]]);
    const tailData = new Uint32Array(elems.length - 1);
    for (let i = 1; i < elems.length; i++) tailData[i - 1] = elems[i];
    G.push([Store.child(pattern, 1), Store.put('arrlit', [tailData])]);
    return true;
  }
  return false;
}

// ============================================================================
// METAVAR / FREEVAR HELPERS
// ============================================================================

const _MV_TAG = Store.TAG.metavar;
const isMetavar = h => Store.tagId(h) === _MV_TAG;

const _FV_TAG_U = Store.TAG.freevar;
const isFreevar = h => Store.tagId(h) === _FV_TAG_U;

const getVarName = h => {
  const tid = Store.tagId(h);
  if (tid !== _FV_TAG_U && tid !== _MV_TAG) return undefined;
  return Store.child(h, 0);
};

// ============================================================================
// UNION-FIND UNIFICATION
// ============================================================================

class UnionFind {
  constructor() {
    this.parent = new Map();
  }

  find(v) {
    if (!this.parent.has(v)) return v;
    const p = this.parent.get(v);
    if (Store.tagId(p) !== _MV_TAG) return p;
    const root = this.find(p);
    if (root !== p) this.parent.set(v, root);
    return root;
  }

  union(v, term) {
    const rv = this.find(v);
    this.parent.set(rv, term);
  }

  toTheta() {
    const theta = [];
    const processed = new Set();
    for (const [v] of this.parent) {
      if (processed.has(v)) continue;
      const root = this.find(v);
      if (root !== v) theta.push([v, root]);
      processed.add(v);
    }
    return theta;
  }
}

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
 * Unify two terms using union-find.
 * Cross-tag matching dispatches through registered equational theories.
 * arrlit ↔ acons/ae stays inline (Store normalization constraint).
 */
const unifyUF = (a, b, opts = {}) => {
  const deferOccursCheck = opts.deferOccursCheck || false;
  const uf = new UnionFind();
  const G = [[a, b]];
  const deferredChecks = [];

  while (G.length) {
    const [t0raw, t1raw] = G.pop();
    const t0 = uf.find(t0raw);
    const t1 = uf.find(t1raw);

    if (t0 === t1) continue;

    if (isMetavar(t0)) {
      if (deferOccursCheck) deferredChecks.push([t0, t1]);
      else if (occursInUF(t0, t1, uf)) return null;
      uf.union(t0, t1);
      continue;
    }

    if (isMetavar(t1)) { G.push([t1, t0]); continue; }

    if (isFreevar(t0) && isFreevar(t1)) {
      if (getVarName(t0) !== getVarName(t1)) return null;
      continue;
    }

    const tid0 = Store.tagId(t0);
    const tid1 = Store.tagId(t1);

    // arrlit: inline (Store normalization prevents rewrite API)
    if (tid0 === TAG_ARRLIT || tid1 === TAG_ARRLIT) {
      if (tid0 === TAG_ARRLIT && tid1 === TAG_ARRLIT) {
        const e0 = Store.getArrayElements(t0);
        const e1 = Store.getArrayElements(t1);
        if (e0.length !== e1.length) return null;
        for (let i = 0; i < e0.length; i++) G.push([e0[i], e1[i]]);
        continue;
      }
      const [pat, arr] = tid0 === TAG_ARRLIT ? [t1, t0] : [t0, t1];
      if (!unifyArrlit(pat, arr, G)) return null;
      continue;
    }

    // charlit: children are charCodes (numbers), not term hashes — compare directly
    if (tid0 === TAG_CHARLIT && tid1 === TAG_CHARLIT) {
      if (Store.child(t0, 0) !== Store.child(t1, 0)) return null;
      continue;
    }

    // Same tag + arity → generic decompose
    if (tid0 === tid1) {
      const arity0 = Store.arity(t0);
      if (arity0 !== Store.arity(t1)) return null;
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

    // Different tags → try equational theories (O(1) lookup)
    let handled = false;
    const th0 = _rewriteFromTag[tid0];
    if (th0) {
      const r = th0.rewrite(tid0, t0, tid1, Store.arity(t1));
      if (r !== null) { G.push([r, t1]); handled = true; }
    }
    if (!handled) {
      const th1 = _rewriteFromTag[tid1];
      if (th1) {
        const r = th1.rewrite(tid1, t1, tid0, Store.arity(t0));
        if (r !== null) { G.push([t0, r]); handled = true; }
      }
    }
    if (handled) continue;

    return null;
  }

  if (deferOccursCheck) {
    for (const [v, term] of deferredChecks) {
      if (occursInUF(v, term, uf)) return null;
    }
  }

  return uf.toTheta();
};

const unify = (a, b) => unifyUF(a, b, { deferOccursCheck: false });

// ============================================================================
// ONE-WAY MATCH (non-indexed, pair-based theta)
// ============================================================================

// Module-level flat worklist (match is iterative and non-reentrant on hot path).
//
// WARNING — NON-REENTRANT: _Gp/_Gt are shared mutable state. match() must NEVER
// be called from within another match() call. This is safe because:
//   1. match() is purely iterative (worklist loop, no recursion)
//   2. match() only calls Store read functions and Store.put (no callbacks)
//   3. The backward prover uses unify() (separate code path), not match()
//   4. Forward chaining is single-threaded with no async boundaries
let _Gp = new Array(64);
let _Gt = new Array(64);

/**
 * One-way matching: pattern matches term.
 * Cross-tag matching dispatches through registered equational theories.
 * arrlit stays inline (Store normalization).
 */
const match = (pattern, term, initialTheta = []) => {
  _Gp[0] = pattern; _Gt[0] = term;
  let gLen = 1;
  let theta = initialTheta;

  while (gLen > 0) {
    gLen--;
    const p = _Gp[gLen], t = _Gt[gLen];

    if (p === t) continue;

    // Pattern is a metavar — bind it
    if (isMetavar(p)) {
      let existingVal = undefined;
      for (let ti = 0; ti < theta.length; ti++) {
        if (theta[ti][0] === p) { existingVal = theta[ti][1]; break; }
      }
      if (existingVal !== undefined && existingVal !== t) return null;
      if (existingVal === undefined) { theta.push([p, t]); }
      continue;
    }

    const tpId = Store.tagId(p);
    const ttId = Store.tagId(t);

    // arrlit: inline (Store normalization prevents rewrite API)
    if (ttId === TAG_ARRLIT) {
      if (tpId === TAG_ARRLIT) {
        // arrlit vs arrlit: element-wise matching
        const ep = Store.getArrayElements(p);
        const et = Store.getArrayElements(t);
        if (ep.length !== et.length) return null;
        if (gLen + ep.length > _Gp.length) {
          const newSize = Math.max(_Gp.length * 2, gLen + ep.length);
          const ngp = new Array(newSize); const ngt = new Array(newSize);
          for (let j = 0; j < gLen; j++) { ngp[j] = _Gp[j]; ngt[j] = _Gt[j]; }
          _Gp = ngp; _Gt = ngt;
        }
        for (let i = 0; i < ep.length; i++) {
          _Gp[gLen] = ep[i]; _Gt[gLen] = et[i]; gLen++;
        }
        continue;
      }
      // Cross-tag: acons/ae decomposition (inline, Store structural concern)
      const elems = Store.getArrayElements(t);
      if (tpId === TAG.atom && Store.child(p, 0) === 'ae') {
        if (elems.length !== 0) return null;
        continue;
      }
      if (tpId === TAG_ACONS && Store.arity(p) === 2) {
        if (elems.length === 0) return null;
        const tailData = new Uint32Array(elems.length - 1);
        for (let i = 1; i < elems.length; i++) tailData[i - 1] = elems[i];
        _Gp[gLen] = Store.child(p, 0); _Gt[gLen] = elems[0]; gLen++;
        _Gp[gLen] = Store.child(p, 1); _Gt[gLen] = Store.put('arrlit', [tailData]); gLen++;
        continue;
      }
      return null;
    }

    // charlit: children are charCodes (numbers), not term hashes — compare directly
    if (tpId === TAG_CHARLIT && ttId === TAG_CHARLIT) {
      if (Store.child(p, 0) !== Store.child(t, 0)) return null;
      continue;
    }

    // Same tag + arity → generic decompose
    if (tpId === ttId) {
      const ap = Store.arity(p);
      if (ap !== Store.arity(t)) return null;
      if (gLen + ap > _Gp.length) {
        const newSize = _Gp.length * 2;
        const ngp = new Array(newSize); const ngt = new Array(newSize);
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

    // Different tags → equational theory dispatch (O(1) lookup)
    let handled = false;
    const thT = _rewriteFromTag[ttId];
    if (thT) {
      const r = thT.rewrite(ttId, t, tpId, Store.arity(p));
      if (r !== null) { _Gp[gLen] = p; _Gt[gLen] = r; gLen++; handled = true; }
    }
    if (!handled) {
      const thP = _rewriteFromTag[tpId];
      if (thP) {
        const r = thP.rewrite(tpId, p, ttId, Store.arity(t));
        if (r !== null) { _Gp[gLen] = r; _Gt[gLen] = t; gLen++; handled = true; }
      }
    }
    if (handled) continue;

    return null;
  }

  return theta;
};

// ============================================================================
// INDEXED MATCH — Stage 6 de Bruijn theta (O(1) metavar lookup)
// ============================================================================

// Fixed-capacity undo stack. Tracks theta slots written by matchIndexed
// for O(k) rollback. 128 slots covers max observed depth (~32 per rule,
// nested save/restore during interleaved matching).
const UNDO_CAPACITY = 128;
let _undoStack = new Uint8Array(UNDO_CAPACITY);
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
 * Cross-tag matching dispatches through registered equational theories
 * via O(1) _rewriteFromTag[tagId] lookup. arrlit stays inline.
 */
const matchIndexed = (pattern, term, theta, slots) => {
  _Gp[0] = pattern; _Gt[0] = term;
  let gLen = 1;

  while (gLen > 0) {
    gLen--;
    const p = _Gp[gLen], t = _Gt[gLen];

    if (p === t) continue;

    // Pattern is a metavar — O(1) indexed lookup via slots map
    const slot = slots[p];
    if (slot !== undefined) {
      const existing = theta[slot];
      if (existing !== undefined) {
        if (existing !== t) {
          // Push for structural comparison (handles binlit vs structural binary)
          _Gp[gLen] = existing; _Gt[gLen] = t; gLen++;
        }
      } else {
        theta[slot] = t;
        if (_undoLen >= UNDO_CAPACITY) {
          throw new Error(`matchIndexed: undo stack overflow (capacity=${UNDO_CAPACITY})`);
        }
        _undoStack[_undoLen++] = slot;
      }
      continue;
    }

    const tpId = Store.tagId(p);
    const ttId = Store.tagId(t);

    // arrlit: inline (Store normalization prevents rewrite API)
    // Checked before same-tag because arrlit children are in Uint32Array,
    // not accessible via Store.child (generic decompose won't work).
    if (ttId === TAG_ARRLIT) {
      if (tpId === TAG_ARRLIT) {
        // arrlit vs arrlit: element-wise matching
        const ep = Store.getArrayElements(p);
        const et = Store.getArrayElements(t);
        if (ep.length !== et.length) return false;
        for (let i = 0; i < ep.length; i++) {
          _Gp[gLen] = ep[i]; _Gt[gLen] = et[i]; gLen++;
        }
        continue;
      }
      // Cross-tag: acons/ae decomposition
      const elems = Store.getArrayElements(t);
      if (tpId === TAG.atom && Store.child(p, 0) === 'ae') {
        if (elems.length !== 0) return false;
        continue;
      }
      if (tpId === TAG_ACONS && Store.arity(p) === 2) {
        if (elems.length === 0) return false;
        const tailData = new Uint32Array(elems.length - 1);
        for (let i = 1; i < elems.length; i++) tailData[i - 1] = elems[i];
        _Gp[gLen] = Store.child(p, 0); _Gt[gLen] = elems[0]; gLen++;
        _Gp[gLen] = Store.child(p, 1); _Gt[gLen] = Store.put('arrlit', [tailData]); gLen++;
        continue;
      }
      return false;
    }

    // charlit: children are charCodes (numbers), not term hashes — compare directly
    if (tpId === TAG_CHARLIT && ttId === TAG_CHARLIT) {
      if (Store.child(p, 0) !== Store.child(t, 0)) return false;
      continue;
    }

    // Same tag + arity → generic decompose (numeric comparison, no string alloc)
    if (tpId === ttId) {
      const ap = Store.arity(p);
      if (ap !== Store.arity(t)) return false;
      if (gLen + ap > _Gp.length) {
        const newSize = _Gp.length * 2;
        const ngp = new Array(newSize); const ngt = new Array(newSize);
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

    // Different tags → equational theory dispatch (O(1) lookup)
    // Replaces hardcoded binlit/strlit branches.
    const thT = _rewriteFromTag[ttId];
    if (thT) {
      const r = thT.rewrite(ttId, t, tpId, Store.arity(p));
      if (r !== null) { _Gp[gLen] = p; _Gt[gLen] = r; gLen++; continue; }
    }
    const thP = _rewriteFromTag[tpId];
    if (thP) {
      const r = thP.rewrite(tpId, p, ttId, Store.arity(t));
      if (r !== null) { _Gp[gLen] = r; _Gt[gLen] = t; gLen++; continue; }
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
  isMetavar,
  setTheories,
};
