/**
 * Backchainer — slot-indexed theta, trail backtracking
 *
 * Calculus-agnostic backward chaining with first-argument indexing.
 * ILL-specific behavior (normalization, proof terms, FFI, equational normalization)
 * injected via opts; defaults from backchain-ill.js.
 *
 * Core invariant: zero allocation in the search loop.
 * Variables are slot indices into a flat array, not Store hashes.
 * Trail-based backtracking: undo() restores theta in O(delta).
 *
 * Zig-friendly: all hot-path data lives in typed arrays / flat arrays.
 * Class-based: Backchainer encapsulates all mutable state for
 * reentrant use and clean Zig struct translation.
 */

const Store = require('../kernel/store');
const { isPredTag, predHead: getHead } = require('../kernel/ast');
const { collectMetavars } = require('./pattern-utils');
const {
  compilePM, PM_BIND, PM_GROUND, PM_COMPOUND, _skipInstruction,
  compilePut, compileKey,
  PUT_GROUND, PUT_SLOT, PUT_COMPOUND, PUT_ARRLIT,
} = require('./compile');
const { buildTheoryLookup, defaultTheories: _defaultTheories } = require('../kernel/eq-theory');

// ============================================================================
// SHARED CONSTANTS
// ============================================================================

const _MV_TAG_ID = Store.TAG.metavar;
const _LEAF_TAGS = new Uint8Array(256);
_LEAF_TAGS[Store.TAG.atom] = 1;
_LEAF_TAGS[Store.TAG.binlit] = 1;
_LEAF_TAGS[Store.TAG.strlit] = 1;
_LEAF_TAGS[Store.TAG.charlit] = 1;
_LEAF_TAGS[Store.TAG.freevar] = 1;
_LEAF_TAGS[Store.TAG.evar] = 1;
const _ARRLIT_TAG = Store.TAG.arrlit;
const _ACONS_TAG = Store.TAG.acons;

const MAX_SLOTS = 32768;
const MAX_TRAIL = 32768;

// _search state machine phases
const _PH_INIT = 0;
const _PH_SELECT = 1;
const _PH_PREMISE = 2;
const _PH_RESUME = 3;

const _INITIAL_SEARCH_CAP = 512;

// Sentinel for rebuild markers on the _resolveSlots work stack.
const _REBUILD = {};
// Maximum iterations for _resolveSlots to prevent runaway resolution.
const _MAX_RESOLVE_ITER = 500_000;

// ============================================================================
// INDEXING — two-level: predicate head → first-arg constructor → [items]
// ============================================================================

/** Get first argument's outermost constructor for indexing. O(1). */
function getFirstArgHead(hash) {
  if (!Store.isTerm(hash)) return null;
  const t = Store.tag(hash);
  if (!t || !isPredTag(t) || Store.arity(hash) === 0) return null;
  const firstArg = Store.child(hash, 0);
  if (!Store.isTerm(firstArg)) return null;
  const argTag = Store.tag(firstArg);
  if (argTag === 'atom') return Store.child(firstArg, 0);
  if (argTag === 'freevar' || argTag === 'metavar') return '_';
  if (isPredTag(argTag)) return argTag;
  if (argTag === 'binlit') {
    const v = Store.child(firstArg, 0);
    if (v === 0n) return 'e';
    return v % 2n === 1n ? 'i' : 'o';
  }
  return null;
}

// In-memory buildIndex cache. Survives Store.restore() (hash identity preserved),
// cleared on Store.clear() (hashes invalidated).
const _indexCache = new Map();
Store.onClear(() => _indexCache.clear());

function _indexCacheKey(clauses, definitions) {
  let h = 0;
  if (clauses) for (const [, cl] of clauses) h = (h * 31 + cl.hash) | 0;
  if (definitions) for (const [, dh] of definitions) h = (h * 31 + dh) | 0;
  return h;
}

/**
 * Build two-level index with compiled clause heads.
 * Each clause gets: compiledHead (instructions), localSlots ({metavarHash: localIdx}),
 * metavarCount, metavarList ([{hash, localSlot}]).
 */
function buildIndex(clauses, definitions) {
  const key = _indexCacheKey(clauses, definitions);
  const cached = _indexCache.get(key);
  if (cached) return cached;

  const idx = { types: {}, clauses: {} };

  for (const [name, hash] of definitions) {
    const head = getHead(hash);
    if (!head) continue;
    const mvSet = new Set();
    collectMetavars(hash, mvSet);
    const localSlots = {};
    const metavarList = [];
    let si = 0;
    for (const mv of mvSet) {
      localSlots[mv] = si;
      metavarList.push({ hash: mv, localSlot: si });
      si++;
    }
    const compiled = {
      hash, localSlots, metavarCount: si, metavarList,
      compiledHead: compilePM(hash, localSlots),
    };
    const fa = getFirstArgHead(hash) || '_';
    (idx.types[head] ||= {})[fa] ||= [];
    idx.types[head][fa].push([name, compiled]);
  }

  for (const [name, clause] of clauses) {
    const head = getHead(clause.hash);
    if (!head) continue;
    const mvSet = new Set();
    collectMetavars(clause.hash, mvSet);
    for (const p of clause.premises) collectMetavars(p, mvSet);
    const localSlots = {};
    const metavarList = [];
    let si = 0;
    for (const mv of mvSet) {
      localSlots[mv] = si;
      metavarList.push({ hash: mv, localSlot: si });
      si++;
    }
    const compiled = {
      hash: clause.hash,
      premises: clause.premises,
      localSlots,
      metavarCount: si,
      metavarList,
      compiledHead: compilePM(clause.hash, localSlots),
      headPut: compilePut(clause.hash, localSlots),
      premisePuts: clause.premises.map(p => compilePut(p, localSlots)),
      premiseKeys: clause.premises.map(p => compileKey(p, localSlots)),
    };
    const fa = getFirstArgHead(clause.hash) || '_';
    (idx.clauses[head] ||= {})[fa] ||= [];
    idx.clauses[head][fa].push([name, compiled]);
  }

  _indexCache.set(key, idx);
  return idx;
}

/** Get candidate types and clauses for a goal. O(1). */
function getCandidates(idx, goalHash, allBuckets) {
  const head = getHead(goalHash);
  if (!head) return { types: [], clauses: [] };
  const fa = getFirstArgHead(goalHash) || '_';
  const ti = idx.types[head] || {};
  const ci = idx.clauses[head] || {};

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
// Backchainer CLASS
// ============================================================================

class Backchainer {
  constructor() {
    // Slot machinery — flat theta array, trail-based backtracking
    this._theta = new Array(MAX_SLOTS);
    this._trail = new Uint32Array(MAX_TRAIL);
    this._trailLen = 0;
    this._nextBase = 0;

    // Slot metavar cache: maps global slot index ↔ unique metavar Store hash.
    this._slotMV = [];
    this._mvSlotsLen = 4_000_000;
    this._mvSlots = new Uint32Array(this._mvSlotsLen);
    this._queryMVCleanup = [];

    // Pre-allocated stacks (non-reentrant)
    this._mStack = new Array(128);
    this._putStack = new Array(64);

    // Chase results (avoids per-call allocation)
    this._chaseValue = undefined;
    this._chaseFinalSlot = 0;

    // Pre-allocated search stack for iterative _search.
    // depth is explicit (not sp-derived) to support tail-premise optimization.
    this._searchStack = new Array(_INITIAL_SEARCH_CAP);
    for (let i = 0; i < _INITIAL_SEARCH_CAP; i++) {
      this._searchStack[i] = {
        goalHash: 0, phase: 0, depth: 0, clauseIdx: 0, premIdx: 0,
        candClauses: null, clauseBase: 0, savedTrail: 0, savedBase: 0,
        premTerms: null,
      };
    }
    this._searchStackCap = _INITIAL_SEARCH_CAP;

    // Per-prove() call state (set at entry)
    this._theoryLookup = {};
    this._maxDepth = 100;
    this._trace = null;
    this._idx = null;
    this._buildTerm = false;
    this._allBuckets = false;
    this._normalize = null;
    this._buildClauseTermFn = null;
    this._buildFFITermFn = null;
    this._buildTypeTermFn = null;
    this._tryFFIFn = null;
  }

  // ── Slot machinery ──────────────────────────────────────────────────

  _ensureMVSlots(id) {
    if (id < this._mvSlotsLen) return;
    const newLen = Math.max(this._mvSlotsLen * 2, id + 1);
    const newArr = new Uint32Array(newLen);
    newArr.set(this._mvSlots);
    this._mvSlots = newArr;
    this._mvSlotsLen = newLen;
  }

  _getSlotMV(slot) {
    if (slot < this._slotMV.length) return this._slotMV[slot];
    while (this._slotMV.length <= slot) {
      const i = this._slotMV.length;
      const h = Store.put('metavar', ['_s' + i]);
      this._slotMV.push(h);
      this._ensureMVSlots(h);
      this._mvSlots[h] = i + 1;
    }
    return this._slotMV[slot];
  }

  _reserveFrame(n) {
    const base = this._nextBase;
    this._nextBase += n;
    return base;
  }

  _bind(slot, value) {
    const theta = this._theta, trail = this._trail;
    theta[slot] = value;
    trail[this._trailLen++] = slot;
  }

  _undo(savedTrail, savedBase) {
    const theta = this._theta, trail = this._trail;
    let tl = this._trailLen;
    while (tl > savedTrail) theta[trail[--tl]] = undefined;
    this._trailLen = tl;
    this._nextBase = savedBase;
  }

  // ── Chase ───────────────────────────────────────────────────────────

  /**
   * Chase a slot metavar chain to its ultimate value or final unbound slot.
   * Results in this._chaseValue / this._chaseFinalSlot.
   */
  _chaseSlot(startSlot) {
    const theta = this._theta, mvSlots = this._mvSlots, mvSlotsLen = this._mvSlotsLen;
    let slot = startSlot;
    for (let hops = 0; hops < 32; hops++) {
      const val = theta[slot];
      if (val === undefined) { this._chaseValue = undefined; this._chaseFinalSlot = slot; return; }
      const ns = val < mvSlotsLen ? mvSlots[val] - 1 : -1;
      if (ns < 0) { this._chaseValue = val; this._chaseFinalSlot = slot; return; }
      slot = ns;
    }
    this._chaseValue = undefined; this._chaseFinalSlot = slot;
  }

  // ── Ground matching ─────────────────────────────────────────────────

  _groundMatch(expected, goalH) {
    if (expected === goalH) return true;
    if (!Store.isTerm(expected) || !Store.isTerm(goalH)) return false;

    const mvSlots = this._mvSlots, mvSlotsLen = this._mvSlotsLen;
    const gTid = Store.tagId(goalH);

    if (gTid === _MV_TAG_ID) {
      const gs = goalH < mvSlotsLen ? mvSlots[goalH] - 1 : -1;
      if (gs >= 0) {
        this._chaseSlot(gs);
        if (this._chaseValue !== undefined) return this._groundMatch(expected, this._chaseValue);
        this._bind(this._chaseFinalSlot, expected);
        return true;
      }
      return false;
    }

    const eTid = Store.tagId(expected);
    if (eTid === _MV_TAG_ID) {
      const eSlot = expected < mvSlotsLen ? mvSlots[expected] - 1 : -1;
      if (eSlot >= 0) {
        this._chaseSlot(eSlot);
        if (this._chaseValue !== undefined) return this._groundMatch(this._chaseValue, goalH);
        this._bind(this._chaseFinalSlot, goalH);
        return true;
      }
      return false;
    }

    if (eTid !== gTid) {
      if (gTid === _ARRLIT_TAG) {
        const gElems = Store.getArrayElements(goalH);
        if (eTid === Store.TAG.atom && Store.child(expected, 0) === 'ae')
          return gElems.length === 0;
        if (eTid === _ACONS_TAG && Store.arity(expected) === 2) {
          if (gElems.length === 0) return false;
          if (!this._groundMatch(Store.child(expected, 0), gElems[0])) return false;
          const tailData = new Uint32Array(gElems.length - 1);
          for (let i = 1; i < gElems.length; i++) tailData[i - 1] = gElems[i];
          return this._groundMatch(Store.child(expected, 1), Store.put('arrlit', [tailData]));
        }
      }
      if (eTid === _ARRLIT_TAG) {
        const eElems = Store.getArrayElements(expected);
        if (gTid === Store.TAG.atom && Store.child(goalH, 0) === 'ae')
          return eElems.length === 0;
        if (gTid === _ACONS_TAG && Store.arity(goalH) === 2) {
          if (eElems.length === 0) return false;
          if (!this._groundMatch(eElems[0], Store.child(goalH, 0))) return false;
          const tailData = new Uint32Array(eElems.length - 1);
          for (let i = 1; i < eElems.length; i++) tailData[i - 1] = eElems[i];
          return this._groundMatch(Store.put('arrlit', [tailData]), Store.child(goalH, 1));
        }
      }
      // Equational theory dispatch (O(1) lookup)
      const thG = this._theoryLookup[gTid];
      if (thG) {
        const rGoal = thG.rewrite(gTid, goalH, eTid, Store.arity(expected));
        if (rGoal !== null) return this._groundMatch(expected, rGoal);
      }
      const thE = this._theoryLookup[eTid];
      if (thE) {
        const rExp = thE.rewrite(eTid, expected, gTid, Store.arity(goalH));
        if (rExp !== null) return this._groundMatch(rExp, goalH);
      }
      return false;
    }

    if (eTid === _ARRLIT_TAG) {
      const eElems = Store.getArrayElements(expected);
      const gElems = Store.getArrayElements(goalH);
      if (eElems.length !== gElems.length) return false;
      for (let i = 0; i < eElems.length; i++) {
        if (!this._groundMatch(eElems[i], gElems[i])) return false;
      }
      return true;
    }
    const eArity = Store.arity(expected);
    if (eArity !== Store.arity(goalH)) return false;
    for (let i = 0; i < eArity; i++) {
      const ec = Store.child(expected, i);
      const gc = Store.child(goalH, i);
      if (Store.isTermChild(ec) && Store.isTermChild(gc)) {
        if (!this._groundMatch(ec, gc)) return false;
      } else if (ec !== gc) {
        return false;
      }
    }
    return true;
  }

  // ── Clause head matching ────────────────────────────────────────────

  _matchHead(insts, goalHash, base) {
    const theta = this._theta, mvSlots = this._mvSlots, mvSlotsLen = this._mvSlotsLen;
    const mStack = this._mStack;
    const theoryLookup = this._theoryLookup;
    let sp = 0;
    mStack[sp++] = 0;
    mStack[sp++] = goalHash;

    while (sp > 0) {
      const h = mStack[--sp];
      const ip = mStack[--sp];
      const inst = insts[ip];

      let resolved = h;
      let goalSlot = -1;
      const gs = h < mvSlotsLen ? mvSlots[h] - 1 : -1;
      if (gs >= 0) {
        this._chaseSlot(gs);
        if (this._chaseValue !== undefined) {
          resolved = this._chaseValue;
        } else {
          goalSlot = this._chaseFinalSlot;
          switch (inst.op) {
            case PM_BIND: {
              const cSlot = base + inst.slot;
              const existing = theta[cSlot];
              if (existing !== undefined) {
                this._bind(goalSlot, existing);
              } else {
                this._bind(goalSlot, this._getSlotMV(cSlot));
                this._bind(cSlot, this._getSlotMV(goalSlot));
              }
              continue;
            }
            case PM_GROUND:
              this._bind(goalSlot, inst.expected);
              continue;
            case PM_COMPOUND: {
              const mat = this._materialize(insts, ip, base);
              this._bind(goalSlot, mat);
              continue;
            }
          }
        }
      }

      switch (inst.op) {
        case PM_BIND: {
          const slot = base + inst.slot;
          const existing = theta[slot];
          if (existing !== undefined) {
            if (existing !== resolved && !this._groundMatch(existing, resolved)) return false;
          } else {
            this._bind(slot, resolved);
          }
          break;
        }
        case PM_GROUND:
          if (resolved !== inst.expected) {
            if (!this._groundMatch(inst.expected, resolved)) return false;
          }
          break;
        case PM_COMPOUND: {
          const tid = Store.tagId(resolved);
          if (tid !== inst.tagId || Store.arity(resolved) !== inst.arity) {
            // arrlit → acons: inline (Store normalizes acons(H,arrlit(T)) → arrlit)
            if (tid === _ARRLIT_TAG && inst.tagId === _ACONS_TAG && inst.arity === 2) {
              const elems = Store.getArrayElements(resolved);
              if (!elems || elems.length === 0) return false;
              const tailData = new Uint32Array(elems.length - 1);
              for (let i = 1; i < elems.length; i++) tailData[i - 1] = elems[i];
              const tailHash = Store.put('arrlit', [tailData]);
              let childIp2 = ip + 1;
              const child1Ip = _skipInstruction(insts, childIp2);
              mStack[sp++] = child1Ip;
              mStack[sp++] = tailHash;
              mStack[sp++] = childIp2;
              mStack[sp++] = elems[0];
              break;
            }
            // Equational theory dispatch (O(1) lookup)
            const th = theoryLookup[tid];
            if (th) {
              const rewritten = th.rewrite(tid, resolved, inst.tagId, inst.arity);
              if (rewritten !== null) { resolved = rewritten; }
              else return false;
            } else {
              return false;
            }
          }
          let childIp = ip + 1;
          for (let ci = inst.arity - 1; ci >= 0; ci--) {
            let skipIp = childIp;
            for (let s = 0; s < ci; s++) skipIp = _skipInstruction(insts, skipIp);
            mStack[sp++] = skipIp;
            mStack[sp++] = Store.child(resolved, ci);
          }
          break;
        }
      }
    }
    return true;
  }

  _materialize(insts, ip, base) {
    const inst = insts[ip];
    switch (inst.op) {
      case PM_GROUND: return inst.expected;
      case PM_BIND: {
        const slot = base + inst.slot;
        const val = this._theta[slot]; // single access, not in a loop
        return val !== undefined ? val : this._getSlotMV(slot);
      }
      case PM_COMPOUND: {
        const children = [];
        let childIp = ip + 1;
        for (let i = 0; i < inst.arity; i++) {
          children.push(this._materialize(insts, childIp, base));
          childIp = _skipInstruction(insts, childIp);
        }
        return Store.put(Store.TAG_NAMES[inst.tagId], children);
      }
    }
    return 0;
  }

  // ── Compiled premise execution ──────────────────────────────────────

  _executePut(insts, base) {
    const theta = this._theta, putStack = this._putStack;
    let sp = 0;
    for (let ip = 0; ip < insts.length; ip++) {
      const inst = insts[ip];
      switch (inst.op) {
        case PUT_GROUND:
          putStack[sp++] = inst.hash;
          break;
        case PUT_SLOT: {
          const val = theta[base + inst.slot];
          putStack[sp++] = val !== undefined ? val : this._getSlotMV(base + inst.slot);
          break;
        }
        case PUT_COMPOUND: {
          const children = new Array(inst.arity);
          sp -= inst.arity;
          for (let i = 0; i < inst.arity; i++) children[i] = putStack[sp + i];
          putStack[sp++] = Store.put(inst.tagName, children);
          break;
        }
        case PUT_ARRLIT: {
          const elems = new Uint32Array(inst.count);
          sp -= inst.count;
          for (let i = 0; i < inst.count; i++) elems[i] = putStack[sp + i];
          putStack[sp++] = Store.putArray(elems);
          break;
        }
      }
    }
    return putStack[0];
  }

  // ── Resolution ──────────────────────────────────────────────────────

  /**
   * Resolve all slot metavars in a Store hash to their bound values.
   * Iterative implementation to avoid stack overflow on deeply nested terms
   * (e.g., 1000+ deep acons chains from arrlit decomposition).
   */
  _resolveSlots(root) {
    const mvSlots = this._mvSlots, mvSlotsLen = this._mvSlotsLen;
    // Quick path: resolve a single metavar chase
    let h = root;
    if (Store.isTerm(h) && Store.tagId(h) === _MV_TAG_ID) {
      const slot = h < mvSlotsLen ? mvSlots[h] - 1 : -1;
      if (slot >= 0) {
        this._chaseSlot(slot);
        if (this._chaseValue !== undefined) h = this._chaseValue;
        else return h;
      } else return h;
    }
    if (!Store.isTerm(h)) return h;
    const tid0 = Store.tagId(h);
    if (_LEAF_TAGS[tid0]) return h;
    if (tid0 === _ARRLIT_TAG) {
      const elems = Store.getArrayElements(h);
      if (!elems || elems.length === 0) return h;
    }
    if (Store.arity(h) === 0 && tid0 !== _ARRLIT_TAG) return h;

    // Full iterative post-order traversal.
    const work = [];
    const results = [];
    work.push(h);
    let iter = 0;

    while (work.length > 0) {
      if (++iter > _MAX_RESOLVE_ITER) return root;
      const item = work.pop();

      if (Array.isArray(item)) {
        const origH = item[1];
        const tag = item[2];
        const n = item[3];
        const tid = Store.tagId(origH);

        if (tid === _ARRLIT_TAG) {
          const elems = Store.getArrayElements(origH);
          let changed = false;
          const newElems = new Uint32Array(n);
          for (let i = n - 1; i >= 0; i--) {
            const r = results.pop();
            newElems[i] = r;
            if (r !== elems[i]) changed = true;
          }
          results.push(changed ? Store.putArray(newElems) : origH);
        } else {
          let changed = false;
          const nc = new Array(n);
          for (let i = n - 1; i >= 0; i--) {
            const r = results.pop();
            nc[i] = r;
            if (r !== Store.child(origH, i)) changed = true;
          }
          results.push(changed ? Store.put(tag, nc) : origH);
        }
        continue;
      }

      let ph = item;
      if (Store.isTerm(ph) && Store.tagId(ph) === _MV_TAG_ID) {
        const slot = ph < mvSlotsLen ? mvSlots[ph] - 1 : -1;
        if (slot >= 0) {
          this._chaseSlot(slot);
          if (this._chaseValue !== undefined) ph = this._chaseValue;
          else { results.push(ph); continue; }
        } else { results.push(ph); continue; }
      }

      if (!Store.isTerm(ph)) { results.push(ph); continue; }

      const tid = Store.tagId(ph);
      if (_LEAF_TAGS[tid]) { results.push(ph); continue; }

      if (tid === _ARRLIT_TAG) {
        const elems = Store.getArrayElements(ph);
        if (!elems || elems.length === 0) { results.push(ph); continue; }
        work.push([_REBUILD, ph, null, elems.length]);
        for (let i = elems.length - 1; i >= 0; i--) work.push(elems[i]);
        continue;
      }

      const a = Store.arity(ph);
      if (a === 0) { results.push(ph); continue; }

      work.push([_REBUILD, ph, Store.tag(ph), a]);
      for (let i = a - 1; i >= 0; i--) work.push(Store.child(ph, i));
    }

    return results.length > 0 ? results[0] : root;
  }

  // ── Search (iterative state-machine) ────────────────────────────────

  _growSearchStack() {
    const newCap = this._searchStackCap * 2;
    while (this._searchStack.length < newCap) {
      this._searchStack.push({
        goalHash: 0, phase: 0, depth: 0, clauseIdx: 0, premIdx: 0,
        candClauses: null, clauseBase: 0, savedTrail: 0, savedBase: 0,
        premTerms: null,
      });
    }
    this._searchStackCap = newCap;
  }

  /**
   * Iterative backward search — state-machine over explicit frame stack.
   *
   * Optimizations:
   * - Committed-choice: when cc.length === 1, premise failure immediately
   *   fails the goal (no undo, no clause iteration — parent handles undo).
   * - Tail-premise: for committed + last premise + !buildTerm, the frame
   *   is reused instead of pushing a child. Turns O(depth) stack into O(1)
   *   for linear-recursive deterministic predicates (e.g. inc, length, not).
   */
  _search(initialGoal, initialDepth) {
    const maxDepth = this._maxDepth, tryFFIFn = this._tryFFIFn;
    const idx = this._idx, allBuckets = this._allBuckets;
    const buildTerm = this._buildTerm, trace = this._trace;
    const theta = this._theta, mvSlots = this._mvSlots, mvSlotsLen = this._mvSlotsLen;
    const normalize = this._normalize, buildClauseTermFn = this._buildClauseTermFn;
    const buildFFITermFn = this._buildFFITermFn, buildTypeTermFn = this._buildTypeTermFn;

    const stack = this._searchStack;
    let sp = 0;
    let childResult = undefined;

    // Initialize first frame
    stack[0].goalHash = initialGoal;
    stack[0].depth = initialDepth;
    stack[0].phase = _PH_INIT;
    sp = 1;

    outer: while (sp > 0) {
      const frame = stack[sp - 1];

      switch (frame.phase) {
        case _PH_INIT: {
          if (frame.depth > maxDepth) { sp--; childResult = null; continue outer; }

          // FFI attempt
          if (tryFFIFn) {
            const ffiResult = tryFFIFn(frame.goalHash);
            if (ffiResult && ffiResult.success) {
              let ffiOk = true;
              if (ffiResult.theta) {
                for (const [varHash, val] of ffiResult.theta) {
                  const slot = varHash < mvSlotsLen ? mvSlots[varHash] - 1 : -1;
                  if (slot >= 0 && theta[slot] === undefined) {
                    this._bind(slot, val);
                  } else if (slot >= 0 && theta[slot] !== val) {
                    // Already bound to a different value — mismatch
                    ffiOk = false; break;
                  } else if (slot < 0 && varHash !== val) {
                    // Ground literal in output position — verify match
                    ffiOk = false; break;
                  }
                }
              }
              if (ffiOk) {
                if (trace) trace.push(`${'  '.repeat(frame.depth)}FFI: ${getHead(frame.goalHash)} ✓`);
                sp--; childResult = { term: buildTerm ? buildFFITermFn(frame.goalHash) : null }; continue outer;
              }
              // FFI value mismatch — fall through to clause resolution
            }
          }

          // Get candidates (single call — types consumed inline, clauses stored)
          const { types: candTypes, clauses: candClauses } = getCandidates(idx, frame.goalHash, allBuckets);

          if (trace) trace.push(`${'  '.repeat(frame.depth)}Goal: ${formatTerm(frame.goalHash)} [${candTypes.length}t/${candClauses.length}c]`);

          // Types loop — no child frames needed
          for (let ti = 0; ti < candTypes.length; ti++) {
            const [name, compiled] = candTypes[ti];
            const savedTrail = this._trailLen;
            const savedBase = this._nextBase;
            const typeBase = this._reserveFrame(compiled.metavarCount);

            if (this._matchHead(compiled.compiledHead, frame.goalHash, typeBase)) {
              if (trace) trace.push(`${'  '.repeat(frame.depth)}  ✓ ${name}`);
              if (buildTerm) {
                const groundGoal = normalize(this._resolveSlots(frame.goalHash));
                sp--; childResult = { term: buildTypeTermFn(groundGoal, name) }; continue outer;
              }
              sp--; childResult = { term: null }; continue outer;
            }
            this._undo(savedTrail, savedBase);
          }

          frame.candClauses = candClauses;
          frame.clauseIdx = 0;
          frame.phase = _PH_SELECT;
          // FALL THROUGH
        }

        case _PH_SELECT: {
          const cc = frame.candClauses;
          while (frame.clauseIdx < cc.length) {
            const [name, compiled] = cc[frame.clauseIdx];
            frame.savedTrail = this._trailLen;
            frame.savedBase = this._nextBase;
            frame.clauseBase = this._reserveFrame(compiled.metavarCount);

            if (!this._matchHead(compiled.compiledHead, frame.goalHash, frame.clauseBase)) {
              this._undo(frame.savedTrail, frame.savedBase);
              frame.clauseIdx++;
              continue;
            }

            if (trace) trace.push(`${'  '.repeat(frame.depth)}  → ${name}`);

            if (compiled.premises.length === 0) {
              if (trace) trace.push(`${'  '.repeat(frame.depth)}  ✓ ${name}`);
              sp--;
              if (buildTerm) {
                const groundHead = normalize(this._resolveSlots(
                  this._executePut(compiled.headPut, frame.clauseBase)));
                const groundPrems = compiled.premisePuts.map(pp => normalize(this._resolveSlots(
                  this._executePut(pp, frame.clauseBase))));
                childResult = { term: buildClauseTermFn(groundPrems, [], groundHead, name) };
              } else {
                childResult = { term: null };
              }
              continue outer;
            }

            frame.premIdx = 0;
            if (buildTerm) frame.premTerms = [];
            frame.phase = _PH_PREMISE;
            continue outer;
          }
          // All clauses exhausted
          if (trace) trace.push(`${'  '.repeat(frame.depth)}  ✗`);
          sp--; childResult = null; continue outer;
        }

        case _PH_PREMISE: {
          const [cName, compiled] = frame.candClauses[frame.clauseIdx];
          if (frame.premIdx >= compiled.premises.length) {
            // All premises proved — clause succeeds
            if (trace) trace.push(`${'  '.repeat(frame.depth)}  ✓ ${cName}`);
            sp--;
            if (buildTerm) {
              const groundHead = normalize(this._resolveSlots(
                this._executePut(compiled.headPut, frame.clauseBase)));
              const groundPrems = compiled.premisePuts.map(pp => normalize(this._resolveSlots(
                this._executePut(pp, frame.clauseBase))));
              childResult = { term: buildClauseTermFn(groundPrems, frame.premTerms, groundHead, cName) };
            } else {
              childResult = { term: null };
            }
            continue outer;
          }
          const premGoal = this._executePut(compiled.premisePuts[frame.premIdx], frame.clauseBase);

          // Tail-premise: for committed clause (single candidate) at last premise
          // with no proof term, reuse this frame. Turns O(depth) → O(1) for
          // linear-recursive deterministic predicates (inc, length, not, etc).
          if (!buildTerm && frame.candClauses.length === 1
              && frame.premIdx === compiled.premises.length - 1) {
            frame.goalHash = premGoal;
            frame.depth++;
            frame.phase = _PH_INIT;
            continue outer;
          }

          frame.phase = _PH_RESUME;
          // Push child frame
          if (sp >= this._searchStackCap) this._growSearchStack();
          const child = stack[sp];
          child.goalHash = premGoal;
          child.depth = frame.depth + 1;
          child.phase = _PH_INIT;
          sp++;
          continue outer;
        }

        case _PH_RESUME: {
          if (childResult === null) {
            if (frame.candClauses.length === 1) {
              // Committed: single candidate, premise failed → goal fails.
              // Skip undo — parent's undo covers our bindings.
              sp--; childResult = null; continue outer;
            }
            // Non-committed: undo and try next clause
            this._undo(frame.savedTrail, frame.savedBase);
            frame.clauseIdx++;
            frame.phase = _PH_SELECT;
            continue outer;
          }
          if (buildTerm) frame.premTerms.push(childResult.term);
          frame.premIdx++;
          frame.phase = _PH_PREMISE;
          continue outer;
        }
      }
    }

    return childResult || null;
  }

  // ── Main entry point ────────────────────────────────────────────────

  /**
   * Backchain a goal using backward chaining with slot-indexed theta.
   *
   * @param {number} goal - Goal hash to prove
   * @param {Map} clauses - Map of name → { hash, premises }
   * @param {Map} definitions - Map of name → hash (axioms/facts)
   * @param {Object} opts
   *   - maxDepth {number} - Max search depth (default 100)
   *   - index {Object} - Pre-built index from buildIndex()
   *   - buildTerm {boolean} - Construct proof terms
   *   - useFFI {boolean} - Enable FFI (default true)
   *   - ffiMeta {Object} - FFI metadata
   *   - allBuckets {boolean} - Try all index buckets for metavar-first-arg goals
   *   - trace {boolean} - Collect trace
   *   - normalize {Function} - Term normalizer
   *   - buildClauseTerm {Function} - Builder (groundPrems, premTerms, groundHead, clauseName) for clause resolution
   *   - buildFFITerm {Function} - Builder (goalHash) for FFI success
   *   - buildTypeTerm {Function} - Builder (groundGoal, typeName) for type/axiom match
   *   - tryFFI {Function} - FFI dispatcher
   *   - theories {Array} - Equational theories (default: defaultTheories + binlitTheory)
   * @returns {{ success: boolean, theta: Array|null, term: Object|null, trace: string[]|null }}
   */
  backchain(goal, clauses, definitions, opts = {}) {
    this._maxDepth = opts.maxDepth || 100;
    this._trace = opts.trace ? [] : null;
    this._idx = opts.index || buildIndex(clauses, definitions);
    const useFFI = opts.useFFI !== false;
    this._buildTerm = !!opts.buildTerm;
    this._allBuckets = opts.allBuckets !== undefined ? !!opts.allBuckets : !useFFI;

    // Resolve backward chaining configuration.
    // Callers provide opts.theories (orchestrator injects from calculus config,
    // direct callers use makeILLBackchainOpts from ill/backchain-ill).
    // Without theories, only kernel default theories apply.
    this._theoryLookup = buildTheoryLookup(opts.theories || _defaultTheories);

    // Resolve normalize + term builders: explicit opts or identity/null
    this._normalize = opts.normalize || (x => x);
    this._buildClauseTermFn = opts.buildClauseTerm || null;
    this._buildFFITermFn = opts.buildFFITerm || null;
    this._buildTypeTermFn = opts.buildTypeTerm || null;

    // Resolve tryFFI: explicit opts or null (no FFI)
    if (opts.tryFFI) {
      if (opts.getFFIMeta) {
        const ffiMeta = opts.getFFIMeta();
        this._tryFFIFn = useFFI ? (g) => opts.tryFFI(g, ffiMeta) : null;
      } else {
        this._tryFFIFn = useFFI ? opts.tryFFI : null;
      }
    } else {
      this._tryFFIFn = null;
    }

    const queryMVs = new Set();
    collectMetavars(goal, queryMVs);
    const queryList = [];
    let qi = 0;
    for (const mv of queryMVs) {
      queryList.push({ hash: mv, localSlot: qi });
      qi++;
    }

    // Initialize slot machinery
    this._trailLen = 0;
    this._nextBase = 0;
    for (let i = 0; i < MAX_SLOTS; i++) this._theta[i] = undefined;
    for (let i = 0; i < this._queryMVCleanup.length; i++) this._mvSlots[this._queryMVCleanup[i]] = 0;
    this._queryMVCleanup.length = 0;
    const queryBase = this._reserveFrame(qi || 0);
    for (const { hash: mvHash, localSlot } of queryList) {
      this._ensureMVSlots(mvHash);
      this._mvSlots[mvHash] = queryBase + localSlot + 1;
      this._queryMVCleanup.push(mvHash);
    }

    const result = this._search(goal, 0);

    if (result) {
      const theta = [];
      for (const { hash: mvHash, localSlot } of queryList) {
        const val = this._theta[queryBase + localSlot];
        if (val !== undefined) {
          theta.push([mvHash, this._resolveSlots(val)]);
        }
      }
      return { success: true, theta, term: result.term, trace: this._trace };
    }
    return { success: false, theta: null, term: null, trace: this._trace };
  }
}

// ============================================================================
// SINGLETON + BACKWARD-COMPATIBLE WRAPPER
// ============================================================================

const _defaultBackchainer = new Backchainer();

function backchain(goal, clauses, definitions, opts) {
  return _defaultBackchainer.backchain(goal, clauses, definitions, opts);
}

// Backward-compatible alias (public API)
const prove = backchain;

// ============================================================================
// UTILITIES
// ============================================================================

function formatTerm(h, depth = 0) {
  if (depth > 5) return '...';
  const node = Store.get(h);
  if (!node) return '?';
  if (node.tag === 'atom') return node.children[0];
  if (node.tag === 'freevar') return node.children[0];
  if (node.tag === 'metavar') return '?' + node.children[0];
  if (node.tag === 'binlit') return `0b${node.children[0].toString(2)}`;
  if (node.children.length === 0) return node.tag;
  const args = node.children.map(c =>
    typeof c === 'number' ? formatTerm(c, depth + 1) : String(c)
  ).join(' ');
  return `${node.tag} ${args}`;
}

// Reset singleton state when Store is cleared (hash IDs get reused).
// Without this, _mvSlots retains stale mappings from previous backchain() runs.
function clearState() {
  _defaultBackchainer._mvSlots.fill(0);
  _defaultBackchainer._slotMV.length = 0;
  _defaultBackchainer._queryMVCleanup.length = 0;
  _defaultBackchainer._trailLen = 0;
  _defaultBackchainer._nextBase = 0;
  for (let i = 0; i < MAX_SLOTS; i++) _defaultBackchainer._theta[i] = undefined;
}
Store.onClear(clearState);

module.exports = { backchain, prove, buildIndex };
