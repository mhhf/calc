/**
 * Backward Chaining Prover — slot-indexed theta, trail backtracking
 *
 * Calculus-agnostic search with first-argument indexing.
 * ILL-specific behavior (normalization, proof terms, FFI) injected via opts.
 *
 * Core invariant: zero allocation in the search loop.
 * Variables are slot indices into a flat array, not Store hashes.
 * Trail-based backtracking: undo() restores theta in O(delta).
 *
 * Zig-friendly: all hot-path data lives in typed arrays / flat arrays.
 */

const Store = require('../kernel/store');
const { isPredTag, getPredicateHead: getHead, buildRightTensor } = require('../kernel/ast');
const { collectMetavars } = require('./pattern-utils');
const {
  compilePatternMatch, PM_BIND, PM_CHECK, PM_GROUND, PM_COMPOUND, _skipInstruction,
} = require('./compile');

// Tag IDs for ephemeral expansion
// NOTE: arrlit, acons, binlit have fixed tag IDs (< PRED_BOUNDARY), safe to cache.
// o, i are dynamic (>= PRED_BOUNDARY) and may change after Store.restore(),
// so we use getter functions instead of cached values.
const _TAG_ARRLIT = Store.TAG.arrlit;
const _TAG_ACONS = Store.TAG.acons;
Store.put('atom', ['ae']); // ensure ae is registered
const _TAG_BINLIT = Store.TAG.binlit;
// Register o/i tags (may not exist until first use)
const _ATOM_E = Store.put('atom', ['e']); // binary zero sentinel
Store.put('o', [_ATOM_E]); // ensure o tag is registered
Store.put('i', [_ATOM_E]); // ensure i tag is registered
// Dynamic tag lookups — Store.restore() may reassign these IDs
function _tagO() { return Store.TAG.o; }
function _tagI() { return Store.TAG.i; }

// Lazy FFI import (only for ILL default opts — never loaded for non-ILL callers)
let _ffi = null;
function _getFfi() { if (!_ffi) _ffi = require('./ffi'); return _ffi; }

// ============================================================================
// ILL-SPECIFIC DEFAULTS (used when callers don't override via opts)
// ============================================================================

/**
 * Normalize binary constructor chains (i/o/e) to compact binlit form.
 * ILL-specific: prevents hash divergence between forward engine and clause resolution.
 */
function _defaultNormalize(h) {
  if (!Store.isTerm(h)) return h;
  const tag = Store.tag(h);
  if (!tag) return h;
  const ffiMod = _getFfi();
  if (tag === 'i' || tag === 'o') {
    const v = ffiMod.convert.binToInt(h);
    if (v !== null) return ffiMod.convert.intToBin(v);
  }
  if (tag === 'atom') {
    const v = ffiMod.convert.binToInt(h);
    if (v !== null) return ffiMod.convert.intToBin(v);
    return h;
  }
  if (tag === 'binlit' || tag === 'strlit' || tag === 'charlit' ||
      tag === 'freevar' || tag === 'metavar') return h;
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) {
      const rc = _defaultNormalize(c);
      nc.push(rc);
      if (rc !== c) changed = true;
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(tag, nc) : h;
}

/**
 * Build an ILL clause proof term from ground components.
 * Reconstructs: copy(loli(tensor(!P₁,...), monad(Q)), loli_l(antProof, monad_l(id(Q))))
 */
function _defaultBuildClauseTerm(groundPrems, premTerms, groundHead) {
  const bangPrems = groundPrems.map(p => Store.put('bang', [p]));
  const groundAnt = buildRightTensor(bangPrems);
  const groundMonad = Store.put('monad', [groundHead]);
  const groundLoli = Store.put('loli', [groundAnt, groundMonad]);

  const wrappedPrems = premTerms.map(pt =>
    ({ rule: 'promotion', principal: null, subterms: [pt] }));
  const antProof = _tensorRSpine(wrappedPrems);

  const monadBody = { rule: 'monad_l', principal: groundMonad, subterms: [
    { rule: 'id', principal: groundHead, subterms: [] }
  ]};
  const loliApp = { rule: 'loli_l', principal: groundLoli,
                    subterms: [antProof, monadBody] };
  return { rule: 'copy', principal: groundLoli, subterms: [loliApp] };
}

function _tensorRSpine(terms) {
  if (terms.length === 0) return { rule: 'one_r', principal: null, subterms: [] };
  if (terms.length === 1) return terms[0];
  let acc = terms[terms.length - 1];
  for (let i = terms.length - 2; i >= 0; i--) {
    acc = { rule: 'tensor_r', principal: null, subterms: [terms[i], acc] };
  }
  return acc;
}

/** Default FFI dispatch for ILL predicates. */
function _defaultTryFFI(goal, ffiMeta) {
  const head = getHead(goal);
  if (!head) return null;
  const meta = ffiMeta[head];
  if (!meta || !meta.ffi) return null;
  if (!Store.isTerm(goal) || !isPredTag(Store.tag(goal))) return null;
  const a = Store.arity(goal);
  const args = new Array(a);
  for (let i = 0; i < a; i++) args[i] = Store.child(goal, i);
  const ffiMod = _getFfi();
  if (!ffiMod.mode.checkMode(args, meta.mode)) return null;
  const fn = ffiMod.get(meta.ffi);
  if (!fn) return null;
  return fn(args);
}

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

/**
 * Build two-level index with compiled clause heads.
 * Each clause gets: compiledHead (instructions), localSlots ({metavarHash: localIdx}),
 * metavarCount, metavarList ([{hash, localSlot}]).
 */
function buildIndex(clauses, types) {
  const idx = { types: {}, clauses: {} };

  for (const [name, hash] of types) {
    const head = getHead(hash);
    if (!head) continue;
    // Compile type for instruction-based matching
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
      compiledHead: compilePatternMatch(hash, localSlots),
    };
    const fa = getFirstArgHead(hash) || '_';
    (idx.types[head] ||= {})[fa] ||= [];
    idx.types[head][fa].push([name, compiled]);
  }

  for (const [name, clause] of clauses) {
    const head = getHead(clause.hash);
    if (!head) continue;
    // Compile clause head + collect metavars across head + premises
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
      compiledHead: compilePatternMatch(clause.hash, localSlots),
    };
    const fa = getFirstArgHead(clause.hash) || '_';
    (idx.clauses[head] ||= {})[fa] ||= [];
    idx.clauses[head][fa].push([name, compiled]);
  }

  return idx;
}

/** Get candidate types and clauses for a goal. O(1). */
function getCandidates(idx, goalHash, allBuckets) {
  const head = getHead(goalHash);
  if (!head) return { types: [], clauses: [] };
  const fa = getFirstArgHead(goalHash) || '_';
  const ti = idx.types[head] || {};
  const ci = idx.clauses[head] || {};

  // When first arg is a variable (fa === '_') AND allBuckets is set,
  // check ALL buckets — the variable could unify with any constructor.
  // With FFI enabled, FFI handles metavar-first-arg cases before clause
  // resolution, so allBuckets is only needed when FFI is off.
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
// SLOT MACHINERY — flat theta array, trail-based backtracking
// ============================================================================

const MAX_SLOTS = 8192;
const MAX_TRAIL = 8192;

// Module-level state (non-reentrant — same contract as matchIndexed).
// _theta[slot] = undefined (unbound) | Store hash (bound to ground/compound value)
const _theta = new Array(MAX_SLOTS);
const _trail = new Uint32Array(MAX_TRAIL);
let _trailLen = 0;
let _nextBase = 0;

// Slot metavar cache: maps global slot index ↔ unique metavar Store hash.
// Created lazily. Used when materializing premises with unbound clause vars.
const _slotMV = [];       // [globalSlot] → metavar hash

// Typed-array reverse map: Store ID → global slot + 1 (0 = not a slot metavar).
// Eliminates the plain-object _slotMVMap that required O(N) clear + repopulate
// on every prove() call. Direct indexed lookup: O(1) with no hash table overhead.
let _mvSlotsLen = 4_000_000;
let _mvSlots = new Uint32Array(_mvSlotsLen);
// Small cleanup list: query metavar Store IDs registered at prove() entry.
// Zeroed out at the start of the next prove() call (typically < 10 entries).
const _queryMVCleanup = [];

function _ensureMVSlots(id) {
  if (id < _mvSlotsLen) return;
  const newLen = Math.max(_mvSlotsLen * 2, id + 1);
  const newArr = new Uint32Array(newLen);
  newArr.set(_mvSlots);
  _mvSlots = newArr;
  _mvSlotsLen = newLen;
}

function _getSlotMV(slot) {
  if (slot < _slotMV.length) return _slotMV[slot];
  while (_slotMV.length <= slot) {
    const i = _slotMV.length;
    const h = Store.put('metavar', ['_s' + i]);
    _slotMV.push(h);
    _ensureMVSlots(h);
    _mvSlots[h] = i + 1;
  }
  return _slotMV[slot];
}

function _reserveFrame(n) {
  const base = _nextBase;
  _nextBase += n;
  return base;
}

function _bind(slot, value) {
  _theta[slot] = value;
  _trail[_trailLen++] = slot;
}

function _undo(savedTrail, savedBase) {
  while (_trailLen > savedTrail) _theta[_trail[--_trailLen]] = undefined;
  _nextBase = savedBase;
}

// ============================================================================
// CLAUSE HEAD MATCHING — compiled instructions vs Store hash
// ============================================================================

// Pre-allocated match stack (non-reentrant). Pairs: [ip, hash].
const _mStack = new Array(128);

/**
 * Structural match: compare ground expected hash against goal hash that may contain metavars.
 * Binds goal metavars (via _mvSlots) to corresponding parts of expected.
 * Called when PM_GROUND identity check fails (goal has metavars).
 */
function _groundMatch(expected, goalH) {
  if (expected === goalH) return true;
  if (!Store.isTerm(expected) || !Store.isTerm(goalH)) return false;

  const gTid = Store.tagId(goalH);

  // Goal is a metavar — chase slot chain (prevents infinite loops on metavar→metavar chains)
  if (gTid === _MV_TAG_ID) {
    const gs = goalH < _mvSlotsLen ? _mvSlots[goalH] - 1 : -1;
    if (gs >= 0) {
      _chaseSlot(gs);
      if (_chaseValue !== undefined) return _groundMatch(expected, _chaseValue);
      _bind(_chaseFinalSlot, expected);
      return true;
    }
    return false; // Unknown metavar
  }

  // Expected is a slot metavar — resolve it before comparing
  const eTid = Store.tagId(expected);
  if (eTid === _MV_TAG_ID) {
    const eSlot = expected < _mvSlotsLen ? _mvSlots[expected] - 1 : -1;
    if (eSlot >= 0) {
      _chaseSlot(eSlot);
      if (_chaseValue !== undefined) return _groundMatch(_chaseValue, goalH);
      // Unbound expected metavar — bind it to the goal
      _bind(_chaseFinalSlot, goalH);
      return true;
    }
    return false; // Unknown metavar
  }

  // Both compound — decompose
  if (eTid !== gTid) {
    // --- Arrlit ephemeral expansion ---
    if (gTid === _TAG_ARRLIT) {
      const gElems = Store.getArrayElements(goalH);
      // ae (empty array sentinel) vs arrlit([])
      if (eTid === Store.TAG.atom && Store.child(expected, 0) === 'ae') {
        return gElems.length === 0;
      }
      // acons(H, T) vs arrlit([e0, e1, ...])
      if (eTid === _TAG_ACONS && Store.arity(expected) === 2) {
        if (gElems.length === 0) return false;
        if (!_groundMatch(Store.child(expected, 0), gElems[0])) return false;
        const tailData = new Uint32Array(gElems.length - 1);
        for (let i = 1; i < gElems.length; i++) tailData[i - 1] = gElems[i];
        return _groundMatch(Store.child(expected, 1), Store.put('arrlit', [tailData]));
      }
    }
    if (eTid === _TAG_ARRLIT) {
      const eElems = Store.getArrayElements(expected);
      // arrlit([]) vs ae
      if (gTid === Store.TAG.atom && Store.child(goalH, 0) === 'ae') {
        return eElems.length === 0;
      }
      // arrlit vs acons
      if (gTid === _TAG_ACONS && Store.arity(goalH) === 2) {
        if (eElems.length === 0) return false;
        if (!_groundMatch(eElems[0], Store.child(goalH, 0))) return false;
        const tailData = new Uint32Array(eElems.length - 1);
        for (let i = 1; i < eElems.length; i++) tailData[i - 1] = eElems[i];
        return _groundMatch(Store.put('arrlit', [tailData]), Store.child(goalH, 1));
      }
    }

    // --- Binlit ephemeral expansion ---
    // binlit goal vs structural expected (e/o/i)
    if (gTid === _TAG_BINLIT) {
      const gVal = Store.child(goalH, 0);
      // e vs binlit(0n)
      if (eTid === Store.TAG.atom && Store.child(expected, 0) === 'e') {
        return gVal === 0n;
      }
      // o(X) vs binlit(n) — even, nonzero
      if (eTid === _tagO() && Store.arity(expected) === 1) {
        if (typeof gVal !== 'bigint' || gVal <= 0n || (gVal & 1n) !== 0n) return false;
        return _groundMatch(Store.child(expected, 0), Store.put1('binlit', gVal >> 1n));
      }
      // i(X) vs binlit(n) — odd
      if (eTid === _tagI() && Store.arity(expected) === 1) {
        if (typeof gVal !== 'bigint' || (gVal & 1n) !== 1n) return false;
        return _groundMatch(Store.child(expected, 0), Store.put1('binlit', gVal >> 1n));
      }
      // binlit vs binlit (different values)
      if (eTid === _TAG_BINLIT) {
        return Store.child(expected, 0) === gVal;
      }
    }
    // Reverse: structural goal (e/o/i) vs binlit expected
    if (eTid === _TAG_BINLIT) {
      const eVal = Store.child(expected, 0);
      // binlit(0n) vs e
      if (gTid === Store.TAG.atom && Store.child(goalH, 0) === 'e') {
        return eVal === 0n;
      }
      // binlit(n) vs o(X) — even, nonzero
      if (gTid === _tagO() && Store.arity(goalH) === 1) {
        if (typeof eVal !== 'bigint' || eVal <= 0n || (eVal & 1n) !== 0n) return false;
        return _groundMatch(Store.put1('binlit', eVal >> 1n), Store.child(goalH, 0));
      }
      // binlit(n) vs i(X) — odd
      if (gTid === _tagI() && Store.arity(goalH) === 1) {
        if (typeof eVal !== 'bigint' || (eVal & 1n) !== 1n) return false;
        return _groundMatch(Store.put1('binlit', eVal >> 1n), Store.child(goalH, 0));
      }
    }

    return false;
  }
  // arrlit vs arrlit: element-wise matching
  if (eTid === _TAG_ARRLIT) {
    const eElems = Store.getArrayElements(expected);
    const gElems = Store.getArrayElements(goalH);
    if (eElems.length !== gElems.length) return false;
    for (let i = 0; i < eElems.length; i++) {
      if (!_groundMatch(eElems[i], gElems[i])) return false;
    }
    return true;
  }
  const eArity = Store.arity(expected);
  if (eArity !== Store.arity(goalH)) return false;
  for (let i = 0; i < eArity; i++) {
    const ec = Store.child(expected, i);
    const gc = Store.child(goalH, i);
    if (Store.isTermChild(ec) && Store.isTermChild(gc)) {
      if (!_groundMatch(ec, gc)) return false;
    } else if (ec !== gc) {
      return false;
    }
  }
  return true;
}

/**
 * Chase a slot metavar chain to its ultimate value or final unbound slot.
 * Results written to _chaseValue / _chaseFinalSlot (avoids per-call allocation).
 *   _chaseValue: ground hash (or undefined if chain ends at unbound slot)
 *   _chaseFinalSlot: the final slot in the chain (for binding if needed)
 * Max 32 hops to prevent infinite loops on circular aliases.
 */
let _chaseValue;
let _chaseFinalSlot;
function _chaseSlot(startSlot) {
  let slot = startSlot;
  for (let hops = 0; hops < 32; hops++) {
    const val = _theta[slot];
    if (val === undefined) { _chaseValue = undefined; _chaseFinalSlot = slot; return; }
    // Is val a slot metavar? Check typed-array reverse map.
    const ns = val < _mvSlotsLen ? _mvSlots[val] - 1 : -1;
    if (ns < 0) { _chaseValue = val; _chaseFinalSlot = slot; return; }
    // It's a slot metavar — follow the chain
    slot = ns;
  }
  _chaseValue = undefined; _chaseFinalSlot = slot; // Circular — treat as unbound
}

/**
 * Match compiled clause head instructions against a goal Store hash.
 *
 * Clause variables: bound into _theta[base + inst.slot].
 * Goal metavars: detected via _mvSlots, resolved through _theta.
 *
 * Handles the two-sided case: when a goal metavar is unbound and meets
 * a clause structure, the structure is materialized and bound to the
 * goal variable (write mode). This is rare — most goals are ground
 * after applying prior bindings.
 *
 * @param {Array} insts - Compiled instructions (DFS pre-order)
 * @param {number} goalHash - Goal Store hash
 * @param {number} base - Frame base for clause variables
 * @returns {boolean} true if match succeeded (_theta updated via trail)
 */
function _matchHead(insts, goalHash, base) {
  let sp = 0;
  _mStack[sp++] = 0;
  _mStack[sp++] = goalHash;

  while (sp > 0) {
    const h = _mStack[--sp];
    const ip = _mStack[--sp];
    const inst = insts[ip];

    // Resolve goal-side metavars: if h is a slot metavar, chase to ground value
    let resolved = h;
    let goalSlot = -1;
    const gs = h < _mvSlotsLen ? _mvSlots[h] - 1 : -1;
    if (gs >= 0) {
      _chaseSlot(gs);
      if (_chaseValue !== undefined) {
        // Ground value found — use it
        resolved = _chaseValue;
      } else {
        // Unbound goal variable — handle per instruction type (write mode)
        goalSlot = _chaseFinalSlot;
        switch (inst.op) {
          case PM_BIND:
          case PM_CHECK: {
            const cSlot = base + inst.slot;
            const existing = _theta[cSlot];
            if (existing !== undefined) {
              _bind(goalSlot, existing);
            } else {
              _bind(goalSlot, _getSlotMV(cSlot));
              _bind(cSlot, _getSlotMV(goalSlot));
            }
            continue;
          }
          case PM_GROUND:
            _bind(goalSlot, inst.expected);
            continue;
          case PM_COMPOUND: {
            const mat = _materialize(insts, ip, base);
            _bind(goalSlot, mat);
            continue;
          }
        }
      }
    }

    // Standard matching (resolved is a concrete Store hash, may contain metavars)
    switch (inst.op) {
      case PM_BIND:
      case PM_CHECK: {
        const slot = base + inst.slot;
        const existing = _theta[slot];
        if (existing !== undefined) {
          // Identity check first (fast path), then ephemeral-aware structural match.
          // Needed because binlit(32) and o(binlit(16)) are semantically equal
          // but have different Store hashes.
          if (existing !== resolved && !_groundMatch(existing, resolved)) return false;
        } else {
          _bind(slot, resolved);
        }
        break;
      }
      case PM_GROUND:
        if (resolved !== inst.expected) {
          // Identity check failed. The goal may have metavars.
          // Fall back to recursive structural match with metavar binding.
          if (!_groundMatch(inst.expected, resolved)) return false;
        }
        break;
      case PM_COMPOUND: {
        const tid = Store.tagId(resolved);
        if (tid !== inst.tagId || Store.arity(resolved) !== inst.arity) {
          // Ephemeral expansion: arrlit ↔ acons/ae matching
          // acons(H, T) pattern vs arrlit goal → decompose head + tail
          if (tid === _TAG_ARRLIT && inst.tagId === _TAG_ACONS && inst.arity === 2) {
            const elems = Store.getArrayElements(resolved);
            if (!elems || elems.length === 0) return false;
            // Synthesize tail: arrlit of remaining elements
            const tailData = new Uint32Array(elems.length - 1);
            for (let i = 1; i < elems.length; i++) tailData[i - 1] = elems[i];
            const tailHash = Store.put('arrlit', [tailData]);
            // Push children: child0=head, child1=tail
            let childIp = ip + 1;
            const child1Ip = _skipInstruction(insts, childIp);
            _mStack[sp++] = child1Ip;
            _mStack[sp++] = tailHash;
            _mStack[sp++] = childIp;
            _mStack[sp++] = elems[0];
            break;
          }
          // ae pattern (atom 'ae') vs arrlit → match empty array
          // Handled by PM_GROUND: ae is ground, arrlit is checked there.

          // Binlit ephemeral expansion: o(X)/i(X) pattern vs binlit goal
          // o(X) matches binlit(n) when n > 0 and LSB = 0 → X = binlit(n >> 1)
          // i(X) matches binlit(n) when LSB = 1 → X = binlit(n >> 1)
          if (tid === _TAG_BINLIT && inst.arity === 1) {
            const value = Store.child(resolved, 0); // BigInt value
            if (inst.tagId === _tagO()) {
              if (typeof value !== 'bigint' || value <= 0n || (value & 1n) !== 0n) return false;
              const childIp = ip + 1;
              _mStack[sp++] = childIp;
              _mStack[sp++] = Store.put1('binlit', value >> 1n);
              break;
            }
            if (inst.tagId === _tagI()) {
              if (typeof value !== 'bigint' || (value & 1n) !== 1n) return false;
              const childIp = ip + 1;
              _mStack[sp++] = childIp;
              _mStack[sp++] = Store.put1('binlit', value >> 1n);
              break;
            }
          }
          return false;
        }
        // Push children in reverse order (DFS left-to-right processing)
        let childIp = ip + 1;
        for (let ci = inst.arity - 1; ci >= 0; ci--) {
          let skipIp = childIp;
          for (let s = 0; s < ci; s++) skipIp = _skipInstruction(insts, skipIp);
          _mStack[sp++] = skipIp;
          _mStack[sp++] = Store.child(resolved, ci);
        }
        break;
      }
    }
  }
  return true;
}

/**
 * Materialize an instruction subtree as a Store hash.
 * Used for "write mode": binding an unbound goal variable to a clause structure.
 * Substitutes bound clause slots with their values; unbound slots become slot metavars.
 */
function _materialize(insts, ip, base) {
  const inst = insts[ip];
  switch (inst.op) {
    case PM_GROUND: return inst.expected;
    case PM_BIND:
    case PM_CHECK: {
      const slot = base + inst.slot;
      const val = _theta[slot];
      return val !== undefined ? val : _getSlotMV(slot);
    }
    case PM_COMPOUND: {
      const children = [];
      let childIp = ip + 1;
      for (let i = 0; i < inst.arity; i++) {
        children.push(_materialize(insts, childIp, base));
        childIp = _skipInstruction(insts, childIp);
      }
      return Store.put(Store.TAG_NAMES[inst.tagId], children);
    }
  }
  return 0; // unreachable
}

// ============================================================================
// PREMISE MATERIALIZATION — substitute bound clause slots in premise hashes
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

/**
 * Materialize a premise Store hash by substituting clause variables.
 * Bound slots → their values. Unbound slots → slot metavars.
 *
 * @param {number} h - Premise Store hash (original, with metavar hashes)
 * @param {Object} localSlots - {metavarHash: localIndex}
 * @param {number} base - Frame base
 * @returns {number} Materialized Store hash
 */
function _materializePremise(h, localSlots, base) {
  if (!Store.isTerm(h)) return h;
  const tid = Store.tagId(h);

  // Metavar: substitute from slot array
  if (tid === _MV_TAG_ID) {
    const localIdx = localSlots[h];
    if (localIdx !== undefined) {
      const val = _theta[base + localIdx];
      return val !== undefined ? val : _getSlotMV(base + localIdx);
    }
    return h; // External metavar (not in this clause) — leave as-is
  }

  // Leaf: no children
  if (_LEAF_TAGS[tid]) return h;

  // Arrlit
  if (tid === _ARRLIT_TAG) {
    const elems = Store.getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const newElems = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      const r = _materializePremise(elems[i], localSlots, base);
      newElems[i] = r;
      if (r !== elems[i]) changed = true;
    }
    return changed ? Store.putArray(newElems) : h;
  }

  // Compound: recurse children
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = new Array(a);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = _materializePremise(c, localSlots, base);
      nc[i] = r;
      if (r !== c) changed = true;
    } else {
      nc[i] = c;
    }
  }
  return changed ? Store.put(Store.tag(h), nc) : h;
}

// ============================================================================
// RESOLUTION — resolve slot metavars in a term to their final values
// ============================================================================

/**
 * Resolve all slot metavars in a Store hash to their bound values.
 * Called at output time only (not during search).
 */
function _resolveSlots(h) {
  if (!Store.isTerm(h)) return h;
  const tid = Store.tagId(h);

  if (tid === _MV_TAG_ID) {
    // Check if it's a slot metavar — chase the chain to ground value
    const slot = h < _mvSlotsLen ? _mvSlots[h] - 1 : -1;
    if (slot >= 0) {
      _chaseSlot(slot);
      if (_chaseValue !== undefined) return _resolveSlots(_chaseValue);
    }
    return h;
  }

  if (_LEAF_TAGS[tid]) return h;

  if (tid === _ARRLIT_TAG) {
    const elems = Store.getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const newElems = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      const r = _resolveSlots(elems[i]);
      newElems[i] = r;
      if (r !== elems[i]) changed = true;
    }
    return changed ? Store.putArray(newElems) : h;
  }

  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = new Array(a);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = _resolveSlots(c);
      nc[i] = r;
      if (r !== c) changed = true;
    } else {
      nc[i] = c;
    }
  }
  return changed ? Store.put(Store.tag(h), nc) : h;
}

// ============================================================================
// PROOF SEARCH
// ============================================================================

/**
 * Prove a goal using backward chaining with slot-indexed theta.
 *
 * @param {number} goal - Goal hash to prove
 * @param {Map} clauses - Map of name → { hash, premises }
 * @param {Map} types - Map of name → hash (axioms/facts)
 * @param {Object} opts
 *   - maxDepth {number} - Max search depth (default 100)
 *   - index {Object} - Pre-built index from buildIndex()
 *   - buildTerm {boolean} - Construct proof terms
 *   - useFFI {boolean} - Enable FFI (default true)
 *   - ffiMeta {Object} - FFI metadata
 *   - allBuckets {boolean} - Try all index buckets for metavar-first-arg goals (auto: !useFFI)
 *   - trace {boolean} - Collect trace
 *   - normalize {Function} - Term normalizer (default: ILL binary normalization)
 *   - buildClauseTerm {Function} - Proof term builder (default: ILL loli/bang/monad)
 *   - tryFFI {Function} - FFI dispatcher (default: ILL FFI)
 * @returns {{ success: boolean, theta: Array|null, term: Object|null, trace: string[]|null }}
 */
function prove(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const trace = opts.trace ? [] : null;
  const idx = opts.index || buildIndex(clauses, types);
  const useFFI = opts.useFFI !== false;
  const ffiMeta = opts.ffiMeta || (useFFI ? _getFfi().defaultMeta : {});
  const buildTerm = !!opts.buildTerm;
  // allBuckets: when first arg is metavar, try all index buckets (not just '_').
  // Auto-enabled when FFI is off, since FFI normally handles metavar-first-arg queries.
  const allBuckets = opts.allBuckets !== undefined ? !!opts.allBuckets : !useFFI;

  // Pluggable ILL hooks (defaults are ILL-specific)
  const normalize = opts.normalize || _defaultNormalize;
  const buildClauseTermFn = opts.buildClauseTerm || _defaultBuildClauseTerm;
  const tryFFIFn = opts.tryFFI !== undefined ? opts.tryFFI
    : (useFFI ? (g) => _defaultTryFFI(g, ffiMeta) : null);

  // Compile the initial goal: collect its metavars and assign query slots
  const queryMVs = new Set();
  collectMetavars(goal, queryMVs);
  const queryList = [];
  let qi = 0;
  for (const mv of queryMVs) {
    queryList.push({ hash: mv, localSlot: qi });
    qi++;
  }

  // Initialize slot machinery
  _trailLen = 0;
  _nextBase = 0;
  // Clear only the slots we'll actually use (lazy clear via undo on backtrack)
  for (let i = 0; i < MAX_SLOTS; i++) _theta[i] = undefined;
  // Clear previous query metavar entries from _mvSlots (typically < 10 entries).
  // Permanent slot metavar entries (_getSlotMV) stay — they never change.
  for (let i = 0; i < _queryMVCleanup.length; i++) _mvSlots[_queryMVCleanup[i]] = 0;
  _queryMVCleanup.length = 0;
  const queryBase = _reserveFrame(qi || 0);
  // Register query metavars in _mvSlots so _chaseSlot can follow chains
  for (const { hash: mvHash, localSlot } of queryList) {
    _ensureMVSlots(mvHash);
    _mvSlots[mvHash] = queryBase + localSlot + 1;
    _queryMVCleanup.push(mvHash);
  }

  function search(goalHash, depth) {
    if (depth > maxDepth) return null;

    // Try FFI first
    if (tryFFIFn) {
      const ffiResult = tryFFIFn(goalHash);
      if (ffiResult && ffiResult.success) {
        if (trace) trace.push(`${'  '.repeat(depth)}FFI: ${getHead(goalHash)} ✓`);
        // Write FFI theta into our slot array
        if (ffiResult.theta) {
          for (const [varHash, val] of ffiResult.theta) {
            const slot = varHash < _mvSlotsLen ? _mvSlots[varHash] - 1 : -1;
            if (slot >= 0 && _theta[slot] === undefined) {
              _bind(slot, val);
            }
          }
        }
        return { term: buildTerm ? { rule: 'ffi', principal: null, subterms: [] } : null };
      }
    }

    const { types: candTypes, clauses: candClauses } = getCandidates(idx, goalHash, allBuckets);

    if (trace) trace.push(`${'  '.repeat(depth)}Goal: ${formatTerm(goalHash)} [${candTypes.length}t/${candClauses.length}c]`);

    // Try types (axioms)
    for (const [name, compiled] of candTypes) {
      const savedTrail = _trailLen;
      const savedBase = _nextBase;
      const typeBase = _reserveFrame(compiled.metavarCount);

      if (_matchHead(compiled.compiledHead, goalHash, typeBase)) {
        if (trace) trace.push(`${'  '.repeat(depth)}  ✓ ${name}`);
        if (buildTerm) {
          const groundGoal = normalize(_resolveSlots(goalHash));
          return {
            term: { rule: 'copy', principal: groundGoal,
                    subterms: [{ rule: 'id', principal: groundGoal, subterms: [] }] }
          };
        }
        return { term: null };
      }
      _undo(savedTrail, savedBase);
    }

    // Try clauses
    for (const [name, compiled] of candClauses) {
      const savedTrail = _trailLen;
      const savedBase = _nextBase;
      const clauseBase = _reserveFrame(compiled.metavarCount);

      if (!_matchHead(compiled.compiledHead, goalHash, clauseBase)) {
        _undo(savedTrail, savedBase);
        continue;
      }

      if (trace) trace.push(`${'  '.repeat(depth)}  → ${name}`);

      // Recurse into premises
      let ok = true;
      const premTerms = [];
      for (let pi = 0; pi < compiled.premises.length; pi++) {
        // Materialize premise: substitute bound clause vars
        const premGoal = _materializePremise(compiled.premises[pi], compiled.localSlots, clauseBase);

        const r = search(premGoal, depth + 1);
        if (r === null) { ok = false; break; }
        if (buildTerm) premTerms.push(r.term);
      }

      if (ok) {
        if (trace) trace.push(`${'  '.repeat(depth)}  ✓ ${name}`);
        if (buildTerm) {
          // Materialize ground head + premises for proof term
          const groundHead = normalize(_resolveSlots(
            _materializePremise(compiled.hash, compiled.localSlots, clauseBase)));
          const groundPrems = compiled.premises.map(p => normalize(_resolveSlots(
            _materializePremise(p, compiled.localSlots, clauseBase))));
          return { term: buildClauseTermFn(groundPrems, premTerms, groundHead) };
        }
        return { term: null };
      }

      _undo(savedTrail, savedBase);
    }

    if (trace) trace.push(`${'  '.repeat(depth)}  ✗`);
    return null;
  }

  const result = search(goal, 0);

  if (result) {
    // Extract output theta: resolve query slots to ground values
    const theta = [];
    for (const { hash: mvHash, localSlot } of queryList) {
      const val = _theta[queryBase + localSlot];
      if (val !== undefined) {
        theta.push([mvHash, _resolveSlots(val)]);
      }
    }
    return { success: true, theta, term: result.term, trace };
  }
  return { success: false, theta: null, term: null, trace };
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
  if (node.tag === 'metavar') return '?' + node.children[0];
  if (node.tag === 'binlit') return `0b${node.children[0].toString(2)}`;
  if (node.children.length === 0) return node.tag;
  const args = node.children.map(c =>
    typeof c === 'number' ? formatTerm(c, depth + 1) : String(c)
  ).join(' ');
  return `${node.tag} ${args}`;
}

module.exports = { prove, formatTerm, buildIndex, getCandidates };
