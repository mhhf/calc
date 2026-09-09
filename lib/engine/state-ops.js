/**
 * State Operations — shared helpers for forward.js and explore.js.
 *
 * Factored from duplicated consume/produce/skip-preserved logic.
 */

import Store from '../kernel/store.js';
import { applyIndexed as subApplyIdx, subCompiled } from '../kernel/substitute.js';
/**
 * Apply substitution to a consequent pattern using compiled recipe if available.
 * Falls back to subApplyIdx when no recipe exists.
 */
function compiledSub(pattern, index, theta, slots, compiledList, _subApplyIdx) {
  const recipe = compiledList && compiledList[index];
  if (recipe && recipe.compiled) {
    return recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
  }
  return _subApplyIdx(pattern, theta, slots);
}

// ── Preserved optimization — skip re-producing unchanged facts ──
// When a rule's antecedent and consequent share linear patterns
// (preserved facts), skip consuming and re-producing them: avoids Store
// lookups and FactSet mutations for unchanged facts.

/** Build a skip-count map for preserved patterns (null if none). */
function preservedSkip(preserved) {
  if (!preserved || preserved.length === 0) return null;
  const skipCount = {};
  for (const h of preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  return skipCount;
}

/**
 * Filter linear patterns by removing preserved (re-produced) facts.
 * Used by explore multi-alt branches where compiled recipes aren't available.
 */
function filterPres(linearPats, preserved) {
  const skipCount = preservedSkip(preserved);
  if (!skipCount) return linearPats;
  const skipUsed = {};
  const out = [];
  for (const p of linearPats) {
    if (skipCount[p] > 0 && (skipUsed[p] || 0) < skipCount[p]) {
      skipUsed[p] = (skipUsed[p] || 0) + 1;
      continue;
    }
    out.push(p);
  }
  return out;
}
/**
 * Consume linear facts from state.
 * @param {FactSet} linear - linear FactSet (mutated)
 * @param {{ [hash: string]: number }} consumed - facts to consume
 * @param {Arena|null} arena - undo arena (null for clone-based)
 */
function consume(linear, consumed, arena) {
  for (const hStr in consumed) {
    const hash = Number(hStr);
    const count = consumed[hStr];
    const tagIdx = Store.tagId(hash);
    for (let c = 0; c < count; c++) {
      linear.remove(tagIdx, hash, arena);
    }
  }
}

/**
 * Produce linear facts into state, with preserved-skip and compiled substitution.
 * @param {FactSet} linear - linear FactSet (mutated)
 * @param {number[]} patterns - consequent linear pattern hashes
 * @param {Array} theta - substitution bindings
 * @param {Object} slots - metavar slot mapping
 * @param {Object|null} rule - compiled rule (for preserved + compiled sub)
 * @param {boolean} optimized - whether to use preserved-skip
 * @param {Arena|null} arena - undo arena
 * @param {Function|null} canon - composed theory canonicalizer (state-canonicity
 *   invariant: live state facts are canonical; applied only to patterns
 *   flagged at compile time)
 * @param {number[]|null} canonPats - flagged pattern hashes (rule.canonPatterns;
 *   passed separately because explore's alt branches pass rule = null)
 */
// Pooled objects for preserved-skip counting (avoid per-call allocation)
const _poolSkipCount = Object.create(null);
const _poolSkipUsed = Object.create(null);
let _poolSkipKeys = [];

function produce(linear, patterns, theta, slots, rule, optimized, arena, canon, canonPats) {
  const cLinear = rule && rule.compiledConseqLinear;
  let hasSkip = false;
  if (optimized && rule && rule.preserved && rule.preserved.length > 0) {
    hasSkip = true;
    for (const h of rule.preserved) _poolSkipCount[h] = (_poolSkipCount[h] || 0) + 1;
    _poolSkipKeys = rule.preserved;
  }

  for (let i = 0; i < patterns.length; i++) {
    const pattern = patterns[i];
    if (hasSkip && _poolSkipCount[pattern] > 0 &&
        (_poolSkipUsed[pattern] || 0) < _poolSkipCount[pattern]) {
      _poolSkipUsed[pattern] = (_poolSkipUsed[pattern] || 0) + 1;
      continue;
    }
    let h = compiledSub(pattern, i, theta, slots, cLinear, subApplyIdx);
    if (canon && canonPats && canonPats.indexOf(pattern) >= 0) h = canon(h);
    linear.insert(Store.tagId(h), h, arena);
  }

  // Reset pooled objects
  if (hasSkip) {
    for (const h of _poolSkipKeys) {
      _poolSkipCount[h] = 0;
      _poolSkipUsed[h] = 0;
    }
  }
}

/**
 * Produce persistent facts into state (dedup: skip if already present).
 * @param {FactSet} persistent - persistent FactSet (mutated)
 * @param {number[]} patterns - consequent persistent pattern hashes
 * @param {Array} theta - substitution bindings
 * @param {Object} slots - metavar slot mapping
 * @param {Object|null} rule - compiled rule (for compiled sub)
 * @param {Arena|null} arena - undo arena
 */
function producePers(persistent, patterns, theta, slots, rule, arena, canon, canonPats) {
  const cPersistent = rule && rule.compiledConseqPersistent;
  for (let i = 0; i < patterns.length; i++) {
    let h = compiledSub(patterns[i], i, theta, slots, cPersistent, subApplyIdx);
    if (canon && canonPats && canonPats.indexOf(patterns[i]) >= 0) h = canon(h);
    const tagIdx = Store.tagId(h);
    if (!persistent.has(tagIdx, h)) {
      persistent.insert(tagIdx, h, arena);
    }
  }
}

/**
 * Mutate state in-place: consume linear facts, produce new facts.
 * Records undo entries in linArena/perArena for backtracking.
 *
 * Secondary-index invalidation (TODO_0309): the _byKey fingerprint index
 * is built once per explore() run and is only sound while the indexed
 * predicate's group is untouched. EVM's indexed facts ($code) are
 * preserved — never consumed — so the index survives; a program that
 * genuinely consumes/produces indexed facts (SAX-style proc churn) must
 * drop it or matching commits against stale facts. Once null it stays
 * null for the rest of the DFS — fpValue and matchLinear1 fall back to
 * complete group scans (correct, slower).
 */
function mutateState(state, consumed, theta, linearPatterns, persistentPatterns, slots, rule, linArena, perArena, canon, canonPats) {
  if (state._byKey && state._fpPred) {
    const fpTagId = Store.TAG[state._fpPred];
    if (fpTagId !== undefined) {
      let touched = false;
      for (const hStr in consumed) {
        if (Store.tagId(Number(hStr)) === fpTagId) { touched = true; break; }
      }
      if (!touched && linearPatterns) {
        for (let i = 0; i < linearPatterns.length; i++) {
          const t = Store.tagId(linearPatterns[i]);
          // a bare-metavar pattern could instantiate to anything —
          // invalidate conservatively
          if (t === fpTagId || Store.tag(linearPatterns[i]) === 'metavar') { touched = true; break; }
        }
      }
      if (touched) state._byKey = null;
    }
  }
  consume(state.linear, consumed, linArena);
  produce(state.linear, linearPatterns, theta, slots, rule, !!rule, linArena, canon, canonPats);
  producePers(state.persistent, persistentPatterns, theta, slots, rule, perArena, canon, canonPats);
}

/**
 * Canonicalize a plain { hash: count } fact object at the state-entry
 * boundary (the API hole in the state-canonicity invariant: parser-built
 * states are canonical, Store-level callers may hand anything). Merges
 * counts on representation collisions — multiset-of-values semantics.
 * Cold path: runs once per exec/explore entry, never per step.
 */
function canonObject(obj, canon) {
  if (!canon || !obj) return obj;
  let changed = false;
  const out = {};
  for (const k in obj) {
    const h = Number(k);
    const c = canon(h);
    if (c !== h) changed = true;
    out[c] = (out[c] || 0) + obj[k];
  }
  return changed ? out : obj;
}

export { filterPres, compiledSub, consume, produce, producePers, mutateState, canonObject };
export default { filterPres, compiledSub, consume, produce, producePers, mutateState, canonObject };
