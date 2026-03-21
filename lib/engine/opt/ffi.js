/**
 * FFI optimization for persistent proving.
 *
 * Extracts the FFI-first persistent proving path from match.js.
 * When enabled, persistent goals try FFI before state lookup and clause
 * resolution. When disabled, only state lookup → clause resolution.
 */

const Store = require('../../kernel/store');
const { isPredTag, getPredicateHead, collectExternalFreevars, proverBoundExternals } = require('../../kernel/ast');
const { matchIndexed: matchIdx, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed: subApplyIdx } = require('../../kernel/substitute');
const ffi = require('../ill/ffi');

const PROFILE = typeof process !== 'undefined' && process.env.CALC_PERF_PROFILE === '1';

// ─── FFI Direct Bypass ──────────────────────────────────────────────

const _ffiMeta = ffi.defaultMeta;
const _ffiParsedModes = ffi.parsedModes;

const _FFI_MAX_ARITY = 4;
const _ffiArgs = [0, 0, 0, 0];
for (const key in _ffiParsedModes) {
  if (_ffiParsedModes[key].length > _FFI_MAX_ARITY) {
    throw new Error(`FFI '${key}' arity ${_ffiParsedModes[key].length} exceeds _FFI_MAX_ARITY ${_FFI_MAX_ARITY} — increase buffer`);
  }
}

/** Try FFI directly, bypassing full prove() machinery */
function tryFFIDirect(goal) {
  const goalTag = Store.tag(goal);
  if (!goalTag) return null;

  let head;
  if (isPredTag(goalTag)) head = goalTag;
  else if (goalTag === 'atom') head = Store.child(goal, 0);
  else return null;

  const meta = _ffiMeta[head];
  if (!meta) return null;
  const fn = ffi.get(meta.ffi);
  if (!fn) return null;

  const modes = _ffiParsedModes[head];
  const goalArity = Store.arity(goal);
  if (goalArity !== modes.length) return null;

  for (let i = 0; i < goalArity; i++) {
    const c = Store.child(goal, i);
    if (!meta.multiModal && modes[i] === '+' && !ffi.convert.isGround(c)) return null;
    _ffiArgs[i] = c;
  }

  const result = fn(_ffiArgs);
  if (result && !result.success && result.reason) return null;
  return result;
}

// ─── FFI-enhanced Persistent Proving ─────────────────────────────────

let profile = { proveTime: 0, proveCalls: 0 };

function getProfile() { return profile; }
function resetProfile() { profile.proveTime = profile.proveCalls = 0; }

/**
 * Prove persistent antecedent patterns with FFI-first order:
 *   1. FFI — O(1) arithmetic (inc, plus, neq, mul, etc.)
 *   2. State lookup — match against persistent facts in state.persistent
 *   3. Clause resolution — full backward chaining via prove.js
 *
 * The evidenceOut parameter enables proof term reconstruction for the 'guided'
 * execution profile. When non-null, each proved goal pushes a record describing
 * HOW it was proved. guided-term.js uses these to build promotion(id/ffi) nodes
 * in the antecedent proof tree.
 *
 * Mutable collector pattern: evidenceOut is null (zero overhead) or [] (collects).
 * Same mutation style as theta — caller allocates, callee pushes.
 *
 * FFI failure is advisory: { success: false } falls through to state lookup
 * and clause resolution. This maintains "FFI is optimization, theory is semantics."
 *
 * @param {number[]} patterns - Persistent antecedent pattern hashes
 * @param {number} startIdx - Index to start proving from
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {State} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, types, backchainIndex } or null
 * @param {Array|null} evidenceOut - When non-null, pushes per-goal evidence
 *   { goal, method: 'state'|'ffi'|'clause', fact?, proof? }
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function provePersistentWithFFI(patterns, startIdx, theta, slots, state, calc, evidenceOut) {
  let idx = startIdx;
  while (idx < patterns.length) {
    // 1. FFI
    const goal = subApplyIdx(patterns[idx], theta, slots);
    const ffiResult = tryFFIDirect(goal);
    if (ffiResult) {
      if (ffiResult.success) {
        const ft = ffiResult.theta;
        for (let fi = 0; fi < ft.length; fi++) {
          const slot = slots[ft[fi][0]];
          if (slot !== undefined) theta[slot] = ft[fi][1];
        }
        if (evidenceOut) evidenceOut.push({ goal, method: 'ffi' });
        idx++;
        continue;
      }
      // FFI says false — advisory, fall through to state lookup + clause.
      // For ground arithmetic (inc, plus, neq, mul) this is redundant
      // (clauses also fail), but keeps FFI as pure optimization per
      // the principle "FFI is optimization, theory is semantics."
    }

    // 2. State lookup
    {
      const pattern = patterns[idx];
      const pPred = getPredicateHead(pattern);

      if (pPred) {
        const pTagId = Store.TAG[pPred];
        const effectiveTagId = (pTagId !== undefined && pTagId >= Store.PRED_BOUNDARY)
          ? pTagId : Store.TAG.atom;
        if (effectiveTagId !== undefined && state.persistent.groupLen(effectiveTagId) > 0) {
          const persGroup = state.persistent.group(effectiveTagId);
          let foundInState = false;
          let matchedFact = null;
          for (let gi = 0; gi < persGroup.length; gi++) {
            const hn = persGroup[gi];
            const savedUndo = undoSave();
            if (matchIdx(pattern, hn, theta, slots)) {
              foundInState = true;
              matchedFact = hn;
              undoDiscard(savedUndo);
              break;
            }
            undoRestore(theta, savedUndo);
          }
          if (foundInState) {
            if (evidenceOut) evidenceOut.push({ goal, method: 'state', fact: matchedFact });
            idx++;
            continue;
          }
        }
      }
    }

    // 3. Clause resolution
    if (calc && calc.clauses && calc.definitions) {
      const externals = collectExternalFreevars(goal, slots);

      const backward = require('../backchain');
      const t0 = PROFILE ? performance.now() : 0;
      const result = backward.prove(goal, calc.clauses, calc.definitions, {
        maxDepth: 50,
        index: calc.backchainIndex,
        buildTerm: !!evidenceOut
      });
      if (PROFILE) {
        profile.proveTime += performance.now() - t0;
        profile.proveCalls++;
      }
      if (result.success) {
        // Reject if prover bound external freevars (unsound — assumed
        // specific values for symbolic constants from forward engine state).
        if (externals && proverBoundExternals(result.theta, externals)) break;

        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) theta[slot] = rt[ri][1];
        }
        if (evidenceOut) evidenceOut.push({ goal, method: 'clause', proof: result, term: result.term });
        idx++;
        continue;
      }
    }
    break;
  }
  return idx;
}

// ─── Compiled Persistent Step Execution ──────────────────────────────

const _ffiIsGround = ffi.convert.isGround;
const _psArgs = [0, 0, 0, 0];
for (const key in _ffiParsedModes) {
  if (_ffiParsedModes[key].length > 4) {
    throw new Error(`FFI '${key}' arity ${_ffiParsedModes[key].length} exceeds _psArgs buffer size 4`);
  }
}

/**
 * Execute a compiled persistent step spec against theta.
 *
 * @param {Object} spec - { ffiFn, argSpecs, arity, multiModal, _slots }
 * @param {Array} theta - Metavar bindings
 * @returns {boolean|null} true (proved), false (definitive failure), null (needs generic fallback)
 */
function executePersistentStep(spec, theta) {
  for (let i = 0; i < spec.arity; i++) {
    const as = spec.argSpecs[i];
    if (as.literal !== undefined) {
      _psArgs[i] = as.literal;
    } else {
      const val = theta[as.slot];
      _psArgs[i] = val !== undefined ? val : as.freevar;
      if (!spec.multiModal && as.isInput &&
          (val === undefined || !_ffiIsGround(val))) {
        return null;
      }
    }
  }

  const result = spec.ffiFn(_psArgs);
  if (result && result.success) {
    const ft = result.theta;
    const specSlots = spec._slots;
    for (let fi = 0; fi < ft.length; fi++) {
      const s = specSlots[ft[fi][0]];
      if (s !== undefined) theta[s] = ft[fi][1];
    }
    return true;
  }
  if (result && !result.success && !result.reason) return false;
  return null;
}

// ─── Compiled Persistent Step Compilation ────────────────────────────

const { isGround } = require('../pattern-utils');

/**
 * Compile a persistent antecedent into a spec for FFI fast path.
 * Returns { ffiFn, argSpecs, arity, multiModal, _slots } or null.
 *
 * true = proved, false = definitive failure, null = needs generic fallback.
 */
function compilePersistentStep(pattern, slots) {
  const pred = getPredicateHead(pattern);
  if (!pred) return null;

  const meta = _ffiMeta[pred];
  if (!meta) return null;

  const ffiFn = ffi.get(meta.ffi);
  if (!ffiFn) return null;

  const modes = _ffiParsedModes[pred];
  const arity = Store.arity(pattern);
  if (arity !== modes.length) return null;

  const multiModal = !!meta.multiModal;

  // Precompute per-position spec
  const argSpecs = new Array(arity);
  for (let i = 0; i < arity; i++) {
    const c = Store.child(pattern, i);
    const slot = slots[c];
    if (slot !== undefined) {
      argSpecs[i] = { slot, freevar: c, isInput: modes[i] === '+' };
    } else if (isGround(c)) {
      argSpecs[i] = { literal: c, isInput: true };
    } else {
      return null;
    }
  }

  return { ffiFn, argSpecs, arity, multiModal, _slots: slots };
}

/**
 * Generate compiled persistent steps for a rule's persistent antecedents.
 * Attaches rule.persistentSteps (array parallel to antecedent.persistent).
 * Called post-compilation by the composition layer (index.js).
 *
 * Used by matchAllLinear (match.js) to skip subApplyIdx + tryFFIDirect
 * overhead for FFI-known predicates (inc, plus, neq, mul).
 */
function compilePersistentSteps(rule) {
  const persistentPats = rule.antecedent.persistent || [];
  if (persistentPats.length === 0) return;

  const slots = rule.metavarSlots;
  const steps = persistentPats.map(p => compilePersistentStep(p, slots));

  // Only attach if at least one step compiled
  if (steps.some(s => s !== null)) {
    rule.persistentSteps = steps;
  }
}

module.exports = {
  tryFFIDirect,
  provePersistentWithFFI,
  executePersistentStep,
  compilePersistentStep,
  compilePersistentSteps,
  ffiParsedModes: _ffiParsedModes,
  getModes: (pred) => _ffiParsedModes[pred] || null,
  getProfile,
  resetProfile,
};
