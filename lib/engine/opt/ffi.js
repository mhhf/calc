/**
 * FFI optimization for persistent proving.
 *
 * Extracts the FFI-first persistent proving path from match.js.
 * When enabled, persistent goals try FFI before state lookup and clause
 * resolution. When disabled, only state lookup → clause resolution.
 */

const Store = require('../../kernel/store');
const { isPredTag, predHead, extFV, boundExt } = require('../../kernel/ast');
const { matchIndexed: matchIdx, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed: subApplyIdx } = require('../../kernel/substitute');
const { isGround } = require('../pattern-utils');
const backward = require('../backchain');
const { tryCCDispatch: _tryCCDispatch } = require('./compiled-clauses');
const { EMPTY_MATCH_OPTS, tryStateLookup, PROVE_METHOD } = require('../match');

const PROFILE = typeof process !== 'undefined' && process.env.CALC_PERF_PROFILE === '1';

// ─── FFI Direct Bypass ──────────────────────────────────────────────

const _FFI_MAX_ARITY = 5;
const _ffiArgs = [0, 0, 0, 0, 0];

/** Validate all FFI predicate arities fit the fixed-size args buffer. */
function _validateArity(parsedModes) {
  for (const key in parsedModes) {
    if (parsedModes[key].length > _FFI_MAX_ARITY) {
      throw new Error(`FFI '${key}' arity ${parsedModes[key].length} exceeds _FFI_MAX_ARITY ${_FFI_MAX_ARITY} — increase buffer`);
    }
  }
}

/** Try FFI directly, bypassing full prove() machinery.
 * All FFI params must be provided; returns null when absent. */
function ffiDirect(goal, ffiMeta, ffiGet, parsedModes, ffiIsGround) {
  if (!ffiMeta) return null;  // No FFI context — skip optimization
  const goalTag = Store.tag(goal);
  if (!goalTag) return null;

  let head;
  if (isPredTag(goalTag)) head = goalTag;
  else if (goalTag === 'atom') head = Store.child(goal, 0);
  else return null;

  const meta = ffiMeta[head];
  if (!meta) return null;
  const fn = ffiGet(meta.ffi);
  if (!fn) return null;

  const modes = parsedModes[head];
  const goalArity = Store.arity(goal);
  if (goalArity !== modes.length) return null;

  for (let i = 0; i < goalArity; i++) {
    const c = Store.child(goal, i);
    if (!meta.multiModal && modes[i] === '+' && !ffiIsGround(c)) return null;
    _ffiArgs[i] = c;
  }

  const result = fn(_ffiArgs);
  if (result && !result.success && result.reason) return null;
  return result;
}

// ─── FFI-enhanced Persistent Proving ─────────────────────────────────

let profile = {
  proveTime: 0, proveCalls: 0,
  // Per-tier counters (PROFILE-gated)
  ffiCalls: 0, ffiTime: 0,
  stateCalls: 0, stateTime: 0,
  compiledCalls: 0, compiledTime: 0,
  clauseCalls: 0, clauseTime: 0,
  failCalls: 0,
  // Per-predicate breakdown: { predName: { ffi, state, compiled, clause, fail } }
  byPredicate: {},
};

function getProfile() { return profile; }
function resetProfile() {
  profile.proveTime = profile.proveCalls = 0;
  profile.ffiCalls = profile.ffiTime = 0;
  profile.stateCalls = profile.stateTime = 0;
  profile.compiledCalls = profile.compiledTime = 0;
  profile.clauseCalls = profile.clauseTime = 0;
  profile.failCalls = 0;
  profile.byPredicate = {};
}

/**
 * Prove persistent antecedent patterns with tiered resolution:
 *   1. State lookup — match against persistent facts in state.persistent
 *   2. FFI — O(1) arithmetic (inc, plus, neq, mul, etc.)
 *   3. Compiled clause — Tier 1/2 zero-subgoal direct lookup
 *   4. Full clause resolution — backward chaining via backchain.js
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
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts. EMPTY_MATCH_OPTS is the canonical empty default.
 *
 * @param {number[]} patterns - Persistent antecedent pattern hashes
 * @param {number} startIdx - Index to start proving from
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {State} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, types, backchainIndex } or null
 * @param {Array|null} evidenceOut - When non-null, pushes per-goal evidence
 *   { goal, method: 'state'|'ffi'|'clause', fact?, proof? }
 * @param {Object} [matchOpts] - Frozen match options (defaults to EMPTY_MATCH_OPTS)
 * @returns {number} Index of first unproved pattern (=== patterns.length if all proved)
 */
function _profileHit(method, goal) {
  const pred = predHead(goal) || 'unknown';
  const bp = profile.byPredicate;
  if (!bp[pred]) bp[pred] = { ffi: 0, state: 0, compiled: 0, clause: 0, fail: 0 };
  bp[pred][method]++;
}

function proveWithFFI(patterns, startIdx, theta, slots, state, calc, evidenceOut, matchOpts = EMPTY_MATCH_OPTS) {
  // D2: extract FFI context from matchOpts at function entry (V8 IC-friendly locals)
  const ffiMeta = matchOpts.ffiMeta;
  const ffiGet = matchOpts.ffiGet;
  const parsedModes = matchOpts.ffiParsedModes;
  const ffiIsGround = matchOpts.ffiIsGround;
  const onProveSuccess = matchOpts.onProveSuccess;
  const onProveFail = matchOpts.onProveFail;
  let idx = startIdx;
  while (idx < patterns.length) {
    const _t0 = PROFILE ? performance.now() : 0;
    const goal = subApplyIdx(patterns[idx], theta, slots);

    // Detect non-groundness for profiling hooks
    let _hasFfi = false, _isGround = true;
    if (onProveSuccess) {
      const head = predHead(goal);
      if (head && ffiMeta[head]) {
        _hasFfi = true;
        const modes = parsedModes[head];
        const arity = Store.arity(goal);
        for (let i = 0; i < arity && i < modes.length; i++) {
          if (!ffiMeta[head].multiModal && modes[i] === '+' && !isGround(Store.child(goal, i))) {
            _isGround = false;
            break;
          }
        }
      }
    }

    // 1. State lookup (cheapest — array scan, shared primitive)
    {
      const pattern = patterns[idx];
      const matchedFact = tryStateLookup(pattern, theta, slots, state);
      if (matchedFact !== null) {
        if (PROFILE) { profile.stateCalls++; profile.stateTime += performance.now() - _t0; _profileHit('state', goal); }
        // Goal reported post-unification; payload uniform across all provers.
        const provedGoal = subApplyIdx(pattern, theta, slots);
        if (evidenceOut) evidenceOut.push({ goal: provedGoal, method: PROVE_METHOD.STATE, fact: matchedFact });
        if (onProveSuccess) onProveSuccess(provedGoal, PROVE_METHOD.STATE, { ground: true, hasFfi: false });
        idx++;
        continue;
      }
    }

    // 2. FFI direct (arithmetic predicates — fastest for ground inputs)
    const ffiResult = ffiDirect(goal, ffiMeta, ffiGet, parsedModes, ffiIsGround);
    if (ffiResult) {
      if (ffiResult.success) {
        const ft = ffiResult.theta;
        let ffiOk = true;
        for (let fi = 0; fi < ft.length; fi++) {
          const slot = slots[ft[fi][0]];
          if (slot !== undefined) {
            theta[slot] = ft[fi][1];
          } else {
            if (ft[fi][1] !== ft[fi][0]) {
              if (isGround(ft[fi][0])) {
                ffiOk = false; break;
              }
              const savedUndo = undoSave();
              if (matchIdx(ft[fi][0], ft[fi][1], theta, slots)) {
                undoDiscard(savedUndo);
              } else {
                undoRestore(theta, savedUndo);
                ffiOk = false; break;
              }
            }
          }
        }
        if (ffiOk) {
          if (PROFILE) { profile.ffiCalls++; profile.ffiTime += performance.now() - _t0; _profileHit('ffi', goal); }
          if (evidenceOut) evidenceOut.push({ goal, method: PROVE_METHOD.FFI });
          if (onProveSuccess) onProveSuccess(goal, PROVE_METHOD.FFI, { ground: true, hasFfi: true });
          idx++;
          continue;
        }
        // FFI computed but output mismatches — definitive failure
        if (onProveFail) onProveFail(goal, 'ffi_mismatch');
        break;
      }
      // FFI advisory failure — fall through to compiled/clause resolution
    }

    // 3. Compiled clause dispatch (structural predicates — compiled from ILL clauses)
    if (calc && calc.clauseDispatch) {
      const _t1 = PROFILE ? performance.now() : 0;
      const ccResult = _tryCCDispatch(
        calc.clauseDispatch, goal, slots, theta,
        matchOpts.canonicalize,
        calc.theoryLookup || null,
        matchOpts.ffiParsedModes
      );
      if (ccResult === true) {
        if (PROFILE) { profile.compiledCalls++; profile.compiledTime += performance.now() - _t1; _profileHit('compiled', goal); }
        if (evidenceOut) evidenceOut.push({ goal, method: PROVE_METHOD.COMPILED });
        if (onProveSuccess) onProveSuccess(goal, PROVE_METHOD.COMPILED, { ground: _isGround, hasFfi: _hasFfi });
        idx++;
        continue;
      }
    }

    // 4. Clause resolution (full backward chaining fallback)
    if (calc && calc.clauses && calc.definitions) {
      const externals = extFV(goal, slots);

      const t0 = PROFILE ? performance.now() : 0;
      const result = backward.prove(goal, calc.clauses, calc.definitions, {
        ...(calc.backwardOpts || {}),
        maxDepth: 20000,
        index: calc.backchainIndex,
        buildTerm: !!evidenceOut
      });
      if (PROFILE) {
        profile.proveTime += performance.now() - t0;
        profile.proveCalls++;
      }
      if (result.success) {
        if (externals && boundExt(result.theta, externals)) {
          if (PROFILE) { profile.failCalls++; _profileHit('fail', goal); }
          if (onProveFail) onProveFail(goal, 'external_binding');
          break;
        }

        const rt = result.theta;
        for (let ri = 0; ri < rt.length; ri++) {
          const slot = slots[rt[ri][0]];
          if (slot !== undefined) theta[slot] = rt[ri][1];
        }
        if (PROFILE) { profile.clauseCalls++; profile.clauseTime += performance.now() - _t0; _profileHit('clause', goal); }
        if (evidenceOut) evidenceOut.push({ goal, method: PROVE_METHOD.CLAUSE, proof: result, term: result.term });
        if (onProveSuccess) onProveSuccess(goal, PROVE_METHOD.CLAUSE, { ground: _isGround, hasFfi: _hasFfi });
        idx++;
        continue;
      }
    }
    if (PROFILE) { profile.failCalls++; _profileHit('fail', goal); }
    if (onProveFail) onProveFail(goal, 'exhausted', { ground: _isGround, hasFfi: _hasFfi });
    break;
  }
  return idx;
}

// ─── Compiled Persistent Step Execution ──────────────────────────────

const _psArgs = [0, 0, 0, 0, 0];

/**
 * Execute a compiled persistent step spec against theta.
 *
 * @param {Object} spec - FFI spec or compiled-clause spec
 * @param {Array} theta - Metavar bindings
 * @returns {boolean|null} true (proved), false (definitive failure), null (needs generic fallback)
 */
function execPS(spec, theta) {
  // Compiled clause spec — resolve goal via tryCCDispatch
  if (spec._compiled) {
    const goal = subApplyIdx(spec._pattern, theta, spec._slots);
    const result = _tryCCDispatch(
      spec._dispatch, goal, spec._slots, theta,
      spec._canonicalize, spec._theories, spec._parsedModes);
    return result === true ? true : null;
  }
  // FFI spec —
  for (let i = 0; i < spec.arity; i++) {
    const as = spec.argSpecs[i];
    if (as.literal !== undefined) {
      _psArgs[i] = as.literal;
    } else if (as.pattern !== undefined) {
      _psArgs[i] = as.pattern;
    } else {
      const val = theta[as.slot];
      _psArgs[i] = val !== undefined ? val : as.freevar;
      if (!spec.multiModal && as.isInput &&
          (val === undefined || !spec._ffiIsGround(val))) {
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
      if (s !== undefined) {
        theta[s] = ft[fi][1];
      } else {
        // Output not a known slot — ground literal or structured pattern
        if (ft[fi][1] !== ft[fi][0]) {
          if (isGround(ft[fi][0])) return false;
          // Structured pattern — unify FFI result against pattern
          const savedUndo = undoSave();
          if (matchIdx(ft[fi][0], ft[fi][1], theta, spec._slots)) {
            undoDiscard(savedUndo);
          } else {
            undoRestore(theta, savedUndo);
            return false;
          }
        }
      }
    }
    return true;
  }
  if (result && !result.success && !result.reason) return false;
  return null;
}

// ─── Compiled Persistent Step Compilation ────────────────────────────

/**
 * Compile a persistent antecedent into a spec for the fast path.
 * Returns FFI spec, compiled-clause spec, or null.
 *
 * @param {number} pattern - Persistent antecedent pattern hash
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object|null} calcContext - { clauseDispatch, theoryLookup } for compiled clause fallback
 * @param {Object|null} ffiContext - { meta, parsedModes, get, isFFIGround } — injected FFI config
 * @returns {Object|null}
 */
function compilePS(pattern, slots, calcContext, ffiContext) {
  // FFI context required — orchestrator always provides it
  if (!ffiContext) return null;
  const _meta = ffiContext.meta;
  const _get = ffiContext.get;
  const _modes = ffiContext.parsedModes;
  const _isGr = ffiContext.isFFIGround;
  const pred = predHead(pattern);
  if (!pred) return null;

  // 1. Try FFI spec
  const meta = _meta[pred];
  if (meta && meta.ffi) {
    const ffiFn = _get(meta.ffi);
    if (ffiFn) {
      const modes = _modes[pred];
      const arity = Store.arity(pattern);
      if (arity === modes.length) {
        const multiModal = !!meta.multiModal;
        const argSpecs = new Array(arity);
        for (let i = 0; i < arity; i++) {
          const c = Store.child(pattern, i);
          const slot = slots[c];
          if (slot !== undefined) {
            argSpecs[i] = { slot, freevar: c, isInput: modes[i] === '+' };
          } else if (isGround(c)) {
            argSpecs[i] = { literal: c, isInput: true };
          } else {
            argSpecs[i] = { pattern: c, isInput: false };
          }
        }
        return { ffiFn, argSpecs, arity, multiModal, _slots: slots, _ffiIsGround: _isGr };
      }
    }
  }

  // 2. Try compiled clause spec (for predicates without FFI but with compiled dispatch)
  if (calcContext && calcContext.clauseDispatch) {
    const modes = _modes[pred];
    if (modes && (calcContext.clauseDispatch[pred] ||
        (calcContext.clauseDispatch._tier2 && calcContext.clauseDispatch._tier2[pred]) ||
        (calcContext.clauseDispatch._tier3 && calcContext.clauseDispatch._tier3[pred]))) {
      return {
        _compiled: true,
        _pattern: pattern,
        _slots: slots,
        _dispatch: calcContext.clauseDispatch,
        _theories: calcContext.theoryLookup || null,
        _parsedModes: _modes,
        _canonicalize: null,
      };
    }
  }

  return null;
}

module.exports = {
  ffiDirect,
  proveWithFFI,
  execPS,
  compilePS,
  getProfile,
  resetProfile,
  _validateArity,
};
