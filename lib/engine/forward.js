/**
 * Forward Chaining Engine — execution and main loop.
 *
 * Applies matches and runs the committed-choice main loop.
 * Matching is in match.js, strategy in strategy.js.
 *
 * State: FactSet-based State object (lib/engine/fact-set.js).
 * Public API accepts/returns plain { linear: {hash:count}, persistent: {hash:true} }
 * objects for backward compatibility.
 *
 * Architecture:
 *   compile.js   — rule preparation (compileRule)
 *   match.js     — pattern matching + persistent proving
 *   strategy.js  — rule selection (fingerprint, disc-tree, predicate)
 *   forward.js   — execution + main loop (applyMatch, run)
 *   explore.js   — exhaustive DFS exploration + mutation/undo
 */

import Store from '../kernel/store.js';
import { compileRule } from './compile.js';
import strategy from './strategy.js';
import { clearBWCache } from './backward-cache.js';
import { fromObject, toObject } from './fact-set.js';
import { consume, produce, producePers } from './state-ops.js';
import { EqNeqSolver } from './constraint.js';
import { satFilter } from './constraint.js';
import { EMPTY_MATCH_OPTS } from './match.js';
// ─── Apply Match ────────────────────────────────────────────────────

/**
 * Apply match result: consume resources, produce new ones.
 * Mutates state in-place (committed-choice: no backtracking needed).
 * Caller must invalidate secondary indices (_byKey) after mutation.
 */
function applyMatchInPlace(state, { rule, theta, slots, consumed, optimized }) {
  consume(state.linear, consumed, null);
  produce(state.linear, rule.consequent.linear || [], theta, slots, rule, optimized, null);
  producePers(state.persistent, rule.consequent.persistent || [], theta, slots, rule, null);
  // Invalidate secondary index (will be rebuilt next iteration if needed)
  state._byKey = null;
}

// ─── Main Loop ──────────────────────────────────────────────────────

/** Run forward chaining until quiescence */
function run(inputState, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const terms = opts.terms || false;
  const evidence = opts.evidence || false;
  const calc = opts.calc || null;
  const onStep = opts.onStep || null;
  // Tabling soundness: the backward cache maps (pred, inputs) → outputs.
  // This is sound because persistent context is monotonically growing during
  // forward execution — cached successes remain valid. We clear at run start
  // because a new run may have a different initial persistent context, making
  // prior cached failures stale (a previously-unprovable goal may now succeed).
  clearBWCache();
  let steps = 0;
  let solver = null; // Lazy EqNeqSolver for multi-alt rules

  // Accept both plain objects and State objects
  let state = inputState.linear && inputState.linear.group
    ? inputState  // Already a State object
    : fromObject(inputState.linear || {}, inputState.persistent || {});

  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  // Window guards need the timed matcher — the untimed engine would fire
  // such rules UNGUARDED (silently wrong). Fail loud (TODO_0265 Phase 4).
  _rejectWindowRules(ruleList);
  // Rule-selection strategy: ONE channel (RES_0143 F2) — the engine
  // context's profile-honoring factory (memoized per rule list), an
  // explicit opts.strategy, or the layer-free fallback for direct callers.
  const eng = opts.engine || null;
  const fwdStrategy = opts.strategy
    || (eng && eng.buildStrategy ? eng.buildStrategy(ruleList) : strategy.bareStrategy(ruleList));
  const fpConfig = fwdStrategy.fpConfig || null;
  // Inject domain-specific lookupArrayValue for virtual fingerprint dispatch
  const _domCfg = calc?.domainConfig || null;
  if (fpConfig && !fpConfig.lookupArrayValue && _domCfg?.lookupArrayValue) {
    fpConfig.lookupArrayValue = _domCfg.lookupArrayValue;
  }
  const indexedRules = { rules, strategy: fwdStrategy, fpConfig };
  const matchOpts = opts.matchOpts || EMPTY_MATCH_OPTS;

  // Build fingerprint secondary index on initial state (skip for virtual —
  // uses ARRAY_TABLE). The builder rides fpConfig (opt/fingerprint.js,
  // RES_0143 M5) — no fingerprint machinery in the generic loop.
  if (fpConfig && fpConfig.type !== 'virtual' && fpConfig.buildIndex) {
    state._fpPred = fpConfig.pred;
    state._fpKeyPos = fpConfig.keyPos;
    fpConfig.buildIndex(state, fpConfig);
  }

  while (steps < maxSteps) {
    // Rebuild _byKey for new state (in case code facts changed)
    if (fpConfig && fpConfig.type !== 'virtual' && fpConfig.buildIndex && !state._byKey) {
      state._fpPred = fpConfig.pred;
      state._fpKeyPos = fpConfig.keyPos;
      fpConfig.buildIndex(state, fpConfig);
    }

    let m = strategy.findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      return { state: toObject(state), quiescent: true, steps, trace };
    }
    // Three trace levels, gated by flags to avoid allocation in the hot path:
    //   evidence=true (guided profile): full rule object, theta snapshot, slots,
    //     per-persistent-goal evidence, loliHash — everything guidedTerm needs.
    //     theta.slice() is the ONLY allocation overhead in the hot loop — theta is
    //     a mutable array reused across matches, so we must snapshot it.
    //   terms=true (full profile with terms): rule name + consumed facts for
    //     monadicTerm's opaque CLF let-chain.
    //   default: string trace for debugging ("[0] rule_name").
    // Multi-alt consequent: SAT-filter alternatives, pick the survivor.
    // Must happen BEFORE trace recording so trace.rule.consequent matches the
    // actual alt used for state transition.
    if (m.rule.consequentAlts && m.rule.consequentAlts.length > 1) {
      if (!solver) solver = new EqNeqSolver({ evalNumeric: _domCfg?.evalNumeric, predNames: _domCfg?.constraintPreds });
      const satAlts = satFilter(solver, m.rule.consequentAlts, m.theta, m.slots);
      if (satAlts.length >= 1 && satAlts[0] !== 0) {
        const alt = m.rule.consequentAlts[satAlts[0]];
        // Null compiled-sub caches (indexed for alt[0]). Keep preserved/optimized intact.
        m = { ...m, rule: { ...m.rule, consequent: alt,
          compiledConseqLinear: null, compiledConseqPersistent: null } };
      }
    }
    if (trace) {
      if (evidence) {
        trace.push({
          rule: m.rule,
          consumed: { ...m.consumed },
          theta: m.theta.slice(),
          slots: m.slots,
          persistentEvidence: m.persistentEvidence || [],
          loliHash: m.loliHash || null
        });
      } else if (terms) {
        trace.push({ rule: m.rule.name, consumed: { ...m.consumed } });
      } else {
        trace.push(`[${steps}] ${m.rule.name}`);
      }
    }
    applyMatchInPlace(state, m);
    steps++;
    if (onStep) onStep({
      step: steps, rule: m.rule,
      consumed: { ...m.consumed }, theta: m.theta.slice(),
      slots: m.slots, state
    });
  }

  return { state: toObject(state), quiescent: false, steps, trace };
}

/** @param {Object} [linearPolicy] - FactSet index policy for the linear zone
 *  (till: groupKey/cmp — see fact-set.js; absent ⇒ default layout) */
function createState(linear = {}, persistent = {}, linearPolicy) {
  return fromObject(linear, persistent, linearPolicy);
}

/** Reject rules this engine cannot execute faithfully. Compilation marks
 *  any rule whose features need a scheduler layer (compile.js sets
 *  `requiresScheduler` to a human reason — window guards, duration
 *  grades, counted parcels, weighted choice); firing such a rule here
 *  would silently ignore those semantics. The FEATURE VOCABULARY lives
 *  in compile.js's grade-gated sections, not here (RES_0143 L9). */
function _rejectWindowRules(ruleList) {
  for (const r of ruleList) {
    if (r.requiresScheduler) {
      throw new Error(`Rule '${r.name}' carries ${r.requiresScheduler} — this requires the timed matcher (calc.settle, TODO_0265 Phase 4); the untimed engine would ignore it`);
    }
  }
}

export { compileRule, run, createState, _rejectWindowRules };
export default { compileRule, run, createState };
