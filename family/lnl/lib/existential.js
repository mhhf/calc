/**
 * Existential resolution for LNL forward chaining.
 *
 * Layer: LNL (Linear-Non-Linear)
 *
 * Two resolution regimes after linear matching succeeds:
 *
 *   1. Plain rules — resolve ∃ consequent goals: per-goal compiled FFI step or
 *      provePersistent, then freshEvar for anything left unbound (S0 eager
 *      eigenvariable, TODO_0307). Existentials never block a rule from firing.
 *
 *   2. Fused-block rules (rule.resolutionBody, TODO_0307 P3) — walk the
 *      dataflow-ordered body (ante asks ∪ consequent tells) in ONE
 *      force-or-defer pass. Because the body is topologically ordered, a
 *      consumer always resolves after its producer, so no goal is proved with a
 *      blank input. FORCE = prove (inputs available), bind outputs. DEFER =
 *      fresh eigenvariable (symbolic value). ABORT (return false) = a ground
 *      guard / infeasible constraint that fails (out-of-gas, unsatisfiable
 *      arithmetic) — the match is rejected exactly as the unfused op would be.
 */

import { freshEvar } from '../../../lib/kernel/fresh.js';
import { applyIndexed } from '../../../lib/kernel/substitute.js';
import { EMPTY_MATCH_OPTS } from '../../../lib/engine/match.js';
import Store from '../../../lib/kernel/store.js';
// Reusable 1-element array for single-goal provePersistent calls
const _singleGoal = [0];

/**
 * Collect existential goals in consequent-persistent order.
 * Used as fallback when _existentialGoalOrder is not pre-computed.
 */
function _collectGoals(rule) {
  const goalSet = new Set();
  for (const slot of rule.existentialSlots) {
    const sg = rule.existentialGoals[slot];
    if (sg) for (const g of sg) goalSet.add(g);
  }
  const goals = [];
  for (const p of (rule.consequent.persistent || [])) {
    if (goalSet.has(p)) goals.push(p);
  }
  return goals;
}

/** True iff h contains an unknown — a metavar (unbound slot), an
 *  eigenvariable (deferred symbolic witness), or a freevar (symbolic query
 *  input). Used for the abort test: a forced goal that fails with fully
 *  concrete inputs is a genuine guard/infeasibility; a failure with any
 *  symbolic input is just an uncomputable step and DEFERS. `and(_q1, mask)`
 *  with symbolic sender _q1 defers to a symbolic result — it is not out-of-gas. */
function _hasSymbolic(h) {
  if (typeof h !== 'number') return false;
  const t = Store.tag(h);
  if (t === 'metavar' || t === 'evar' || t === 'freevar') return true;
  if (t === 'arrlit') {
    const es = Store.getArrayElements(h);
    if (es) for (let i = 0; i < es.length; i++) if (_hasSymbolic(es[i])) return true;
    return false;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && _hasSymbolic(c)) return true;
  }
  return false;
}

/**
 * Fused-block body pass (TODO_0307 P3). Walk the dataflow-ordered body in one
 * force-or-defer pass. Returns false iff a ground guard fails (abort).
 */
function _resolveBody(theta, slots, rule, state, calc, matchOpts) {
  const steps = rule.resolutionBody.steps;
  const provePersistent = matchOpts.provePersistent;
  for (let i = 0; i < steps.length; i++) {
    const entry = steps[i];
    const goal = entry.goal;

    // Wildcard guard: a blank metavar in a fixed-direction input position would
    // let tier-1 state lookup match any fact. In correct dataflow order this
    // cannot happen (producers ran first), but appended-unschedulable goals or
    // genuinely-undetermined inputs can leave a slot blank — freshen those
    // input slots to opaque eigenvariables first (evars never wildcard).
    if (!entry.symmetric) {
      for (const s of entry.inSlots) if (theta[s] === undefined) theta[s] = freshEvar();
    }

    let proved = false;
    if (provePersistent) {
      _singleGoal[0] = goal;
      proved = provePersistent(_singleGoal, 0, theta, slots, state, calc, null, matchOpts) === 1;
    }
    if (proved) continue;

    // Force failed. Abort iff the input positions are FULLY CONCRETE (the
    // relation/partial-function genuinely does not hold here — out-of-gas,
    // an unsatisfiable ground constraint). Otherwise the inputs are symbolic:
    // defer (the output is a fresh symbolic value).
    const g = applyIndexed(goal, theta, slots);
    let inputsConcrete = true;
    for (const idx of entry.inputArgIdx) {
      if (_hasSymbolic(Store.child(g, idx))) { inputsConcrete = false; break; }
    }
    if (inputsConcrete) return false;

    for (const s of entry.outSlots) if (theta[s] === undefined) theta[s] = freshEvar();
  }

  // Final sweep over EVERY consequent-reaching var: any still unbound becomes
  // an eigenvariable (symbolic witness), and any bound to a non-ground term
  // after dereference is deferred too (the clause tier can return a non-ground
  // answer — G1). A fired rule then never emits an open pattern slot into a
  // produced fact (doc/def/0046 canonicity).
  for (const slot of rule.resolutionBody.freshenSlots) {
    const v = theta[slot];
    if (v === undefined) { theta[slot] = freshEvar(); continue; }
    if (typeof v === 'number' && _hasSymbolic(v)) {
      const dv = applyIndexed(v, theta, slots);
      if (_hasMetavar(dv)) theta[slot] = freshEvar();
      else theta[slot] = dv;
    }
  }
  return true;
}

/** Metavar-only check (evars are legitimate final values; metavars are not). */
function _hasMetavar(h) {
  if (typeof h !== 'number') return false;
  const t = Store.tag(h);
  if (t === 'metavar') return true;
  if (t === 'evar') return false;
  if (t === 'arrlit') {
    const es = Store.getArrayElements(h);
    if (es) for (let i = 0; i < es.length; i++) if (_hasMetavar(es[i])) return true;
    return false;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && _hasMetavar(c)) return true;
  }
  return false;
}

/**
 * Resolve existential variables in theta after matching.
 *
 * Contract: matchOpts is always the frozen record produced by buildMatchOpts
 * (EMPTY_MATCH_OPTS is the canonical empty default).
 *
 * @param {Array} theta - Metavar bindings (mutated in-place)
 * @param {Object} slots - Hash → slot index mapping
 * @param {Object} rule - Compiled rule
 * @param {Object} state - FactSet-based State object
 * @param {Object|null} calc - { clauses, definitions, backchainIndex }
 * @param {Object} [matchOpts] - Frozen match options
 * @returns {boolean} false iff a fused-block guard failed (abort the match);
 *   plain-rule ∃ resolution always returns true (never blocks)
 */
function resolveEx(theta, slots, rule, state, calc, matchOpts = EMPTY_MATCH_OPTS) {
  // Fused-block rules: the ordered force-or-defer body pass (TODO_0307 P3).
  if (rule.resolutionBody) return _resolveBody(theta, slots, rule, state, calc, matchOpts);

  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return true;

  // Use pre-computed goal order (from compileExChain) or collect on demand
  const goals = rule._existentialGoalOrder || _collectGoals(rule);

  if (goals.length > 0) {
    const chain = rule._compiledExChain;
    const _execExStep = matchOpts.execExStep;
    const useCompiled = chain && _execExStep && matchOpts.useCompiledSteps
      && !matchOpts.onProveSuccess && !matchOpts.onProveFail && !matchOpts.evidence;
    const provePersistent = matchOpts.provePersistent;

    // One loop for every mode (compiled fast path differs only in trying the
    // compiled FFI step first) — modes must not diverge semantically.
    for (let i = 0; i < goals.length; i++) {
      let proved = false;
      const step = useCompiled && i < chain.length ? chain[i] : null;
      if (step && _execExStep(step, theta, slots)) {
        proved = true;
      } else if (provePersistent) {
        _singleGoal[0] = goals[i];
        proved = provePersistent(_singleGoal, 0, theta, slots, state, calc, null, matchOpts) === 1;
      }
      if (!proved) {
        // Eager eigenvariable introduction (TODO_0307): a goal that failed to
        // determine its ∃-outputs freshens them NOW. Later goals then see an
        // opaque evar — never an open pattern slot, which every tier would
        // treat as a wildcard and resolve against an arbitrary stored fact.
        for (const slot of rule.existentialSlots) {
          if (theta[slot] !== undefined) continue;
          const sg = rule.existentialGoals[slot];
          if (sg && sg.includes(goals[i])) theta[slot] = freshEvar();
        }
      }
    }
  }

  // Remaining unbound slots → freshEvar (symbolic witness)
  for (const slot of rule.existentialSlots) {
    if (theta[slot] === undefined) theta[slot] = freshEvar();
  }
  return true;
}

export { resolveEx };
export default { resolveEx };
