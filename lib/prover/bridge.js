/**
 * Mode Switch Bridge — backward prover ↔ forward engine.
 *
 * The bridge implements the polarity shift at monad_r: when the backward prover
 * (negative/async) encounters {S} on the right, it transfers ALL linear resources
 * to the forward engine (positive/sync) which runs to quiescence.
 *
 * This boundary is STRATEGIC, not logical — both sides implement ILL derivation
 * rules. The forward engine is an oracle/strategy for the backward prover,
 * eliminating search. Three execution profiles control the bridge:
 *
 *   'full' (default): forward runs fully, backward sees opaque leaf.
 *     rightFocus verifies residual state matches succedent.
 *     Kernel returns { valid: true, unverified: 'modeSwitch' }.
 *
 *   'guided': forward runs with evidence collection, guidedTerm produces
 *     a complete ILL proof term (copy → loli_l → tensor_r → monad_l chain).
 *     check-term.js verifies every step. No unverified gap.
 *
 *   'off': forward not used, backward searches inside monad (intractable for
 *     large programs). Extracted to TODO_0082.
 *
 * Key data flow:
 *   sequentToState(seq)     → { linear: {hash:count}, persistent: {hash:count} }
 *   forward.run(state, ...) → { state, trace, quiescent, steps }
 *   rightFocus(residual, succedent) → remaining linear (null = failure)
 *   rightFocusTerm(residual, succedent) → { remaining, term } (with proof term)
 */

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';
import { ProofTree } from './pt.js';
import forward from '../engine/forward.js';
import { monadicTerm } from './generic-term.js';
import { guidedTerm } from './ill/guided-term.js';
/** Convert sequent linear → forward linear, cartesian → forward persistent */
function sequentToState(seq) {
  const linear = {}, persistent = {};
  for (const h of Seq.getContext(seq, 'linear'))
    linear[h] = (linear[h] || 0) + 1;
  for (const h of Seq.getContext(seq, 'cartesian'))
    persistent[h] = (persistent[h] || 0) + 1;
  return { linear, persistent };
}

/** Convert forward state back to linear context array */
function stateToContext(state) {
  const formulas = [];
  for (const [h, count] of Object.entries(state.linear || {}))
    for (let i = 0; i < count; i++) formulas.push(Number(h));
  return formulas;
}

/** Check if plain-object linear state is empty */
function linearEmpty(linear) {
  for (const _ in linear) return false;
  return true;
}

/** The ONE bridge proof-node shape (kernel dispatches on state.modeSwitch;
 *  round-15 F1 flags non-termVerified nodes as unverified:'modeSwitch'). */
function bridgeNode(seq, rule, state) {
  return new ProofTree({ conclusion: seq, rule, proven: true, premises: [], state });
}

/**
 * rightFocus — Celf-style synchronous succedent decomposition (verify-only).
 *
 * After the forward engine reaches quiescence, rightFocus verifies that the
 * residual state matches the requested inner succedent S of {S}. Decomposes
 * S against the residual state by walking its type structure:
 *
 *   tensor(A,B) → greedy left-to-right: decompose A, then B on remainder
 *   one         → linear state must be empty
 *   bang(A)     → A must exist in persistent state (not consumed)
 *   atom/pred   → consume one copy from linear state
 *   async types → fail (cannot decompose loli, with, oplus, monad, freevar)
 *
 * Greedy left-to-right is correct because the forward engine only produces
 * ground facts — no metavars, so decomposition is deterministic.
 *
 * This is the verify-only variant (no term construction). For term construction,
 * see rightFocusTerm below. The two share identical branch logic — rightFocusTerm
 * was factored out to avoid the redundant double traversal (10.3 fix).
 *
 * @param {Object} linear  - { hash: count } linear state
 * @param {Object} persistent - { hash: count } persistent state
 * @param {number} hash    - succedent formula hash
 * @param {Object} [roles] - connective role map
 * @returns {Object|null}  remaining linear state, or null on failure
 */
function rightFocus(linear, persistent, hash, roles = {}) {
  if (!Store.isTerm(hash)) return null;
  const tag = Store.tag(hash);

  // Synchronous decomposition via roles
  if (roles.product && tag === roles.product) {
    const r1 = rightFocus(linear, persistent, Store.child(hash, 0), roles);
    if (!r1) return null;
    return rightFocus(r1, persistent, Store.child(hash, 1), roles);
  }
  if (roles.unit && tag === roles.unit) {
    return linearEmpty(linear) ? linear : null;
  }
  if (roles.exponential && tag === roles.exponential) {
    const inner = Store.child(hash, 1);
    return (persistent[inner] > 0) ? linear : null;
  }

  // Async types / unresolved variables — can't rightFocus
  if (tag === 'freevar' || tag === 'metavar') return null;
  // Reject async connectives by role (implication, choices, computation)
  if (tag === roles.implication || tag === roles.externalChoice ||
      tag === roles.internalChoice || tag === roles.computation?.tag) return null;

  // Atom, predicate, any ground term — consume one copy from linear
  const count = linear[hash] || 0;
  if (count <= 0) return null;
  const next = { ...linear };
  if (count === 1) delete next[hash];
  else next[hash] = count - 1;
  return next;
}

/**
 * rightFocusTerm — succedent decomposition with proof term construction.
 *
 * Same logic as rightFocus but also builds a GenericTerm (TODO_0068 §3.3):
 *   tensor(A,B) → tensor_r(rf(A), rf(B))
 *   one         → one_r()
 *   bang(A)     → promotion(id(a))  where a:A in persistent
 *   atom        → id(x)             where x:atom in linear
 *
 * @param {Object} linear  - { hash: count }
 * @param {Object} persistent - { hash: count }
 * @param {number} hash    - succedent formula hash
 * @param {Object} [roles] - connective role map
 * @returns {{ remaining: Object, term: Object }|null}
 */
function rightFocusTerm(linear, persistent, hash, roles = {}) {
  if (!Store.isTerm(hash)) return null;
  const tag = Store.tag(hash);

  // Tensor: tensor_r(rf(left), rf(right))
  if (roles.product && tag === roles.product) {
    const r1 = rightFocusTerm(linear, persistent, Store.child(hash, 0), roles);
    if (!r1) return null;
    const r2 = rightFocusTerm(r1.remaining, persistent, Store.child(hash, 1), roles);
    if (!r2) return null;
    return {
      remaining: r2.remaining,
      term: { rule: 'tensor_r', principal: null, subterms: [r1.term, r2.term] }
    };
  }

  // One: one_r()
  if (roles.unit && tag === roles.unit) {
    if (!linearEmpty(linear)) return null;
    return {
      remaining: linear,
      term: { rule: 'one_r', principal: null, subterms: [] }
    };
  }

  // Bang: promotion(id(a)) where a:A in persistent
  if (roles.exponential && tag === roles.exponential) {
    const inner = Store.child(hash, 1);
    if (!(persistent[inner] > 0)) return null;
    return {
      remaining: linear,
      term: {
        rule: 'promotion', principal: null,
        subterms: [{ rule: 'id', principal: inner, subterms: [] }]
      }
    };
  }

  // Async types / unresolved variables — can't rightFocus
  if (tag === 'freevar' || tag === 'metavar') return null;
  if (tag === roles.implication || tag === roles.externalChoice ||
      tag === roles.internalChoice || tag === roles.computation?.tag) return null;

  // Atom/predicate: id(x) where x consumed from linear
  const count = linear[hash] || 0;
  if (count <= 0) return null;
  const next = { ...linear };
  if (count === 1) delete next[hash];
  else next[hash] = count - 1;
  return {
    remaining: next,
    term: { rule: 'id', principal: hash, subterms: [] }
  };
}

/**
 * Execute mode switch: seq → forward.run() → rightFocus → proof node.
 *
 * This is the single integration point where the execution profile is checked.
 * Everything upstream (inversion, focus, identity, copy) is identical regardless
 * of profile. The profile determines:
 *   - What forward.run options are passed (evidence, terms)
 *   - Whether rightFocus or rightFocusTerm is called
 *   - Whether guidedTerm or monadicTerm constructs the term
 *
 * The returned ProofTree node has state.modeSwitch = true, which kernel.js
 * uses to dispatch monad_r verification.
 */
function modeSwitch(seq, engineCalc, opts = {}, ruleName = null) {
  if (!engineCalc?.forwardRules?.length) return null;

  // Timed calculus (TODO_0265 Phase 6b Stage 2): a GRADED computation over
  // a settle-capable engine reads the succedent grade as the observation
  // horizon — {S}@T means settle(Δ, T), then exact rightFocus of S against
  // the residual timed multiset. Each firing is one @fire instance
  // (THY_0018 §5); success implies settle-reachability AND derivability —
  // a sound, NOT complete oracle (THY_0018 §5 bridge soundness: monad_r
  // subeffecting derives goals no settle run produces). ILL's ungraded
  // monad (gradeIdx null) never enters this branch.
  {
    const comp = engineCalc.roles?.computation;
    if (comp && comp.gradeIdx != null && typeof engineCalc.settle === 'function') {
      return timedSwitch(seq, engineCalc, opts, comp, ruleName);
    }
  }

  const guided = opts.forward === 'guided';
  const initialState = sequentToState(seq);
  const result = forward.run(initialState, engineCalc.forwardRules, {
    maxSteps: opts.maxSteps || 1000,
    trace: true,
    terms: !!opts.terms && !guided,
    evidence: guided,
    calc: engineCalc
  });

  // rightFocus: verify residual state matches inner succedent (body child of
  // the computation node — index from the role record; grade rides along)
  const roles = engineCalc?.roles || {};
  const comp = roles.computation;
  if (!comp) {
    // No silent ILL default (TODO_0274 item 8): a calculus without a
    // computation (monad-category) connective cannot bridge — misrouting
    // here would read the wrong child index on the succedent.
    throw new Error('bridge.modeSwitch: engine calculus has no roles.computation — a computation (monad-category) connective is required for the bridge');
  }
  const innerSucc = Store.child(seq.succedent, comp.bodyIdx);
  const linear = result.state.linear || {};
  const persistent = result.state.persistent || {};

  let rfTerm = null;
  let mTerm = null;
  let termVerified = false;

  if (guided) {
    // Guided profile: rightFocusTerm + guidedTerm → complete ILL proof term.
    // Every forward step becomes copy → loli_l → tensor_r → monad_l in ILL.
    // check-term.js can fully recurse into the evidence — no unverified gap.
    const rfResult = rightFocusTerm(linear, persistent, innerSucc, roles);
    if (!rfResult || !linearEmpty(rfResult.remaining)) return null;
    rfTerm = rfResult.term;
    mTerm = guidedTerm(result.trace || [], rfTerm);
    termVerified = true;
  } else if (opts.terms) {
    // Full profile with terms: rightFocusTerm builds opaque CLF let-chain.
    // Single pass — no redundant rightFocus + rightFocusTerm (10.3 fix).
    const rfResult = rightFocusTerm(linear, persistent, innerSucc, roles);
    if (!rfResult || !linearEmpty(rfResult.remaining)) return null;
    rfTerm = rfResult.term;
    mTerm = monadicTerm(result.trace || [], rfTerm);
    termVerified = true;
  } else {
    // Full profile, no terms: verify-only via rightFocus (zero allocation).
    // Leftover resources after decomposition = proof failure.
    const remaining = rightFocus(linear, persistent, innerSucc, roles);
    if (!remaining || !linearEmpty(remaining)) return null;
  }

  const proofNode = bridgeNode(seq, `${comp.tag}_r`, {
    modeSwitch: true, quiescent: result.quiescent,
    steps: result.steps, residualState: result.state, trace: result.trace,
    rightFocusTerm: rfTerm, monadicTerm: mTerm, termVerified,
    guided: guided || undefined
  });

  return { proofNode, quiescent: result.quiescent };
}

/**
 * timedSwitch — the settle bridge for a graded computation (till).
 *
 * Δ ⊢ {S}@T: transfer Δ to the timed engine (stamped atoms at(A,t) pass
 * through content-addressed; unstamped atoms are stamp 0 by D11), settle
 * to horizon T (the succedent monad grade), then verify the residual
 * timed multiset matches S EXACTLY via rightFocus — the exact-state
 * reading of the executable specs' gates. A non-stamp grade (metavar, ω)
 * makes the rule inapplicable, not an error. Verify-only in v1: the
 * evidence is the settle event trace; guided terms for timed traces are
 * a recorded residue (rides serialize-trace / 4c).
 */
function timedSwitch(seq, engineCalc, opts, comp, ruleName) {
  const horizon = Store.child(seq.succedent, comp.gradeIdx);
  const initialState = sequentToState(seq);
  let result;
  try {
    result = engineCalc.settle(initialState, { stamp: horizon }, opts.settleOpts || {});
  } catch (e) {
    // ground-grade fence: an unparseable horizon = rule inapplicable
    if (/parseStamp/.test(e?.message || '')) return null;
    throw e;
  }

  const roles = engineCalc.roles || {};
  const innerSucc = Store.child(seq.succedent, comp.bodyIdx);

  // Ambient law A ⊣⊢ A@0 (THY_0018 §5, D11): the engine may stamp an
  // untouched atom at 0 where the succedent writes it bare (or vice
  // versa). Canonicalize BOTH sides to the stripped form before the
  // exact rightFocus — hash-level, algebra-agnostic (the zero stamp is
  // the effect unit of the engine's own timed config).
  const zero = engineCalc.timedConfig?.effect?.unit?.();   // public timed-config record
  const canon = (h) =>
    (zero != null && Store.tag(h) === 'at' && Store.child(h, 1) === zero)
      ? Store.child(h, 0) : h;
  const canonState = (m) => {
    const out = {};
    for (const [k, c] of Object.entries(m || {})) {
      const h = canon(Number(k));
      out[h] = (out[h] || 0) + c;
    }
    return out;
  };
  const canonSucc = (h) => {
    if (roles.product && Store.tag(h) === roles.product) {
      const a = canonSucc(Store.child(h, 0));
      const b = canonSucc(Store.child(h, 1));
      return Store.put(roles.product, [a, b]);
    }
    return canon(h);
  };

  const remaining = rightFocus(canonState(result.state.linear),
    canonState(result.state.persistent), canonSucc(innerSucc), roles);
  if (!remaining || !linearEmpty(remaining)) return null;

  const proofNode = bridgeNode(seq, ruleName || `${comp.tag}_r`, {
    modeSwitch: true, quiescent: true,
    steps: result.events?.length ?? 0, residualState: result.state,
    trace: result.events || [],
    rightFocusTerm: null, monadicTerm: null, termVerified: false,
  });
  return { proofNode, quiescent: true };
}

export { sequentToState, stateToContext, rightFocus, rightFocusTerm, modeSwitch };
export default { sequentToState, stateToContext, rightFocus, rightFocusTerm, modeSwitch };
