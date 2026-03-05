/**
 * Mode Switch Bridge — backward prover ↔ forward engine.
 *
 * When monad_r fires, ALL linear resources transfer to the forward engine.
 * The engine runs to quiescence and returns residual state.
 * rightFocus then decomposes the succedent against the residual state.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { ProofTree } = require('./pt');
const forward = require('../engine/forward');

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

/**
 * rightFocus — Celf-style succedent decomposition.
 *
 * Decomposes a synchronous type S against the residual forward state.
 * Returns remaining linear state on success, null on failure.
 * Persistent state is pass-through (not consumed).
 *
 * Greedy left-to-right: correct for ground formulas (deterministic matching).
 *
 * @param {Object} linear  - { hash: count } linear state
 * @param {Object} persistent - { hash: count } persistent state
 * @param {number} hash    - succedent formula hash
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
    const inner = Store.child(hash, 0);
    return (persistent[inner] > 0) ? linear : null;
  }

  // Async types / unresolved variables — can't rightFocus
  if (tag === 'freevar') return null;
  // Reject async connectives by role (implication, choices, computation)
  if (tag === roles.implication || tag === roles['external-choice'] ||
      tag === roles['internal-choice'] || tag === roles.computation) return null;

  // Atom, predicate, any ground term — consume one copy from linear
  const count = linear[hash] || 0;
  if (count <= 0) return null;
  const next = { ...linear };
  if (count === 1) delete next[hash];
  else next[hash] = count - 1;
  return next;
}

/** Execute mode switch: seq → forward.run() → rightFocus → proof node */
function executeModeSwitch(seq, engineCalc, opts = {}) {
  if (!engineCalc?.forwardRules?.length) return null;

  const initialState = sequentToState(seq);
  const result = forward.run(initialState, engineCalc.forwardRules, {
    maxSteps: opts.maxSteps || 1000,
    trace: true,
    calc: engineCalc
  });

  // rightFocus: verify residual state matches inner succedent
  const innerSucc = Store.child(seq.succedent, 0);
  const roles = engineCalc?.roles || {};
  const remaining = rightFocus(
    result.state.linear || {},
    result.state.persistent || {},
    innerSucc,
    roles
  );
  // rightFocus failed or leftover resources → proof fails
  if (!remaining || !linearEmpty(remaining)) return null;

  const proofNode = new ProofTree({
    conclusion: seq, rule: 'monad_r', proven: true, premises: [],
    state: {
      modeSwitch: true, quiescent: result.quiescent,
      steps: result.steps, residualState: result.state, trace: result.trace
    }
  });

  return { proofNode, quiescent: result.quiescent };
}

module.exports = { sequentToState, stateToContext, rightFocus, executeModeSwitch };
