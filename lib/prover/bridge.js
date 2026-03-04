/**
 * Mode Switch Bridge — backward prover ↔ forward engine.
 *
 * When monad_r fires, ALL linear resources transfer to the forward engine.
 * The engine runs to quiescence and returns residual state.
 * Dormant lolis come back as compound formulas in residualContext.
 */

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

/** Execute mode switch: seq → forward.run() → proof node */
function executeModeSwitch(seq, engineCalc, opts = {}) {
  if (!engineCalc?.forwardRules?.length) return null;

  const initialState = sequentToState(seq);
  const result = forward.run(initialState, engineCalc.forwardRules, {
    maxSteps: opts.maxSteps || 1000,
    trace: true,
    calc: engineCalc
  });

  const residualContext = stateToContext(result.state);
  const proofNode = new ProofTree({
    conclusion: seq, rule: 'monad_r', proven: true, premises: [],
    state: {
      modeSwitch: true, quiescent: result.quiescent,
      steps: result.steps, residualState: result.state, trace: result.trace
    }
  });

  return { proofNode, residualContext, quiescent: result.quiescent };
}

module.exports = { sequentToState, stateToContext, executeModeSwitch };
