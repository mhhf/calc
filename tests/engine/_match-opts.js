/**
 * Test helper: build a factory-produced matchOpts from a flat options bag.
 *
 * Purpose: enforce the "no ad-hoc matchOpts" invariant (S8) in tests.
 * Instead of writing `matchLoli(h, state, null, { connectives: rc })` with
 * a bare object, tests use `matchLoli(h, state, null, makeMatchOpts({ rc }))`.
 * This guarantees the frozen 20-field shape via buildMatchOpts.
 *
 * Not exported from lib/ — tests only. Production code wires matchOpts at
 * the composition root (lib/engine/index.js).
 */

import { buildGenericProtocol, buildFamilyProtocol, buildOptProtocol, buildFfiProtocol, buildMatchOpts } from '../../lib/engine/match.js';
/**
 * @param {Object} [opts]
 * @param {Object} [opts.rc]               - Resolved connective table
 * @param {boolean} [opts.evidence]        - Collect evidence
 * @param {Function} [opts.onProveSuccess]
 * @param {Function} [opts.onProveFail]
 * @param {Function} [opts.canonicalize]
 * @param {Function} [opts.provePersistent] - Override prover
 * @param {Function} [opts.matchDynamicRule]
 * @param {Function} [opts.resolveEx]
 * @param {Function} [opts.drainDynamicRules]
 * @param {boolean} [opts.backchainUseFFI]
 * @param {boolean} [opts.useCompiledSteps]
 * @param {Function} [opts.execPS]
 * @param {Function} [opts.execExStep]
 * @param {Function} [opts.tryCCDispatch]
 * @param {Object} [opts.ffi]              - { parsedModes, meta, get, isFFIGround }
 */
function makeMatchOpts(opts = {}) {
  return buildMatchOpts({
    ...buildGenericProtocol({
      optimizePreserved: opts.optimizePreserved,
      evidence: opts.evidence,
      canonicalize: opts.canonicalize,
      onProveFail: opts.onProveFail,
      onProveSuccess: opts.onProveSuccess,
      provePersistent: opts.provePersistent,
    }),
    ...buildFamilyProtocol({
      matchDynamicRule: opts.matchDynamicRule,
      resolveEx: opts.resolveEx,
      drainDynamicRules: opts.drainDynamicRules,
      rc: opts.rc,
      backchainUseFFI: opts.backchainUseFFI,
    }),
    ...buildOptProtocol({
      execPS: opts.execPS,
      execExStep: opts.execExStep,
      tryCCDispatch: opts.tryCCDispatch,
      useCompiledSteps: opts.useCompiledSteps,
    }),
    ...buildFfiProtocol(opts.ffi || null),
  });
}

export { makeMatchOpts };
export default { makeMatchOpts };
