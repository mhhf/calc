/**
 * Compiled persistent steps — FFI fast path for persistent antecedents.
 *
 * Precomputes per-persistent-antecedent closures that bypass the generic
 * subApplyIdx → tryFFIDirect path. Each step directly calls the FFI function
 * with pre-resolved argument specs.
 *
 * Re-exports from compile.js and match.js.
 */

const { compilePersistentStep, compilePersistentSteps } = require('../compile');
const { executePersistentStep } = require('../match');

module.exports = {
  compilePersistentStep,
  compilePersistentSteps,
  executePersistentStep,
};
