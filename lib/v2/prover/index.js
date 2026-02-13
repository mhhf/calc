/**
 * v2 Prover API
 *
 * Convenience re-exports from the prover lasagne layers.
 * Uses L4a auto strategy by default for backward proof search.
 */

const auto = require('./strategy/auto');

module.exports = {
  create: auto.create,
  prove: auto.prove,
};
