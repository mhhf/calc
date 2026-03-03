/**
 * Fingerprint optimization — O(1) rule lookup via discriminator value.
 *
 * Fingerprinting detects a dominant discriminator predicate in rules
 * (e.g., code(PC, OPCODE)) and builds a secondary index for O(1) lookup
 * by ground value (opcode). Combined with a pointer predicate (e.g., pc(PC))
 * this enables O(1) rule selection.
 *
 * Re-exports from match.js and strategy.js for clean opt/ separation.
 */

const {
  detectFingerprintConfig,
  findFingerprintValue,
  buildDiscriminatorIndex,
} = require('../match');

const {
  makeFingerprintLayer,
  attachPredictions,
} = require('../strategy');

const { buildFingerprintIndex } = require('../forward');

module.exports = {
  detectFingerprintConfig,
  findFingerprintValue,
  buildDiscriminatorIndex,
  makeFingerprintLayer,
  attachPredictions,
  buildFingerprintIndex,
};
