/**
 * Fingerprint optimization — O(1) rule lookup via discriminator value.
 *
 * Fingerprinting detects a dominant discriminator predicate in rules
 * (e.g., code(PC, OPCODE)) and builds a secondary index for O(1) lookup
 * by ground value (opcode). Combined with a pointer predicate (e.g., pc(PC))
 * this enables O(1) rule selection.
 *
 * Re-exports the surface consumed by the composition root (index.js).
 */

import { fpDetect } from '../match.js';
import { fpLayer, attachPred } from '../strategy.js';
export { fpDetect, fpLayer, attachPred };
export default { fpDetect, fpLayer, attachPred };
