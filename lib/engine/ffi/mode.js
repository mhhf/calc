/**
 * Mode Checking for FFI
 *
 * Modes determine when FFI can be used:
 * - '+' = ground input (no metavariables)
 * - '-' = computed output (will be unified with result)
 */

const { isGround } = require('./convert');

/**
 * Parse mode specification string (cached)
 * @param {string} modeStr - e.g., "+ + -"
 * @returns {Array<'+'|'-'>}
 */
const _modeCache = {};
function parseMode(modeStr) {
  let cached = _modeCache[modeStr];
  if (cached) return cached;
  cached = modeStr.trim().split(/\s+/);
  _modeCache[modeStr] = cached;
  return cached;
}

/**
 * Check if arguments match mode specification
 * @param {number[]} args - Term hashes
 * @param {string} modeStr - Mode specification
 * @returns {boolean}
 */
function checkMode(args, modeStr) {
  const modes = parseMode(modeStr);

  if (args.length !== modes.length) {
    return false;
  }

  for (let i = 0; i < args.length; i++) {
    if (modes[i] === '+' && !isGround(args[i])) {
      return false;
    }
  }

  return true;
}

module.exports = { parseMode, checkMode };
