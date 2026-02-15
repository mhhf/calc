/**
 * Binary ↔ BigInt Conversion for FFI
 *
 * Compact form: binlit stores BigInt directly in 1 node.
 * Flat form: e = 0, i(X) = 2*X + 1, o(X) = 2*X (for pattern matching).
 *
 * FFI always produces binlit for O(1) storage.
 */

const Store = require('../../kernel/store');

/**
 * Convert binary term to BigInt
 * Handles both binlit (compact) and legacy recursive form
 * @param {number} h - Term hash
 * @returns {bigint|null} - null if not ground
 */
function binToInt(h) {
  const t = Store.tag(h);
  if (!t) return null;

  // Compact form - O(1)
  if (t === 'binlit') return Store.child(h, 0);

  // Legacy recursive form - O(log n)
  if (t === 'atom' && Store.child(h, 0) === 'e') return 0n;

  // Flat form: i(rest) or o(rest)
  if ((t === 'i' || t === 'o') && Store.arity(h) === 1) {
    const rest = binToInt(Store.child(h, 0));
    if (rest === null) return null;
    return t === 'i' ? rest * 2n + 1n : rest * 2n;
  }

  return null;
}

/**
 * Convert BigInt to binary term hash (compact binlit form)
 * @param {bigint} n - Non-negative integer
 * @returns {number} - Term hash
 */
function intToBin(n) {
  return Store.put('binlit', [n]);
}

/**
 * Convert string to strlit term hash
 * @param {string} s - String value
 * @returns {number} - Term hash
 */
function strToHash(s) {
  return Store.put('strlit', [s]);
}

/**
 * Convert strlit term hash to string
 * @param {number} h - Term hash
 * @returns {string|null} - null if not a strlit
 */
function hashToStr(h) {
  if (Store.tag(h) !== 'strlit') return null;
  return Store.child(h, 0);
}

/**
 * Convert character code point to charlit term hash
 * @param {number} codePoint - Unicode code point
 * @returns {number} - Term hash
 */
function charToHash(codePoint) {
  return Store.put('charlit', [codePoint]);
}

/**
 * Convert charlit term hash to code point
 * @param {number} h - Term hash
 * @returns {number|null} - null if not a charlit
 */
function hashToChar(h) {
  if (Store.tag(h) !== 'charlit') return null;
  return Store.child(h, 0);
}

/**
 * Check if term is ground (no metavariables)
 * @param {number} h - Term hash
 * @returns {boolean}
 */
function isGround(h) {
  const t = Store.tag(h);
  if (!t) return false;

  if (t === 'freevar') {
    const name = Store.child(h, 0);
    return typeof name !== 'string' || !name.startsWith('_');
  }

  if (t === 'atom') return true;

  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && !isGround(c)) return false;
  }
  return true;
}

module.exports = {
  binToInt,
  intToBin,
  strToHash,
  hashToStr,
  charToHash,
  hashToChar,
  isGround
};
