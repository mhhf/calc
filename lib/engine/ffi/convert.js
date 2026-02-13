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
  const node = Store.get(h);
  if (!node) return null;

  // Compact form - O(1)
  if (node.tag === 'binlit') {
    return node.children[0];
  }

  // Legacy recursive form - O(log n)
  if (node.tag === 'atom' && node.children[0] === 'e') {
    return 0n;
  }

  // Flat form: {tag: 'i', children: [rest]} or {tag: 'o', children: [rest]}
  if ((node.tag === 'i' || node.tag === 'o') && node.children.length === 1) {
    const rest = binToInt(node.children[0]);
    if (rest === null) return null;
    return node.tag === 'i' ? rest * 2n + 1n : rest * 2n;
  }

  // Not a valid binary term (e.g., contains metavar)
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
  const node = Store.get(h);
  if (!node || node.tag !== 'strlit') return null;
  return node.children[0];
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
  const node = Store.get(h);
  if (!node || node.tag !== 'charlit') return null;
  return node.children[0];
}

/**
 * Check if term is ground (no metavariables)
 * @param {number} h - Term hash
 * @returns {boolean}
 */
function isGround(h) {
  const node = Store.get(h);
  if (!node) return false;

  if (node.tag === 'freevar') {
    const name = node.children[0];
    return typeof name !== 'string' || !name.startsWith('_');
  }

  if (node.tag === 'atom') return true;

  return node.children.every(c =>
    typeof c === 'number' ? isGround(c) : true
  );
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
