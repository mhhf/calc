/**
 * Binary ↔ BigInt Conversion for FFI
 *
 * Two representations:
 * - Compact: binlit stores BigInt directly in 1 node
 * - Legacy:  e = 0, (i X) = 2*X + 1, (o X) = 2*X (for pattern matching)
 *
 * FFI always produces binlit for O(1) storage.
 * binToInt handles both forms for backwards compatibility.
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

  if (node.tag === 'app') {
    const headNode = Store.get(node.children[0]);
    if (!headNode || headNode.tag !== 'atom') return null;

    const bit = headNode.children[0];
    const rest = binToInt(node.children[1]);

    if (rest === null) return null;

    if (bit === 'i') return rest * 2n + 1n;
    if (bit === 'o') return rest * 2n;
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
  return Store.intern('binlit', [n]);
}

/**
 * Convert BigInt to legacy recursive binary form
 * Use only for testing/comparison with legacy code
 * @param {bigint} n - Non-negative integer
 * @returns {number} - Term hash
 */
function intToBinRecursive(n) {
  if (n === 0n) {
    return Store.intern('atom', ['e']);
  }

  const bit = n % 2n === 1n ? 'i' : 'o';
  const rest = intToBinRecursive(n / 2n);

  const bitAtom = Store.intern('atom', [bit]);
  return Store.intern('app', [bitAtom, rest]);
}

/**
 * Convert string to strlit term hash
 * @param {string} s - String value
 * @returns {number} - Term hash
 */
function strToHash(s) {
  return Store.intern('strlit', [s]);
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
  return Store.intern('charlit', [codePoint]);
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
  intToBinRecursive,
  strToHash,
  hashToStr,
  charToHash,
  hashToChar,
  isGround
};
