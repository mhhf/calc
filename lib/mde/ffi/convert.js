/**
 * Binary ↔ BigInt Conversion for FFI
 *
 * Binary representation: e = 0, (i X) = 2*X + 1, (o X) = 2*X
 */

const Store = require('../../v2/kernel/store');

/**
 * Convert binary term to BigInt
 * @param {number} h - Term hash
 * @returns {bigint|null} - null if not ground
 */
function binToInt(h) {
  const node = Store.get(h);
  if (!node) return null;

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
 * Convert BigInt to binary term hash
 * @param {bigint} n - Non-negative integer
 * @returns {number} - Term hash
 */
function intToBin(n) {
  if (n === 0n) {
    return Store.intern('atom', ['e']);
  }

  const bit = n % 2n === 1n ? 'i' : 'o';
  const rest = intToBin(n / 2n);

  const bitAtom = Store.intern('atom', [bit]);
  return Store.intern('app', [bitAtom, rest]);
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

module.exports = { binToInt, intToBin, isGround };
