/**
 * Content-Addressed AST Store
 *
 * Implements proper content-addressing where:
 * - Each unique AST structure has exactly one hash (CID)
 * - Hash IS the pointer/identifier
 * - Children are stored as hashes (references), not embedded objects
 * - Equality is O(1) hash comparison
 *
 * Node format in store:
 *   STORE[hash] = { tag: string, children: (hash|string)[] }
 *
 * Children can be:
 * - number: hash reference to another term
 * - string: primitive value (variable names, atom names)
 *
 * Example:
 *   intern('freevar', ['A'])     -> hash1, stores { tag: 'freevar', children: ['A'] }
 *   intern('freevar', ['B'])     -> hash2, stores { tag: 'freevar', children: ['B'] }
 *   intern('tensor', [hash1, hash2]) -> hash3, stores { tag: 'tensor', children: [hash1, hash2] }
 */

const { hashString, hashCombine } = require('../../hash');

// The store: hash -> { tag, children }
const STORE = new Map();

/**
 * Compute hash for a node
 * @param {string} tag - Node tag
 * @param {(number|string)[]} children - Child hashes or primitive strings
 * @returns {number} 32-bit hash
 */
function computeHash(tag, children) {
  let h = hashString(tag);
  // Include arity to distinguish nullary from unary, etc.
  h = hashCombine(h, children.length);
  for (const c of children) {
    // If child is a hash (number), combine directly
    // If child is a string (primitive), hash the string
    h = hashCombine(h, typeof c === 'number' ? c : hashString(String(c)));
  }
  return h;
}

/**
 * Intern a node: store if new, return hash
 * @param {string} tag - Node tag
 * @param {(number|string)[]} children - Child hashes or primitive strings
 * @returns {number} Hash (CID) for this node
 */
function intern(tag, children) {
  const h = computeHash(tag, children);
  if (!STORE.has(h)) {
    STORE.set(h, { tag, children });
  }
  return h;
}

/**
 * Get node by hash
 * @param {number} h - Hash
 * @returns {{ tag: string, children: (number|string)[] } | undefined}
 */
function get(h) {
  return STORE.get(h);
}

/**
 * Get tag of node
 * @param {number} h - Hash
 * @returns {string | undefined}
 */
function tag(h) {
  return STORE.get(h)?.tag;
}

/**
 * Get children of node
 * @param {number} h - Hash
 * @returns {(number|string)[]}
 */
function children(h) {
  return STORE.get(h)?.children || [];
}

/**
 * Get specific child
 * @param {number} h - Hash
 * @param {number} i - Child index
 * @returns {number|string|undefined}
 */
function child(h, i) {
  return STORE.get(h)?.children[i];
}

/**
 * Check if value is a term hash (stored in STORE)
 * @param {*} v - Value to check
 * @returns {boolean}
 */
function isTerm(v) {
  return typeof v === 'number' && STORE.has(v);
}

/**
 * Check if child is a term reference (hash) vs primitive (string)
 * @param {number|string} c - Child value
 * @returns {boolean}
 */
function isTermChild(c) {
  return typeof c === 'number';
}

/**
 * Clear the store (for testing)
 */
function clear() {
  STORE.clear();
}

/**
 * Get store size
 * @returns {number}
 */
function size() {
  return STORE.size;
}

/**
 * Debug: dump store contents
 */
function dump() {
  const entries = [];
  for (const [h, node] of STORE) {
    entries.push({ hash: h, ...node });
  }
  return entries;
}

// Convenience: equality is just hash comparison
const eq = (a, b) => a === b;

module.exports = {
  intern,
  get,
  tag,
  children,
  child,
  isTerm,
  isTermChild,
  eq,
  clear,
  size,
  dump,
  // For advanced use
  computeHash,
  STORE
};
