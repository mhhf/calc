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
 *   STORE[hash] = { tag: string, children: (hash|string|bigint)[] }
 *
 * Children can be:
 * - number: hash reference to another term
 * - string: primitive value (variable names, atom names)
 * - bigint: for binlit compact storage (stores value directly)
 *
 * Example:
 *   put('freevar', ['A'])     -> hash1, stores { tag: 'freevar', children: ['A'] }
 *   put('freevar', ['B'])     -> hash2, stores { tag: 'freevar', children: ['B'] }
 *   put('tensor', [hash1, hash2]) -> hash3, stores { tag: 'tensor', children: [hash1, hash2] }
 *   put('binlit', [42n])      -> hash4, stores { tag: 'binlit', children: [42n] }
 *   put('strlit', ['hello'])  -> hash5, stores { tag: 'strlit', children: ['hello'] }
 *   put('charlit', [97])      -> hash6, stores { tag: 'charlit', children: [97] }
 */

const { hashString, hashCombine, hashBigInt } = require('../hash');

// The store: hash -> { tag, children }
const STORE = new Map();

/**
 * Compute hash for a node
 *
 * Supports three child types:
 * - number: hash reference to another term (most common)
 * - string: primitive value (variable names, atom names)
 * - bigint: for binlit compact storage
 *
 * @param {string} tag - Node tag
 * @param {(number|string|bigint)[]} children - Child hashes or primitives
 * @returns {number} 32-bit hash
 */
function computeHash(tag, children) {
  let h = hashString(tag);
  // Include arity to distinguish nullary from unary, etc.
  h = hashCombine(h, children.length);
  for (const c of children) {
    if (typeof c === 'number') {
      // Hash reference - combine directly
      h = hashCombine(h, c);
    } else if (typeof c === 'bigint') {
      // BigInt for binlit - use dedicated hasher
      h = hashCombine(h, hashBigInt(c));
    } else {
      // String primitive (atom names, variable names)
      h = hashCombine(h, hashString(String(c)));
    }
  }
  return h;
}

/**
 * Put a node: store if new, return hash (content-addressed / hash-consing)
 * @param {string} tag - Node tag
 * @param {(number|string)[]} children - Child hashes or primitive strings
 * @returns {number} Hash (CID) for this node
 */
function put(tag, children) {
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
 * Check if child is a term reference (hash) vs primitive (string/bigint)
 * @param {number|string|bigint} c - Child value
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
  put,
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
