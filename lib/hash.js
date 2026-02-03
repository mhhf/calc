/**
 * Fast 32-bit hashing for content-addressed storage
 *
 * Uses FNV-1a algorithm which is:
 * - Fast (no crypto overhead, uses native Number ops)
 * - Good distribution
 * - Consistent across runs
 *
 * NOTE: 32-bit has collision risk at ~77k items (birthday paradox).
 * For now this is acceptable for proof search (typically <10k terms).
 *
 * TODO (medium priority): Implement hybrid approach:
 * - Use 32-bit for fast runtime operations
 * - Compute 128-bit CID lazily for persistence/serialization
 * - Add memoization (ast._hash) to avoid recomputation
 * See: lib/hash-alternatives.js for xxHash128 implementation
 */

// FNV-1a 32-bit parameters
const FNV_PRIME = 0x01000193;
const FNV_OFFSET = 0x811c9dc5;

/**
 * Hash a string to 32-bit unsigned integer using FNV-1a
 * @param {string} str
 * @returns {number} 32-bit hash
 */
function hashString(str) {
  let hash = FNV_OFFSET;
  for (let i = 0; i < str.length; i++) {
    hash ^= str.charCodeAt(i);
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
  }
  return hash;
}

/**
 * Hash a Uint8Array to 32-bit unsigned integer using FNV-1a
 * @param {Uint8Array} bytes
 * @returns {number} 32-bit hash
 */
function hashBytes(bytes) {
  let hash = FNV_OFFSET;
  for (let i = 0; i < bytes.length; i++) {
    hash ^= bytes[i];
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
  }
  return hash;
}

/**
 * Hash a number (integer) to 32-bit unsigned integer
 * @param {number} n
 * @returns {number} 32-bit hash
 */
function hashNumber(n) {
  let hash = FNV_OFFSET;
  let val = Math.abs(Math.floor(n));

  // Hash sign bit
  hash ^= n < 0 ? 1 : 0;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;

  // Hash each byte (up to 6 bytes for safe integers)
  while (val > 0) {
    hash ^= val & 0xFF;
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
    val = Math.floor(val / 256);
  }

  return hash;
}

/**
 * Hash a BigInt to 32-bit unsigned integer
 * @param {bigint} n
 * @returns {number} 32-bit hash
 */
function hashBigInt(n) {
  let hash = FNV_OFFSET;
  let val = n < 0n ? -n : n;

  // Hash sign
  hash ^= n < 0n ? 1 : 0;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;

  // Hash each byte
  while (val > 0n) {
    hash ^= Number(val & 0xFFn);
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
    val >>= 8n;
  }

  return hash;
}

/**
 * Combine multiple hashes into one
 * @param {...number} hashes - 32-bit hashes to combine
 * @returns {number} Combined 32-bit hash
 */
function hashCombine(...hashes) {
  let hash = FNV_OFFSET;
  for (const h of hashes) {
    hash ^= h;
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
  }
  return hash;
}

/**
 * Hash for structural nodes: combines constructor ID and children hashes
 * @param {number} constructorId
 * @param {number[]} childHashes - Array of 32-bit child hashes
 * @returns {number} 32-bit hash
 */
function structHash(constructorId, childHashes) {
  let hash = FNV_OFFSET;

  // Include constructor ID
  hash ^= constructorId;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;

  // Include arity
  hash ^= childHashes.length;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;

  // Include each child hash
  for (const childHash of childHashes) {
    hash ^= childHash;
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
  }

  return hash;
}

/**
 * Generic hash function - dispatches based on type
 * @param {string|number|bigint|Uint8Array|Array} value
 * @returns {number} 32-bit hash
 */
function hash64(value) {
  // Note: Still named hash64 for backwards compatibility, but returns 32-bit
  if (typeof value === 'string') {
    return hashString(value);
  }
  if (typeof value === 'bigint') {
    return hashBigInt(value);
  }
  if (typeof value === 'number') {
    return hashNumber(value);
  }
  if (value instanceof Uint8Array) {
    return hashBytes(value);
  }
  if (Array.isArray(value)) {
    return hashCombine(...value.map(hash64));
  }
  throw new Error(`Cannot hash value of type ${typeof value}`);
}

module.exports = {
  hash64,
  hashString,
  hashBytes,
  hashBigInt,
  hashNumber,
  hashCombine,
  structHash,
  FNV_PRIME,
  FNV_OFFSET,
};
