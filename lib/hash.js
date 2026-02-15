/**
 * Fast 32-bit hashing for content-addressed storage
 *
 * Uses FNV-1a algorithm: fast, good distribution, consistent across runs.
 *
 * 32-bit has collision risk at ~77k items (birthday paradox).
 * Acceptable for proof search (typically <10k terms).
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

module.exports = {
  hashString,
  hashBigInt,
  hashCombine,
};
