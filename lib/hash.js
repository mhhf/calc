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
 * Hash a BigInt to 32-bit unsigned integer.
 * Uses bitwise shift (>>) instead of division for byte extraction.
 * @param {bigint} n
 * @returns {number} 32-bit hash
 */
function hashBigInt(n) {
  let hash = FNV_OFFSET;
  let val = n < 0n ? -n : n;

  // Hash sign
  hash ^= n < 0n ? 1 : 0;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;

  // Hash each byte (>>= 8n is bitwise shift, avoids BigInt division runtime)
  while (val > 0n) {
    hash ^= Number(val & 0xFFn);
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
    val >>= 8n;
  }

  return hash;
}

/**
 * Combine exactly two hashes. Fixed-arity avoids V8 Arguments object allocation.
 * Prefer this over hashCombine() on hot paths (store.js:computeHash).
 * @param {number} h1 - First 32-bit hash
 * @param {number} h2 - Second 32-bit hash
 * @returns {number} Combined 32-bit hash
 */
function hashCombine2(h1, h2) {
  let hash = FNV_OFFSET ^ h1;
  hash = Math.imul(hash, FNV_PRIME) >>> 0;
  hash ^= h2;
  return Math.imul(hash, FNV_PRIME) >>> 0;
}

/**
 * Combine N hashes (variadic). Used by cold-path callers (sequent, convert).
 * @param {...number} hashes - 32-bit hashes to combine
 * @returns {number} Combined 32-bit hash
 */
function hashCombine(...hashes) {
  let hash = FNV_OFFSET;
  for (let i = 0; i < hashes.length; i++) {
    hash ^= hashes[i];
    hash = Math.imul(hash, FNV_PRIME) >>> 0;
  }
  return hash;
}

module.exports = {
  hashString,
  hashBigInt,
  hashCombine,
  hashCombine2,
};
