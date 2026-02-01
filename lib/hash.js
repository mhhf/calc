/**
 * Fast 64-bit hashing for content-addressed storage
 *
 * Uses FNV-1a algorithm which is:
 * - Fast (no crypto overhead)
 * - Good distribution
 * - Consistent across runs
 */

// FNV-1a 64-bit parameters (using BigInt for 64-bit precision)
const FNV_PRIME = 0x100000001b3n;
const FNV_OFFSET = 0xcbf29ce484222325n;
const MASK_64 = (1n << 64n) - 1n;

/**
 * Hash a string to 64-bit BigInt using FNV-1a
 */
function hashString(str) {
  let hash = FNV_OFFSET;
  for (let i = 0; i < str.length; i++) {
    hash ^= BigInt(str.charCodeAt(i));
    hash = (hash * FNV_PRIME) & MASK_64;
  }
  return hash;
}

/**
 * Hash a Uint8Array to 64-bit BigInt using FNV-1a
 */
function hashBytes(bytes) {
  let hash = FNV_OFFSET;
  for (let i = 0; i < bytes.length; i++) {
    hash ^= BigInt(bytes[i]);
    hash = (hash * FNV_PRIME) & MASK_64;
  }
  return hash;
}

/**
 * Hash a BigInt to 64-bit BigInt
 */
function hashBigInt(n) {
  // Convert to bytes and hash
  let hash = FNV_OFFSET;
  let val = n < 0n ? -n : n;

  // Hash sign
  hash ^= n < 0n ? 1n : 0n;
  hash = (hash * FNV_PRIME) & MASK_64;

  // Hash each byte
  while (val > 0n) {
    hash ^= val & 0xFFn;
    hash = (hash * FNV_PRIME) & MASK_64;
    val >>= 8n;
  }

  return hash;
}

/**
 * Hash a number (integer) to 64-bit BigInt
 */
function hashNumber(n) {
  return hashBigInt(BigInt(Math.floor(n)));
}

/**
 * Combine multiple hashes into one
 */
function hashCombine(...hashes) {
  let hash = FNV_OFFSET;
  for (const h of hashes) {
    // XOR with existing hash
    hash ^= h;
    hash = (hash * FNV_PRIME) & MASK_64;
  }
  return hash;
}

/**
 * Hash for structural nodes: combines constructor ID and children hashes
 */
function structHash(constructorId, childHashes) {
  let hash = FNV_OFFSET;

  // Include constructor ID
  hash ^= BigInt(constructorId);
  hash = (hash * FNV_PRIME) & MASK_64;

  // Include arity
  hash ^= BigInt(childHashes.length);
  hash = (hash * FNV_PRIME) & MASK_64;

  // Include each child hash
  for (const childHash of childHashes) {
    hash ^= childHash;
    hash = (hash * FNV_PRIME) & MASK_64;
  }

  return hash;
}

/**
 * Generic hash function - dispatches based on type
 */
function hash64(value) {
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
