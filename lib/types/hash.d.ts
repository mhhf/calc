/**
 * FNV-1a 64-bit hashing for content-addressed storage
 */

/** FNV-1a prime for 64-bit */
export const FNV_PRIME: bigint;

/** FNV-1a offset basis for 64-bit */
export const FNV_OFFSET: bigint;

/**
 * Hash a string using FNV-1a 64-bit
 */
export function hashString(str: string): bigint;

/**
 * Hash a bigint
 */
export function hashBigInt(n: bigint): bigint;

/**
 * Hash a structural node (constructor + children)
 */
export function structHash(constructorId: number, childHashes: bigint[]): bigint;

/**
 * Combine multiple hashes into one
 */
export function hashCombine(...hashes: bigint[]): bigint;

/**
 * Hash any value by type dispatch
 */
export function hash64(value: string | bigint | number | { hash: bigint }): bigint;
