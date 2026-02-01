/**
 * Term - High-level wrapper around content-addressed hashes
 */

import { Store, ScopedStore } from './store';

/**
 * Term wrapper for content-addressed storage
 *
 * Provides O(1) equality via hash comparison and
 * convenient traversal methods
 */
export class Term {
  store: Store | ScopedStore;
  hash: bigint;

  constructor(store: Store | ScopedStore, hash: bigint);

  /**
   * Create a Term from an existing hash
   */
  static fromHash(store: Store | ScopedStore, hash: bigint): Term;

  /**
   * Create a Term from a string value
   */
  static fromString(store: Store | ScopedStore, str: string): Term;

  /**
   * Create a Term from a bigint value
   */
  static fromBigInt(store: Store | ScopedStore, n: bigint): Term;

  /**
   * Create a structural Term from constructor ID and children
   */
  static struct(
    store: Store | ScopedStore,
    constructorId: number,
    children: (Term | bigint)[]
  ): Term;

  /**
   * Check if this term represents a string
   */
  isString(): boolean;

  /**
   * Check if this term represents a bigint
   */
  isBigInt(): boolean;

  /**
   * Check if this term is a structural node
   */
  isStruct(): boolean;

  /**
   * Get the string value (throws if not a string)
   */
  getString(): string;

  /**
   * Get the bigint value (throws if not a bigint)
   */
  getBigInt(): bigint;

  /**
   * Get the constructor ID (throws if not a struct)
   */
  constructorId(): number;

  /**
   * Get child hashes (throws if not a struct)
   */
  childHashes(): bigint[];

  /**
   * Get children as Terms
   */
  children(): Term[];

  /**
   * Get number of children (0 for non-structs)
   */
  arity(): number;

  /**
   * O(1) equality check
   */
  equals(other: Term | null | undefined): boolean;

  /**
   * Check if this term contains another (by hash)
   */
  contains(targetHash: bigint): boolean;

  /**
   * Map a function over all nodes (bottom-up)
   */
  map(fn: (term: Term) => Term): Term;

  /**
   * Fold over all nodes (bottom-up)
   */
  fold<T>(fn: (acc: T, term: Term) => T, initial: T): T;

  /**
   * Debug string representation
   */
  toString(): string;
}
