/**
 * Content-addressed storage for term representations
 */

/** Node types for stored terms */
export enum NodeType {
  String = 'string',
  BigInt = 'bigint',
  Struct = 'struct',
}

/** Structure node data */
export interface StructData {
  constructorId: number;
  children: bigint[];
}

/**
 * Content-addressed store for terms
 *
 * Stores terms by their content hash for O(1) equality and structural sharing
 */
export class Store {
  strings: Map<bigint, string>;
  bigints: Map<bigint, bigint>;
  structs: Map<bigint, StructData>;
  types: Map<bigint, NodeType>;

  constructor();

  /**
   * Intern a string, return its hash
   */
  internString(str: string): bigint;

  /**
   * Intern a bigint, return its hash
   */
  internBigInt(n: bigint): bigint;

  /**
   * Intern a struct node, return its hash
   */
  internStruct(constructorId: number, childHashes: bigint[]): bigint;

  /**
   * Get the type of a stored value
   */
  getType(hash: bigint): NodeType | undefined;

  /**
   * Get stored string by hash
   */
  getString(hash: bigint): string | undefined;

  /**
   * Get stored bigint by hash
   */
  getBigInt(hash: bigint): bigint | undefined;

  /**
   * Get stored struct by hash
   */
  getStruct(hash: bigint): StructData | undefined;

  /**
   * O(1) equality check
   */
  equal(hash1: bigint, hash2: bigint): boolean;

  /**
   * Get store statistics
   */
  stats(): { strings: number; bigints: number; structs: number; total: number };
}

/**
 * Scoped store for backtracking support
 */
export class ScopedStore {
  constructor(parent: Store | ScopedStore | null);

  /**
   * Fork a new scope
   */
  fork(): ScopedStore;

  /**
   * Commit local changes to parent
   */
  commit(): void;

  /**
   * Discard local changes
   */
  discard(): void;

  // Inherits Store methods
  internString(str: string): bigint;
  internBigInt(n: bigint): bigint;
  internStruct(constructorId: number, childHashes: bigint[]): bigint;
  getType(hash: bigint): NodeType | undefined;
  getString(hash: bigint): string | undefined;
  getBigInt(hash: bigint): bigint | undefined;
  getStruct(hash: bigint): StructData | undefined;
  equal(hash1: bigint, hash2: bigint): boolean;
  stats(): { strings: number; bigints: number; structs: number; total: number };
}
