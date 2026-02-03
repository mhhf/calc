/**
 * Content-Addressed Store for Terms
 *
 * Provides O(1) equality checking via hash comparison and
 * structural sharing via hash-consing.
 */

const { hashString, hashBigInt, structHash } = require('../hash');
const { profiler } = require('./profiler');

// Node types
const NodeType = {
  STRING: 0,    // String literal (variable names, atoms)
  BIGINT: 1,    // BigInt value (for numeric computations)
  STRUCT: 2,    // Structural node (constructor + children)
};

/**
 * Content-addressed store for terms
 */
class Store {
  constructor() {
    // Index: hash -> stored data
    this.strings = new Map();    // hash -> string
    this.bigints = new Map();    // hash -> bigint
    this.structs = new Map();    // hash -> { constructorId, children: [hash] }

    // Type index: hash -> NodeType
    this.types = new Map();

    // Stats
    this._internCount = 0;
    this._lookupCount = 0;
  }

  // === Interning (store and deduplicate) ===

  /**
   * Intern a string, return its hash
   */
  internString(str) {
    profiler.count('store.internString');
    const hash = hashString(str);

    if (!this.strings.has(hash)) {
      this.strings.set(hash, str);
      this.types.set(hash, NodeType.STRING);
      this._internCount++;
    }

    return hash;
  }

  /**
   * Intern a bigint, return its hash
   */
  internBigInt(val) {
    profiler.count('store.internBigInt');
    const hash = hashBigInt(val);

    if (!this.bigints.has(hash)) {
      this.bigints.set(hash, val);
      this.types.set(hash, NodeType.BIGINT);
      this._internCount++;
    }

    return hash;
  }

  /**
   * Intern a structural node, return its hash
   */
  internStruct(constructorId, childHashes) {
    profiler.count('store.internStruct');
    const hash = structHash(constructorId, childHashes);

    if (!this.structs.has(hash)) {
      this.structs.set(hash, {
        constructorId,
        children: childHashes,
      });
      this.types.set(hash, NodeType.STRUCT);
      this._internCount++;
    }

    return hash;
  }

  // === Retrieval ===

  /**
   * Get the type of a hash
   */
  getType(hash) {
    this._lookupCount++;
    return this.types.get(hash);
  }

  /**
   * Get string by hash
   */
  getString(hash) {
    this._lookupCount++;
    return this.strings.get(hash);
  }

  /**
   * Get bigint by hash
   */
  getBigInt(hash) {
    this._lookupCount++;
    return this.bigints.get(hash);
  }

  /**
   * Get structural node by hash
   */
  getStruct(hash) {
    this._lookupCount++;
    return this.structs.get(hash);
  }

  // === Query ===

  /**
   * Check if hash exists in store
   */
  has(hash) {
    return this.types.has(hash);
  }

  /**
   * Check if hash is a string
   */
  isString(hash) {
    return this.getType(hash) === NodeType.STRING;
  }

  /**
   * Check if hash is a bigint
   */
  isBigInt(hash) {
    return this.getType(hash) === NodeType.BIGINT;
  }

  /**
   * Check if hash is structural
   */
  isStruct(hash) {
    return this.getType(hash) === NodeType.STRUCT;
  }

  /**
   * Get constructor ID for a structural node
   */
  getConstructorId(hash) {
    const struct = this.getStruct(hash);
    return struct?.constructorId;
  }

  /**
   * Get children hashes for a structural node
   */
  getChildren(hash) {
    const struct = this.getStruct(hash);
    return struct?.children || [];
  }

  // === Equality ===

  /**
   * O(1) equality check via hash comparison
   */
  equal(hash1, hash2) {
    return hash1 === hash2;
  }

  // === Stats ===

  /**
   * Get store statistics
   */
  stats() {
    return {
      strings: this.strings.size,
      bigints: this.bigints.size,
      structs: this.structs.size,
      total: this.types.size,
      internCount: this._internCount,
      lookupCount: this._lookupCount,
    };
  }
}

/**
 * Scoped store for proof search branches
 *
 * Inherits from parent, but local additions can be discarded on backtrack.
 */
class ScopedStore {
  constructor(parent) {
    this.parent = parent;
    this.local = new Store();
  }

  // === Interning (store locally) ===

  internString(str) {
    // Check parent first
    const hash = hashString(str);
    if (this.parent.has(hash)) {
      return hash;
    }
    return this.local.internString(str);
  }

  internBigInt(val) {
    const hash = hashBigInt(val);
    if (this.parent.has(hash)) {
      return hash;
    }
    return this.local.internBigInt(val);
  }

  internStruct(constructorId, childHashes) {
    const hash = structHash(constructorId, childHashes);
    if (this.parent.has(hash)) {
      return hash;
    }
    return this.local.internStruct(constructorId, childHashes);
  }

  // === Retrieval (check local then parent) ===

  getType(hash) {
    const localType = this.local.getType(hash);
    if (localType !== undefined) return localType;
    return this.parent.getType(hash);
  }

  getString(hash) {
    const local = this.local.getString(hash);
    if (local !== undefined) return local;
    return this.parent.getString(hash);
  }

  getBigInt(hash) {
    const local = this.local.getBigInt(hash);
    if (local !== undefined) return local;
    return this.parent.getBigInt(hash);
  }

  getStruct(hash) {
    const local = this.local.getStruct(hash);
    if (local !== undefined) return local;
    return this.parent.getStruct(hash);
  }

  // === Query ===

  has(hash) {
    return this.local.has(hash) || this.parent.has(hash);
  }

  isString(hash) {
    return this.getType(hash) === NodeType.STRING;
  }

  isBigInt(hash) {
    return this.getType(hash) === NodeType.BIGINT;
  }

  isStruct(hash) {
    return this.getType(hash) === NodeType.STRUCT;
  }

  getConstructorId(hash) {
    const struct = this.getStruct(hash);
    return struct?.constructorId;
  }

  getChildren(hash) {
    const struct = this.getStruct(hash);
    return struct?.children || [];
  }

  // === Equality ===

  equal(hash1, hash2) {
    return hash1 === hash2;
  }

  // === Scoping ===

  /**
   * Create a child scope
   */
  fork() {
    return new ScopedStore(this);
  }

  /**
   * Commit local changes to parent
   */
  commit() {
    // Merge local strings
    for (const [hash, str] of this.local.strings) {
      if (!this.parent.has(hash)) {
        if (this.parent instanceof ScopedStore) {
          this.parent.local.strings.set(hash, str);
          this.parent.local.types.set(hash, NodeType.STRING);
        } else {
          this.parent.strings.set(hash, str);
          this.parent.types.set(hash, NodeType.STRING);
        }
      }
    }

    // Merge local bigints
    for (const [hash, val] of this.local.bigints) {
      if (!this.parent.has(hash)) {
        if (this.parent instanceof ScopedStore) {
          this.parent.local.bigints.set(hash, val);
          this.parent.local.types.set(hash, NodeType.BIGINT);
        } else {
          this.parent.bigints.set(hash, val);
          this.parent.types.set(hash, NodeType.BIGINT);
        }
      }
    }

    // Merge local structs
    for (const [hash, struct] of this.local.structs) {
      if (!this.parent.has(hash)) {
        if (this.parent instanceof ScopedStore) {
          this.parent.local.structs.set(hash, struct);
          this.parent.local.types.set(hash, NodeType.STRUCT);
        } else {
          this.parent.structs.set(hash, struct);
          this.parent.types.set(hash, NodeType.STRUCT);
        }
      }
    }
  }

  /**
   * Discard local changes (for backtracking)
   */
  discard() {
    this.local = new Store();
  }

  // === Stats ===

  stats() {
    return {
      local: this.local.stats(),
      parent: this.parent.stats(),
    };
  }
}

// === Global Singleton Store ===

let globalStore = null;

/**
 * Get the global store (creates if needed)
 * This is THE store - all content-addressed operations use it
 */
function getStore() {
  if (!globalStore) {
    globalStore = new Store();
  }
  return globalStore;
}

/**
 * Reset the global store (for testing only)
 */
function resetStore() {
  globalStore = new Store();
  return globalStore;
}

module.exports = { Store, ScopedStore, NodeType, getStore, resetStore };
