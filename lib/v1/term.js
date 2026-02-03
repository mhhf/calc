/**
 * Term - Wrapper around content-addressed hash
 *
 * Provides a convenient API for working with terms while
 * maintaining O(1) equality via hash comparison.
 */

const { NodeType } = require('./store');

/**
 * Term wrapper around a hash in the store
 */
class Term {
  constructor(store, hash) {
    this.store = store;
    this.hash = hash;
  }

  // === Type checking ===

  isString() {
    return this.store.isString(this.hash);
  }

  isBigInt() {
    return this.store.isBigInt(this.hash);
  }

  isStruct() {
    return this.store.isStruct(this.hash);
  }

  // === Value access ===

  /**
   * Get the string value (if this is a string)
   */
  getString() {
    return this.store.getString(this.hash);
  }

  /**
   * Get the bigint value (if this is a bigint)
   */
  getBigInt() {
    return this.store.getBigInt(this.hash);
  }

  /**
   * Get the constructor ID (if this is a struct)
   */
  constructorId() {
    return this.store.getConstructorId(this.hash);
  }

  /**
   * Get children as Term objects (if this is a struct)
   */
  children() {
    const childHashes = this.store.getChildren(this.hash);
    return childHashes.map(h => new Term(this.store, h));
  }

  /**
   * Get child hashes (if this is a struct)
   */
  childHashes() {
    return this.store.getChildren(this.hash);
  }

  /**
   * Get arity (number of children)
   */
  arity() {
    return this.store.getChildren(this.hash).length;
  }

  // === Equality ===

  /**
   * O(1) equality check
   */
  equals(other) {
    if (!(other instanceof Term)) return false;
    return this.hash === other.hash;
  }

  // === Factory methods ===

  /**
   * Create a Term from a hash
   */
  static fromHash(store, hash) {
    return new Term(store, hash);
  }

  /**
   * Create a Term from a string
   */
  static fromString(store, str) {
    const hash = store.internString(str);
    return new Term(store, hash);
  }

  /**
   * Create a Term from a bigint
   */
  static fromBigInt(store, val) {
    const hash = store.internBigInt(val);
    return new Term(store, hash);
  }

  /**
   * Create a structural Term
   */
  static struct(store, constructorId, children) {
    const childHashes = children.map(c =>
      c instanceof Term ? c.hash : c
    );
    const hash = store.internStruct(constructorId, childHashes);
    return new Term(store, hash);
  }

  // === Traversal ===

  /**
   * Map over all nodes in the term (post-order)
   */
  map(fn) {
    if (!this.isStruct()) {
      return fn(this);
    }

    const newChildren = this.children().map(c => c.map(fn));
    const newChildHashes = newChildren.map(c => c.hash);
    const oldChildHashes = this.childHashes();

    // Check if any children changed
    let changed = false;
    for (let i = 0; i < newChildHashes.length; i++) {
      if (newChildHashes[i] !== oldChildHashes[i]) {
        changed = true;
        break;
      }
    }

    if (!changed) {
      return fn(this);
    }

    // Create new term with mapped children
    const newTerm = Term.struct(this.store, this.constructorId(), newChildren);
    return fn(newTerm);
  }

  /**
   * Fold over all nodes (post-order)
   */
  fold(fn, initial) {
    if (!this.isStruct()) {
      return fn(initial, this);
    }

    let acc = initial;
    for (const child of this.children()) {
      acc = child.fold(fn, acc);
    }
    return fn(acc, this);
  }

  /**
   * Check if term contains a specific hash
   */
  contains(hash) {
    if (this.hash === hash) return true;
    if (!this.isStruct()) return false;
    return this.children().some(c => c.contains(hash));
  }

  // === Debug ===

  /**
   * String representation for debugging
   */
  toString() {
    if (this.isString()) {
      return `String(${this.getString()})`;
    }
    if (this.isBigInt()) {
      return `BigInt(${this.getBigInt()})`;
    }
    if (this.isStruct()) {
      const children = this.children().map(c => c.toString()).join(', ');
      return `Struct(${this.constructorId()}, [${children}])`;
    }
    return `Unknown(${this.hash})`;
  }
}

module.exports = { Term };
