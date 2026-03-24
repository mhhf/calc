/**
 * Content-Addressed AST Store — Flat TypedArray Arena
 *
 * SoA (Struct-of-Arrays) layout with sequential indices.
 * Content-addressing preserved via dedup Map on put() (cold path).
 *
 * Node identity: sequential uint32 index (not hash).
 * Equality: a === b (same content → same index via dedup).
 *
 * Children can be:
 * - term index (uint32): reference to another node
 * - string table index (uint32): for atom/freevar/strlit names
 * - bigint table index (uint32): for binlit values
 * - raw uint32: for charlit codepoints
 *
 * Tag determines child type (no per-node bitmask needed).
 */

const { hashString, hashCombine, hashCombine2, hashBigInt } = require('../hash');

// =============================================================================
// Tag Registry
// =============================================================================

const TAG = Object.create(null);
const TAG_NAMES = [];
let nextTag = 0;

function registerTag(name) {
  if (TAG[name] !== undefined) return TAG[name];
  const id = nextTag++;
  TAG[name] = id;
  TAG_NAMES[id] = name;
  return id;
}

// Pre-register all known non-predicate tags (connectives, structural, quantifiers).
// Tags registered here get IDs below PRED_BOUNDARY — everything dynamic is a predicate.
['atom', 'freevar', 'metavar', 'tensor', 'loli', 'with', 'bang', 'one', 'type',
 'arrow', 'monad', 'app', 'binlit', 'strlit', 'charlit',
 'var', 'any', 'hyp', 'comma', 'empty', 'seq', 'deriv',
 'bound', 'exists', 'forall', 'evar', 'oplus', 'zero',
 'arrlit', 'acons'].forEach(registerTag);

// Namespace boundary: tags with ID < PRED_BOUNDARY are built-in (non-predicate).
// Tags with ID >= PRED_BOUNDARY are user-defined predicates.
const PRED_BOUNDARY = nextTag;

// Tag-based child type discrimination (set after registration)
const STRING_CHILD_TAGS = new Uint8Array(256);
STRING_CHILD_TAGS[TAG.atom] = 1;
STRING_CHILD_TAGS[TAG.freevar] = 1;
STRING_CHILD_TAGS[TAG.metavar] = 1;
STRING_CHILD_TAGS[TAG.strlit] = 1;

const BIGINT_CHILD_TAGS = new Uint8Array(256);
BIGINT_CHILD_TAGS[TAG.binlit] = 1;
BIGINT_CHILD_TAGS[TAG.bound] = 1;
BIGINT_CHILD_TAGS[TAG.evar] = 1;

const ARRAY_CHILD_TAGS = new Uint8Array(256);
ARRAY_CHILD_TAGS[TAG.arrlit] = 1;

// Leaf tags: no term children to recurse into (used by walkers).
// Indexed by tagId for O(1) lookup vs 4+ string comparisons.
const LEAF_TAGS = new Uint8Array(256);
LEAF_TAGS[TAG.atom] = 1;
LEAF_TAGS[TAG.binlit] = 1;
LEAF_TAGS[TAG.strlit] = 1;
LEAF_TAGS[TAG.charlit] = 1;
LEAF_TAGS[TAG.arrlit] = 1;

// charlit: child is raw uint32 codepoint (not a term ref, not a string)
// No special table needed — stored directly in child0

// =============================================================================
// String Interning
// =============================================================================

/** String interning table: dedup strings to uint32 indices.
 *  Zig equivalent: std.StringHashMap(u32) + ArrayList([]const u8). */
class StringTable {
  constructor() {
    this._toId = new Map();
    this._toStr = [];
    this._next = 0;
  }
  intern(s) {
    let id = this._toId.get(s);
    if (id === undefined) {
      id = this._next++;
      this._toId.set(s, id);
      this._toStr.push(s);
    }
    return id;
  }
  get(id) { return this._toStr[id]; }
  size() { return this._next; }
  clear() {
    this._toId.clear();
    this._toStr.length = 0;
    this._next = 0;
  }
  /** Snapshot all strings for serialization. */
  snapshot() { return this._toStr.slice(0, this._next); }
  /** Bulk restore from array of strings. */
  restore(strings) {
    this.clear();
    for (const s of strings) {
      this._toId.set(s, this._next);
      this._toStr.push(s);
      this._next++;
    }
  }
}

const stringTable = new StringTable();

// =============================================================================
// BigInt Side Table
// =============================================================================

/** BigInt interning table: stores BigInt values by uint32 index.
 *  Zig equivalent: ArrayList(u256) or [N][4]u64 for fixed-width arithmetic. */
class BigIntTable {
  constructor() {
    this._values = [];
    this._next = 0;
  }
  store(value) {
    const id = this._next++;
    this._values.push(value);
    return id;
  }
  get(id) { return this._values[id]; }
  size() { return this._next; }
  clear() {
    this._values.length = 0;
    this._next = 0;
  }
  /** Snapshot all values for serialization. */
  snapshot() { return this._values.slice(0, this._next); }
  /** Bulk restore from array of BigInts. */
  restore(values) {
    this.clear();
    for (const v of values) {
      this._values.push(v);
      this._next++;
    }
  }
}

const bigIntTable = new BigIntTable();

// =============================================================================
// Array Side Table (for arrlit nodes)
// =============================================================================

const ARRAY_TABLE = [];  // {data: Uint32Array, offset: u32, length: u32}
let nextArrayId = 0;

function storeArray(data, offset, length) {
  if (offset === undefined) offset = 0;
  if (length === undefined) length = data.length;
  const id = nextArrayId++;
  ARRAY_TABLE.push({ data, offset, length });
  return id;
}

function getArrayEntry(id) { return ARRAY_TABLE[id]; }

/**
 * Get array elements as a Uint32Array view for an arrlit hash.
 * @param {number} h - arrlit node hash
 * @returns {Uint32Array|undefined}
 */
function getArrayElements(h) {
  if (typeof h !== 'number' || h < 1 || h >= nextId) return undefined;
  if (tags[h] !== TAG.arrlit) return undefined;
  const entry = ARRAY_TABLE[child0[h]];
  if (!entry) return undefined;
  return entry.data.subarray(entry.offset, entry.offset + entry.length);
}

/**
 * Convenience: put an arrlit node from a Uint32Array of element hashes.
 * @param {Uint32Array|number[]} elements
 * @returns {number} arrlit node hash
 */
function putArray(elements) {
  const data = elements instanceof Uint32Array ? elements : new Uint32Array(elements);
  return put('arrlit', [data]);
}

// =============================================================================
// SoA TypedArray Arena
// =============================================================================

const INITIAL_CAPACITY = 4_000_000;

let capacity = INITIAL_CAPACITY;
let tags    = new Uint8Array(capacity);
let arities = new Uint8Array(capacity);
let child0  = new Uint32Array(capacity);
let child1  = new Uint32Array(capacity);
let child2  = new Uint32Array(capacity);
let child3  = new Uint32Array(capacity);
let child4  = new Uint32Array(capacity);

// Index 0 reserved as null sentinel (so falsy checks on indices work)
let nextId = 1;

// Content-address dedup: content hash → sequential index
const DEDUP = new Map();

function grow() {
  const newCap = capacity * 2;
  const newTags = new Uint8Array(newCap);
  const newArities = new Uint8Array(newCap);
  const newChild0 = new Uint32Array(newCap);
  const newChild1 = new Uint32Array(newCap);
  const newChild2 = new Uint32Array(newCap);
  const newChild3 = new Uint32Array(newCap);
  const newChild4 = new Uint32Array(newCap);
  newTags.set(tags);
  newArities.set(arities);
  newChild0.set(child0);
  newChild1.set(child1);
  newChild2.set(child2);
  newChild3.set(child3);
  newChild4.set(child4);
  tags = newTags;
  arities = newArities;
  child0 = newChild0;
  child1 = newChild1;
  child2 = newChild2;
  child3 = newChild3;
  child4 = newChild4;
  capacity = newCap;
}

// =============================================================================
// Hashing (same FNV-1a as before, for dedup)
// =============================================================================

function computeHash(tag, children) {
  let h = hashString(tag);
  // For arrlit, children[0] is Uint32Array — hash length + elements
  if (children.length === 1 && children[0] instanceof Uint32Array) {
    const arr = children[0];
    h = hashCombine2(h, arr.length);
    for (let i = 0; i < arr.length; i++) {
      h = hashCombine2(h, arr[i]);
    }
    return h;
  }
  h = hashCombine2(h, children.length);
  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    if (typeof c === 'number') {
      h = hashCombine2(h, c);
    } else if (typeof c === 'bigint') {
      h = hashCombine2(h, hashBigInt(c));
    } else {
      h = hashCombine2(h, hashString(String(c)));
    }
  }
  return h;
}

// =============================================================================
// Core API
// =============================================================================

/** Verify that an existing entry structurally matches (tag, children). */
function matchesEntry(id, tagName, children) {
  const tagId = TAG[tagName];
  if (tagId === undefined || tags[id] !== tagId) return false;
  // arrlit: children[0] is Uint32Array, stored as arrayTableIdx with arity=1
  if (ARRAY_CHILD_TAGS[tagId]) {
    if (arities[id] !== 1) return false;
    const arr = children[0];
    if (!(arr instanceof Uint32Array)) return false;
    const entry = ARRAY_TABLE[child0[id]];
    if (!entry || entry.length !== arr.length) return false;
    for (let i = 0; i < arr.length; i++) {
      if (entry.data[entry.offset + i] !== arr[i]) return false;
    }
    return true;
  }
  if (arities[id] !== children.length) return false;
  const ca = [child0, child1, child2, child3, child4];
  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    const stored = ca[i][id];
    if (typeof c === 'string') {
      if (stringTable.get(stored) !== c) return false;
    } else if (typeof c === 'bigint') {
      if (bigIntTable.get(stored) !== c) return false;
    } else {
      if (stored !== c) return false;
    }
  }
  return true;
}

/**
 * Put a node: store if new, return sequential index (content-addressed).
 * @param {string} tagName - Node tag
 * @param {(number|string|bigint)[]} children - Child values
 * @returns {number} Sequential index for this node
 */
function put(tagName, children) {
  // Normalize acons(H, arrlit(...)) → arrlit([H, ...]) and acons(H, ae) → arrlit([H])
  if (tagName === 'acons' && children.length === 2) {
    const tail = children[1];
    if (typeof tail === 'number' && tail >= 1 && tail < nextId) {
      if (tags[tail] === TAG.arrlit) {
        const entry = ARRAY_TABLE[child0[tail]];
        const elems = entry.data.subarray(entry.offset, entry.offset + entry.length);
        const newElems = new Uint32Array(elems.length + 1);
        newElems[0] = children[0];
        newElems.set(elems, 1);
        return put('arrlit', [newElems]);
      }
      if (tags[tail] === TAG.atom && stringTable.get(child0[tail]) === 'ae') {
        return put('arrlit', [new Uint32Array([children[0]])]);
      }
    }
  }

  let h = computeHash(tagName, children);
  let existing = DEDUP.get(h);
  if (existing !== undefined) {
    if (matchesEntry(existing, tagName, children)) return existing;
    // 32-bit FNV-1a collision — linear probe to find an empty slot
    for (let probe = 1; probe < 64; probe++) {
      const h2 = (h + probe) >>> 0;
      const ex2 = DEDUP.get(h2);
      if (ex2 === undefined) { h = h2; existing = undefined; break; }
      if (matchesEntry(ex2, tagName, children)) return ex2;
    }
    if (existing !== undefined) {
      throw new Error(
        `Store hash collision (exhausted probes): entry ${existing} (tag=${TAG_NAMES[tags[existing]]}) ` +
        `collides with new (tag=${tagName}). Consider upgrading to 64-bit hash.`
      );
    }
  }

  if (nextId >= capacity) grow();

  const id = nextId++;
  DEDUP.set(h, id);

  const tagId = TAG[tagName] !== undefined ? TAG[tagName] : registerTag(tagName);
  tags[id] = tagId;

  // arrlit: children[0] is Uint32Array → store in ARRAY_TABLE
  if (ARRAY_CHILD_TAGS[tagId] && children.length === 1 && children[0] instanceof Uint32Array) {
    arities[id] = 1;
    child0[id] = storeArray(children[0]);
    return id;
  }

  arities[id] = children.length;

  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    let val;
    if (typeof c === 'string') {
      val = stringTable.intern(c);
    } else if (typeof c === 'bigint') {
      val = bigIntTable.store(c);
    } else {
      val = c; // term index or raw number (charlit codepoint)
    }
    if (i === 0) child0[id] = val;
    else if (i === 1) child1[id] = val;
    else if (i === 2) child2[id] = val;
    else if (i === 3) child3[id] = val;
    else child4[id] = val;
  }

  return id;
}

/**
 * Arity-1 specialization: avoids children array allocation.
 * Hot path: binlit, freevar, bang, monad construction.
 */
function put1(tagName, c0) {
  const tagId = TAG[tagName] !== undefined ? TAG[tagName] : registerTag(tagName);

  // Compute hash inline (no children array needed)
  let h = hashString(tagName);
  h = hashCombine2(h, 1); // arity = 1
  if (typeof c0 === 'number') {
    h = hashCombine2(h, c0);
  } else if (typeof c0 === 'bigint') {
    h = hashCombine2(h, hashBigInt(c0));
  } else {
    h = hashCombine2(h, hashString(String(c0)));
  }

  // Dedup check
  let existing = DEDUP.get(h);
  if (existing !== undefined) {
    if (tags[existing] === tagId && arities[existing] === 1) {
      const stored = child0[existing];
      if (typeof c0 === 'string') {
        if (stringTable.get(stored) === c0) return existing;
      } else if (typeof c0 === 'bigint') {
        if (bigIntTable.get(stored) === c0) return existing;
      } else {
        if (stored === c0) return existing;
      }
    }
    // Collision — fall through to generic put (handles linear probing)
    return put(tagName, [c0]);
  }

  if (nextId >= capacity) grow();
  const id = nextId++;
  DEDUP.set(h, id);
  tags[id] = tagId;
  arities[id] = 1;

  if (typeof c0 === 'string') {
    child0[id] = stringTable.intern(c0);
  } else if (typeof c0 === 'bigint') {
    child0[id] = bigIntTable.store(c0);
  } else {
    child0[id] = c0;
  }
  return id;
}

/**
 * Arity-2 specialization: avoids children array allocation.
 * Hot path: loli, tensor, with, oplus, exists, forall construction.
 */
function put2(tagName, c0, c1) {
  // Normalize acons(H, arrlit/ae) → arrlit — delegate to generic put
  if (tagName === 'acons') return put(tagName, [c0, c1]);

  const tagId = TAG[tagName] !== undefined ? TAG[tagName] : registerTag(tagName);

  // Compute hash inline
  let h = hashString(tagName);
  h = hashCombine2(h, 2); // arity = 2
  // Both children are term indices (numbers) in the common case
  if (typeof c0 === 'number') {
    h = hashCombine2(h, c0);
  } else if (typeof c0 === 'bigint') {
    h = hashCombine2(h, hashBigInt(c0));
  } else {
    h = hashCombine2(h, hashString(String(c0)));
  }
  if (typeof c1 === 'number') {
    h = hashCombine2(h, c1);
  } else if (typeof c1 === 'bigint') {
    h = hashCombine2(h, hashBigInt(c1));
  } else {
    h = hashCombine2(h, hashString(String(c1)));
  }

  // Dedup check
  let existing = DEDUP.get(h);
  if (existing !== undefined) {
    if (tags[existing] === tagId && arities[existing] === 2) {
      // Quick structural check (both children are typically numbers)
      let match = true;
      if (typeof c0 === 'string') { if (stringTable.get(child0[existing]) !== c0) match = false; }
      else if (typeof c0 === 'bigint') { if (bigIntTable.get(child0[existing]) !== c0) match = false; }
      else { if (child0[existing] !== c0) match = false; }
      if (match) {
        if (typeof c1 === 'string') { if (stringTable.get(child1[existing]) !== c1) match = false; }
        else if (typeof c1 === 'bigint') { if (bigIntTable.get(child1[existing]) !== c1) match = false; }
        else { if (child1[existing] !== c1) match = false; }
      }
      if (match) return existing;
    }
    // Collision — fall through to generic put
    return put(tagName, [c0, c1]);
  }

  if (nextId >= capacity) grow();
  const id = nextId++;
  DEDUP.set(h, id);
  tags[id] = tagId;
  arities[id] = 2;

  if (typeof c0 === 'string') child0[id] = stringTable.intern(c0);
  else if (typeof c0 === 'bigint') child0[id] = bigIntTable.store(c0);
  else child0[id] = c0;

  if (typeof c1 === 'string') child1[id] = stringTable.intern(c1);
  else if (typeof c1 === 'bigint') child1[id] = bigIntTable.store(c1);
  else child1[id] = c1;

  return id;
}

/** Reconstruct child value from raw uint32 based on parent tag */
function reconstructChild(id, i) {
  const raw = i === 0 ? child0[id] : i === 1 ? child1[id] : i === 2 ? child2[id] : i === 3 ? child3[id] : child4[id];
  const t = tags[id];
  if (STRING_CHILD_TAGS[t]) return stringTable.get(raw);
  if (BIGINT_CHILD_TAGS[t]) return bigIntTable.get(raw);
  if (ARRAY_CHILD_TAGS[t]) {
    const entry = ARRAY_TABLE[raw];
    return entry.data.subarray(entry.offset, entry.offset + entry.length);
  }
  return raw; // term index or raw number (charlit)
}

/**
 * Get node by index (backward-compatible wrapper, allocates object).
 * Use tag()/child()/arity() for hot-path access.
 */
function get(id) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return undefined;
  const a = arities[id];
  const ch = [];
  for (let i = 0; i < a; i++) {
    ch.push(reconstructChild(id, i));
  }
  return { tag: TAG_NAMES[tags[id]], children: ch };
}

/** Get tag name of node */
function tag(id) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return undefined;
  return TAG_NAMES[tags[id]];
}

/** Get raw numeric tag ID (0 = invalid/sentinel). No string allocation. */
function tagId(id) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return 0;
  return tags[id];
}

/** Get children of node (allocates array) */
function children(id) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return [];
  const a = arities[id];
  const ch = [];
  for (let i = 0; i < a; i++) {
    ch.push(reconstructChild(id, i));
  }
  return ch;
}

/** Get arity (number of children) */
function arity(id) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return 0;
  return arities[id];
}

/** Get specific child of node */
function child(id, i) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return undefined;
  return reconstructChild(id, i);
}

/** Get raw child value (uint32 index) without type-based reconstruction.
 *  For term children this is the term index; for string children it's the
 *  string table index; for bigint children it's the bigint table index.
 *  Used by ZK witness generation where all values must be numeric. */
function rawChild(id, i) {
  if (typeof id !== 'number' || id < 1 || id >= nextId) return 0;
  return i === 0 ? child0[id] : i === 1 ? child1[id] : i === 2 ? child2[id] : i === 3 ? child3[id] : child4[id];
}

/** Check if value is a valid term index */
function isTerm(v) {
  return typeof v === 'number' && v >= 1 && v < nextId;
}

/** Check if child value is a term reference (vs string/bigint primitive) */
function isTermChild(c) {
  return typeof c === 'number';
}

// Registered cleanup callbacks invoked on clear().
// Used by subsystems (e.g., backward cache) that hold Store-dependent state.
const _clearHooks = [];
function onClear(fn) { _clearHooks.push(fn); }

/** Clear the store (for testing) */
function clear() {
  nextId = 1; // reserve 0 as null sentinel
  DEDUP.clear();
  stringTable.clear();
  bigIntTable.clear();
  ARRAY_TABLE.length = 0;
  nextArrayId = 0;
  // TypedArrays: no need to zero — slots >= nextId are never read
  for (let i = 0; i < _clearHooks.length; i++) _clearHooks[i]();
}

/** Get store size (number of terms) */
function size() {
  return nextId - 1; // exclude sentinel
}

// Convenience: equality is just index comparison
const eq = (a, b) => a === b;

/**
 * Snapshot the current Store state for binary serialization.
 * Returns copies of all internal arrays (safe to serialize independently).
 * @param {Object} [metadata] - SDK metadata to include in snapshot
 * @returns {Object} snapshot data
 */
function snapshot(metadata) {
  const n = nextId - 1; // number of entries (excluding sentinel)

  // Copy SoA slices (indices 1..nextId-1 → 0..n-1 in output)
  const snapTags = new Uint8Array(n);
  const snapArities = new Uint8Array(n);
  const snapChild0 = new Uint32Array(n);
  const snapChild1 = new Uint32Array(n);
  const snapChild2 = new Uint32Array(n);
  const snapChild3 = new Uint32Array(n);
  const snapChild4 = new Uint32Array(n);

  snapTags.set(tags.subarray(1, nextId));
  snapArities.set(arities.subarray(1, nextId));
  snapChild0.set(child0.subarray(1, nextId));
  snapChild1.set(child1.subarray(1, nextId));
  snapChild2.set(child2.subarray(1, nextId));
  snapChild3.set(child3.subarray(1, nextId));
  snapChild4.set(child4.subarray(1, nextId));

  // Precompute content hashes for DEDUP rebuild
  const dedupHashes = new Uint32Array(n);
  for (const [hash, id] of DEDUP) {
    dedupHashes[id - 1] = hash; // id is 1-based, array is 0-based
  }

  // Copy string and bigint tables
  const snapStrings = stringTable.snapshot();
  const snapBigints = bigIntTable.snapshot();

  // Copy array table (flatten to contiguous data for each entry)
  const snapArrays = ARRAY_TABLE.slice(0, nextArrayId).map(e => ({
    data: e.data.slice(e.offset, e.offset + e.length)
  }));

  // Copy tag registry
  const snapTagNames = TAG_NAMES.slice(0, nextTag);

  return {
    nodeCount: n,
    tags: snapTags,
    arities: snapArities,
    child0: snapChild0,
    child1: snapChild1,
    child2: snapChild2,
    child3: snapChild3,
    child4: snapChild4,
    dedupHashes,
    strings: snapStrings,
    bigints: snapBigints,
    arrays: snapArrays,
    tagNames: snapTagNames,
    metadata: metadata || {}
  };
}

/**
 * Restore Store state from a snapshot (e.g. deserialized binary).
 * Clears current state and bulk-copies all arrays.
 * @param {Object} data - snapshot data (from deserialize)
 */
function restore(data) {
  const { nodeCount, tags: dTags, arities: dArities,
          child0: dC0, child1: dC1, child2: dC2, child3: dC3, child4: dC4,
          dedupHashes, strings, bigints, arrays, tagNames } = data;

  // Ensure capacity
  const needed = nodeCount + 1; // +1 for sentinel
  while (needed > capacity) grow();

  // Reset dynamic tags (>= PRED_BOUNDARY)
  for (let i = PRED_BOUNDARY; i < nextTag; i++) {
    delete TAG[TAG_NAMES[i]];
  }
  TAG_NAMES.length = PRED_BOUNDARY;
  nextTag = PRED_BOUNDARY;

  // Restore tag registry (re-register dynamic tags from snapshot)
  for (let i = PRED_BOUNDARY; i < tagNames.length; i++) {
    registerTag(tagNames[i]);
  }

  // Bulk memcpy SoA arrays (snapshot is 0-based, Store is 1-based)
  tags.set(dTags, 1);
  arities.set(dArities, 1);
  child0.set(dC0, 1);
  child1.set(dC1, 1);
  child2.set(dC2, 1);
  child3.set(dC3, 1);
  if (dC4) child4.set(dC4, 1);
  nextId = nodeCount + 1;

  // Rebuild DEDUP map from precomputed hashes
  DEDUP.clear();
  for (let i = 0; i < nodeCount; i++) {
    DEDUP.set(dedupHashes[i], i + 1); // 0-based → 1-based
  }

  // Restore string table
  stringTable.restore(strings);

  // Restore bigint table
  bigIntTable.restore(bigints);

  // Restore array table
  ARRAY_TABLE.length = 0;
  nextArrayId = 0;
  if (arrays) {
    for (const entry of arrays) {
      const data = entry.data instanceof Uint32Array ? entry.data : new Uint32Array(entry.data);
      ARRAY_TABLE.push({ data, offset: 0, length: data.length });
      nextArrayId++;
    }
  }
}

module.exports = {
  put,
  put1,
  put2,
  get,
  tag,
  tagId,
  children,
  child,
  rawChild,
  arity,
  isTerm,
  isTermChild,
  eq,
  clear,
  size,
  snapshot,
  restore,
  TAG,
  TAG_NAMES,
  PRED_BOUNDARY,
  ARRAY_CHILD_TAGS,
  registerTag,
  storeArray,
  getArrayEntry,
  getArrayElements,
  putArray,
  onClear,
  LEAF_TAGS,
};
