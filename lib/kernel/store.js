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

const { hashString, hashCombine, hashBigInt } = require('../hash');

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

// Pre-register all known non-predicate tags
['atom', 'freevar', 'tensor', 'loli', 'with', 'bang', 'one', 'type',
 'arrow', 'monad', 'app', 'binlit', 'strlit', 'charlit',
 'var', 'any', 'hyp', 'comma', 'empty', 'seq', 'deriv'].forEach(registerTag);

// Tag-based child type discrimination (set after registration)
const STRING_CHILD_TAGS = new Uint8Array(256);
STRING_CHILD_TAGS[TAG.atom] = 1;
STRING_CHILD_TAGS[TAG.freevar] = 1;
STRING_CHILD_TAGS[TAG.strlit] = 1;

const BIGINT_CHILD_TAGS = new Uint8Array(256);
BIGINT_CHILD_TAGS[TAG.binlit] = 1;

// charlit: child is raw uint32 codepoint (not a term ref, not a string)
// No special table needed — stored directly in child0

// =============================================================================
// String Interning
// =============================================================================

const STRING_TO_ID = new Map();
const ID_TO_STRING = [];
let nextStringId = 0;

function internString(s) {
  let id = STRING_TO_ID.get(s);
  if (id === undefined) {
    id = nextStringId++;
    STRING_TO_ID.set(s, id);
    ID_TO_STRING.push(s);
  }
  return id;
}

function getString(id) { return ID_TO_STRING[id]; }

// =============================================================================
// BigInt Side Table
// =============================================================================

const BIGINT_TABLE = [];
let nextBigIntId = 0;

function storeBigInt(value) {
  const id = nextBigIntId++;
  BIGINT_TABLE.push(value);
  return id;
}

function getBigInt(id) { return BIGINT_TABLE[id]; }

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
  newTags.set(tags);
  newArities.set(arities);
  newChild0.set(child0);
  newChild1.set(child1);
  newChild2.set(child2);
  newChild3.set(child3);
  tags = newTags;
  arities = newArities;
  child0 = newChild0;
  child1 = newChild1;
  child2 = newChild2;
  child3 = newChild3;
  capacity = newCap;
}

// =============================================================================
// Hashing (same FNV-1a as before, for dedup)
// =============================================================================

function computeHash(tag, children) {
  let h = hashString(tag);
  h = hashCombine(h, children.length);
  for (const c of children) {
    if (typeof c === 'number') {
      h = hashCombine(h, c);
    } else if (typeof c === 'bigint') {
      h = hashCombine(h, hashBigInt(c));
    } else {
      h = hashCombine(h, hashString(String(c)));
    }
  }
  return h;
}

// =============================================================================
// Core API
// =============================================================================

/**
 * Put a node: store if new, return sequential index (content-addressed).
 * @param {string} tagName - Node tag
 * @param {(number|string|bigint)[]} children - Child values
 * @returns {number} Sequential index for this node
 */
function put(tagName, children) {
  const h = computeHash(tagName, children);
  const existing = DEDUP.get(h);
  if (existing !== undefined) return existing;

  if (nextId >= capacity) grow();

  const id = nextId++;
  DEDUP.set(h, id);

  const tagId = TAG[tagName] !== undefined ? TAG[tagName] : registerTag(tagName);
  tags[id] = tagId;
  arities[id] = children.length;

  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    let val;
    if (typeof c === 'string') {
      val = internString(c);
    } else if (typeof c === 'bigint') {
      val = storeBigInt(c);
    } else {
      val = c; // term index or raw number (charlit codepoint)
    }
    if (i === 0) child0[id] = val;
    else if (i === 1) child1[id] = val;
    else if (i === 2) child2[id] = val;
    else child3[id] = val;
  }

  return id;
}

/** Reconstruct child value from raw uint32 based on parent tag */
function reconstructChild(id, i) {
  const raw = i === 0 ? child0[id] : i === 1 ? child1[id] : i === 2 ? child2[id] : child3[id];
  const t = tags[id];
  if (STRING_CHILD_TAGS[t]) return getString(raw);
  if (BIGINT_CHILD_TAGS[t]) return getBigInt(raw);
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

/** Check if value is a valid term index */
function isTerm(v) {
  return typeof v === 'number' && v >= 1 && v < nextId;
}

/** Check if child value is a term reference (vs string/bigint primitive) */
function isTermChild(c) {
  return typeof c === 'number';
}

/** Clear the store (for testing) */
function clear() {
  nextId = 1; // reserve 0 as null sentinel
  DEDUP.clear();
  STRING_TO_ID.clear();
  ID_TO_STRING.length = 0;
  nextStringId = 0;
  BIGINT_TABLE.length = 0;
  nextBigIntId = 0;
  // TypedArrays: no need to zero — slots >= nextId are never read
}

/** Get store size (number of terms) */
function size() {
  return nextId - 1; // exclude sentinel
}

/** Debug: dump store contents */
function dump() {
  const entries = [];
  for (let id = 1; id < nextId; id++) {
    const node = get(id);
    entries.push({ hash: id, ...node });
  }
  return entries;
}

// Convenience: equality is just index comparison
const eq = (a, b) => a === b;

module.exports = {
  put,
  get,
  tag,
  children,
  child,
  arity,
  isTerm,
  isTermChild,
  eq,
  clear,
  size,
  dump,
  // Tag registry (for hot-path integer comparison)
  TAG,
  TAG_NAMES,
  registerTag,
};
