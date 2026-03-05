/**
 * FactSet — Sorted typed-array state representation.
 *
 * Per-tag grouped sorted Int32Arrays with incremental Zobrist hashing
 * and arena-based undo for backtracking in explore.
 *
 * State IS the index: FactSet.group(tagIdx) replaces buildStateIndex.
 */

const Store = require('../kernel/store');

// ─── Zobrist Hash Mixer ─────────────────────────────────────────────

/**
 * Mix a (hash, count) pair into a 32-bit Zobrist contribution.
 * Order-independent: XOR of contributions gives state fingerprint.
 * Count-dependent: changing count changes contribution (multiset-safe).
 */
function hashFactEntry(h, count) {
  let x = Math.imul(h | 0, 2654435761) ^ Math.imul(count | 0, 2246822519);
  x = Math.imul(x ^ (x >>> 16), 0x45d9f3b);
  x = Math.imul(x ^ (x >>> 13), 0x45d9f3b);
  return (x ^ (x >>> 16)) >>> 0;
}

// ─── Binary Search ──────────────────────────────────────────────────

/**
 * Find leftmost insertion point for val in buf[lo..hi).
 * Returns index where val should be inserted to maintain sorted order.
 */
function lowerBound(buf, lo, hi, val) {
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (buf[mid] < val) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

// ─── Arena (undo log) ───────────────────────────────────────────────

const INSERT_OP = 0;
const REMOVE_OP = 1;

class Arena {
  constructor(capacity = 16384) {
    this.buf = new Int32Array(capacity);
    this.cursor = 0;
  }

  checkpoint() {
    return this.cursor;
  }

  push4(a, b, c, d) {
    const c0 = this.cursor;
    if (c0 + 4 > this.buf.length) {
      const nb = new Int32Array(this.buf.length * 2);
      nb.set(this.buf);
      this.buf = nb;
    }
    this.buf[c0] = a;
    this.buf[c0 + 1] = b;
    this.buf[c0 + 2] = c;
    this.buf[c0 + 3] = d;
    this.cursor = c0 + 4;
  }

  restore(checkpoint) {
    this.cursor = checkpoint;
  }
}

// ─── FactSet ────────────────────────────────────────────────────────

const DEFAULT_GROUP_CAP = 8;

class FactSet {
  /**
   * @param {number} maxTagId - Number of tag slots to allocate
   */
  constructor(maxTagId) {
    this.maxTagId = maxTagId;
    this.groups = new Array(maxTagId);    // Int32Array per tag (sorted)
    this.lens = new Int32Array(maxTagId); // current length per group
    this.hash = 0;                        // Zobrist hash
    this.total = 0;                       // total fact count
    // groups are lazily allocated on first insert
  }

  _initGroup(tagIdx, initialCap) {
    const cap = Math.max(initialCap, DEFAULT_GROUP_CAP);
    this.groups[tagIdx] = new Int32Array(cap);
  }

  _grow(tagIdx) {
    const old = this.groups[tagIdx];
    const ng = new Int32Array(old.length * 2);
    ng.set(old);
    this.groups[tagIdx] = ng;
  }

  /**
   * Insert fact hash into the group for tagIdx.
   * Maintains sorted order and incremental Zobrist hash.
   * Records undo entry in arena if provided.
   */
  insert(tagIdx, hash, arena) {
    if (!this.groups[tagIdx]) this._initGroup(tagIdx, DEFAULT_GROUP_CAP);
    const len = this.lens[tagIdx];
    if (len >= this.groups[tagIdx].length) this._grow(tagIdx);

    const buf = this.groups[tagIdx];
    const pos = lowerBound(buf, 0, len, hash);

    // Count current occurrences for Zobrist update
    const oldCount = this._countAt(buf, pos, len, hash);

    // Shift right to make room
    for (let i = len; i > pos; i--) buf[i] = buf[i - 1];
    buf[pos] = hash;
    this.lens[tagIdx] = len + 1;
    this.total++;

    // Update Zobrist: XOR out old contribution, XOR in new
    if (oldCount > 0) this.hash ^= hashFactEntry(hash, oldCount);
    this.hash ^= hashFactEntry(hash, oldCount + 1);

    if (arena) arena.push4(INSERT_OP, tagIdx, hash, 0);
  }

  /**
   * Remove one instance of fact hash from the group for tagIdx.
   * Maintains sorted order and incremental Zobrist hash.
   * Records undo entry in arena if provided.
   */
  remove(tagIdx, hash, arena) {
    const buf = this.groups[tagIdx];
    const len = this.lens[tagIdx];
    if (!buf || len === 0) return;

    const pos = lowerBound(buf, 0, len, hash);
    if (pos >= len || buf[pos] !== hash) return; // not found

    // Count current occurrences for Zobrist update
    const oldCount = this._countAt(buf, pos, len, hash);

    // Shift left to fill gap
    for (let i = pos; i < len - 1; i++) buf[i] = buf[i + 1];
    this.lens[tagIdx] = len - 1;
    this.total--;

    // Update Zobrist: XOR out old contribution, XOR in new (if any remain)
    this.hash ^= hashFactEntry(hash, oldCount);
    if (oldCount > 1) this.hash ^= hashFactEntry(hash, oldCount - 1);

    if (arena) arena.push4(REMOVE_OP, tagIdx, hash, 0);
  }

  /**
   * Undo operations recorded in arena from current cursor back to checkpoint.
   * Walks backward, performing symmetric insert/remove without recording.
   */
  undo(arena, checkpoint) {
    const buf = arena.buf;
    for (let i = arena.cursor - 4; i >= checkpoint; i -= 4) {
      const op = buf[i];
      const tagIdx = buf[i + 1];
      const hash = buf[i + 2];
      if (op === INSERT_OP) {
        // Undo insert → remove (no arena recording)
        this._removeNoArena(tagIdx, hash);
      } else {
        // Undo remove → insert (no arena recording)
        this._insertNoArena(tagIdx, hash);
      }
    }
    arena.cursor = checkpoint;
  }

  /** Internal insert without arena recording (for undo) */
  _insertNoArena(tagIdx, hash) {
    if (!this.groups[tagIdx]) this._initGroup(tagIdx, DEFAULT_GROUP_CAP);
    const len = this.lens[tagIdx];
    if (len >= this.groups[tagIdx].length) this._grow(tagIdx);

    const buf = this.groups[tagIdx];
    const pos = lowerBound(buf, 0, len, hash);
    const oldCount = this._countAt(buf, pos, len, hash);

    for (let i = len; i > pos; i--) buf[i] = buf[i - 1];
    buf[pos] = hash;
    this.lens[tagIdx] = len + 1;
    this.total++;

    if (oldCount > 0) this.hash ^= hashFactEntry(hash, oldCount);
    this.hash ^= hashFactEntry(hash, oldCount + 1);
  }

  /** Internal remove without arena recording (for undo) */
  _removeNoArena(tagIdx, hash) {
    const buf = this.groups[tagIdx];
    const len = this.lens[tagIdx];
    if (!buf || len === 0) return;

    const pos = lowerBound(buf, 0, len, hash);
    if (pos >= len || buf[pos] !== hash) return;

    const oldCount = this._countAt(buf, pos, len, hash);

    for (let i = pos; i < len - 1; i++) buf[i] = buf[i + 1];
    this.lens[tagIdx] = len - 1;
    this.total--;

    this.hash ^= hashFactEntry(hash, oldCount);
    if (oldCount > 1) this.hash ^= hashFactEntry(hash, oldCount - 1);
  }

  /**
   * Count consecutive entries equal to hash starting at pos.
   * buf must be sorted.
   */
  _countAt(buf, pos, len, hash) {
    let count = 0;
    for (let i = pos; i < len && buf[i] === hash; i++) count++;
    // Also check left of pos (entries before the insertion point may equal hash)
    // No — lowerBound returns leftmost position, so all equal entries are at pos..pos+count-1
    return count;
  }

  /** Deep copy of this FactSet. Independent copy. */
  snapshot() {
    const fs = new FactSet(this.maxTagId);
    fs.hash = this.hash;
    fs.total = this.total;
    for (let i = 0; i < this.maxTagId; i++) {
      const len = this.lens[i];
      if (len > 0) {
        fs.groups[i] = new Int32Array(this.groups[i].buffer.slice(0, len * 4));
        fs.lens[i] = len;
      }
    }
    return fs;
  }

  /**
   * Read-only bulk snapshot: all groups packed into one Int32Array.
   * Returns a new FactSet where group views share one backing buffer.
   * One allocation instead of 30-40 per-group slices.
   * DO NOT insert/remove from the returned FactSet — groups share a buffer.
   */
  snapshotBulk() {
    const fs = new FactSet(this.maxTagId);
    fs.hash = this.hash;
    fs.total = this.total;

    let totalLen = 0;
    for (let i = 0; i < this.maxTagId; i++) totalLen += this.lens[i];

    if (totalLen > 0) {
      const bulk = new Int32Array(totalLen);
      let pos = 0;
      for (let i = 0; i < this.maxTagId; i++) {
        const len = this.lens[i];
        if (len > 0) {
          bulk.set(this.groups[i].subarray(0, len), pos);
          fs.groups[i] = bulk.subarray(pos, pos + len);
          fs.lens[i] = len;
          pos += len;
        }
      }
    }
    return fs;
  }

  /** Zero-copy subarray view of group entries. Returns Int32Array of length groupLen. */
  group(tagIdx) {
    const len = this.lens[tagIdx];
    if (!len) return _emptyI32;
    return this.groups[tagIdx].subarray(0, len);
  }

  /** Number of entries in group. */
  groupLen(tagIdx) {
    return this.lens[tagIdx];
  }

  /** Check if hash exists in group (binary search). */
  has(tagIdx, hash) {
    const len = this.lens[tagIdx];
    if (!len) return false;
    const pos = lowerBound(this.groups[tagIdx], 0, len, hash);
    return pos < len && this.groups[tagIdx][pos] === hash;
  }

  /** Count occurrences of hash in group. */
  count(tagIdx, hash) {
    const len = this.lens[tagIdx];
    if (!len) return 0;
    const buf = this.groups[tagIdx];
    const pos = lowerBound(buf, 0, len, hash);
    if (pos >= len || buf[pos] !== hash) return 0;
    let c = 0;
    for (let i = pos; i < len && buf[i] === hash; i++) c++;
    return c;
  }

  /** Iterate all facts across all groups. Calls fn(hash) for each. */
  forEach(fn) {
    for (let t = 0; t < this.maxTagId; t++) {
      const len = this.lens[t];
      if (!len) continue;
      const buf = this.groups[t];
      for (let i = 0; i < len; i++) fn(buf[i]);
    }
  }
}

const _emptyI32 = new Int32Array(0);

// ─── State ──────────────────────────────────────────────────────────

/**
 * State wraps linear FactSet + persistent FactSet.
 * Replaces { linear: {hash:count}, persistent: {hash:true} } objects
 * and the parallel stateIndex.
 */
class State {
  constructor(linear, persistent) {
    this.linear = linear;       // FactSet (multiset)
    this.persistent = persistent; // FactSet (set — no duplicates)
    // Secondary index for fingerprint (set during init)
    this._byKey = null;
    this._fpPred = null;
    this._fpKeyPos = -1;
  }

  get stateHash() {
    // Combine linear and persistent hashes.
    // Use different mixing for persistent to avoid collisions.
    return (this.linear.hash ^ Math.imul(this.persistent.hash, 2654435761)) >>> 0;
  }

  /** Deep copy of this State. */
  snapshot() {
    const s = new State(this.linear.snapshot(), this.persistent.snapshot());
    s._byKey = this._byKey;   // shared ref (read-only during execution)
    s._fpPred = this._fpPred;
    s._fpKeyPos = this._fpKeyPos;
    return s;
  }

  /**
   * Read-only bulk snapshot: one Int32Array per FactSet instead of 30-40.
   * Returns a State with full API compatibility (group, groupLen, has, etc.)
   * but the backing groups share a single ArrayBuffer.
   * DO NOT mutate (insert/remove) the returned State.
   */
  snapshotBulk() {
    const s = new State(this.linear.snapshotBulk(), this.persistent.snapshotBulk());
    s._byKey = this._byKey;
    s._fpPred = this._fpPred;
    s._fpKeyPos = this._fpKeyPos;
    return s;
  }

  /** Check if hash exists in linear FactSet. */
  hasLinear(hash) {
    return this.linear.has(Store.tagId(hash), hash);
  }

  /** Clone for committed-choice (forward.run). */
  clone() {
    return this.snapshot();
  }

  /**
   * Check if a predicate (by name) has any facts in the linear state.
   * Handles both predicate tags (ID >= PRED_BOUNDARY) and atoms (tag 0).
   * Used by strategy layers for trigger predicate checks.
   */
  hasPredicate(predName) {
    const tagId = Store.TAG[predName];
    if (tagId !== undefined && tagId >= Store.PRED_BOUNDARY) {
      return this.linear.groupLen(tagId) > 0;
    }
    // Atom check: scan atom group for matching name
    const atomTagId = Store.TAG.atom;
    const atomGroup = this.linear.group(atomTagId);
    for (let i = 0; i < atomGroup.length; i++) {
      if (Store.child(atomGroup[i], 0) === predName) return true;
    }
    return false;
  }

  /**
   * Get the group of linear facts for a predicate name.
   * For predicate tags: returns the tag's group directly.
   * For atoms: returns atom group (caller must filter by name).
   * For unknown preds: returns empty.
   */
  groupForPred(predName) {
    if (!predName) return _emptyI32;
    const tagId = Store.TAG[predName];
    if (tagId !== undefined && tagId >= Store.PRED_BOUNDARY) {
      return this.linear.group(tagId);
    }
    // Atom predicate: return entire atom group (caller filters)
    return this.linear.group(Store.TAG.atom);
  }
}

// ─── Conversion ─────────────────────────────────────────────────────

/**
 * Build State from { linear: {hash:count}, persistent: {hash:true} } objects.
 */
function fromObject(linearObj, persistentObj) {
  const maxTagId = Store.TAG_NAMES.length;
  const linear = new FactSet(maxTagId);
  const persistent = new FactSet(maxTagId);

  for (const hStr in linearObj) {
    const h = Number(hStr);
    const count = linearObj[hStr];
    if (count <= 0) continue;
    const tagIdx = Store.tagId(h);
    for (let c = 0; c < count; c++) {
      linear.insert(tagIdx, h, null);
    }
  }

  for (const hStr in persistentObj) {
    const h = Number(hStr);
    const tagIdx = Store.tagId(h);
    persistent.insert(tagIdx, h, null);
  }

  return new State(linear, persistent);
}

/**
 * Convert State back to { linear: {hash:count}, persistent: {hash:true} } objects.
 * For API compatibility (tests, debug, show.js).
 */
function toObject(state) {
  const linear = {};
  const persistent = {};

  for (let t = 0; t < state.linear.maxTagId; t++) {
    const len = state.linear.lens[t];
    if (!len) continue;
    const buf = state.linear.groups[t];
    for (let i = 0; i < len; i++) {
      linear[buf[i]] = (linear[buf[i]] || 0) + 1;
    }
  }

  for (let t = 0; t < state.persistent.maxTagId; t++) {
    const len = state.persistent.lens[t];
    if (!len) continue;
    const buf = state.persistent.groups[t];
    for (let i = 0; i < len; i++) {
      persistent[buf[i]] = true;
    }
  }

  return { linear, persistent };
}

module.exports = {
  // Primitives
  hashFactEntry,
  lowerBound,
  // Classes
  FactSet,
  Arena,
  State,
  // Conversion
  fromObject,
  toObject,
  // Constants
  INSERT_OP,
  REMOVE_OP,
};
