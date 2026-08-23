/**
 * FactSet — Sorted typed-array state representation.
 *
 * Per-tag grouped sorted Int32Arrays with incremental Zobrist hashing
 * and arena-based undo for backtracking in explore.
 *
 * State IS the index: FactSet.group(tagIdx) replaces buildStateIndex.
 */

import Store from '../kernel/store.js';
import { StampTable, packRef, refInner, refStamp, INNER_CAP } from './labels.js';
// ─── Zobrist Hash Mixer ─────────────────────────────────────────────

/**
 * Mix a (hash, count) pair into a 32-bit Zobrist contribution.
 * Order-independent: XOR of contributions gives state fingerprint.
 * Count-dependent: changing count changes contribution (multiset-safe).
 */
function zobristMix(h, count) {
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

  /** Label-mode record: (op, group, inner, sid, count) — a packed ref
   *  exceeds Int32, so label rows log their two halves (THY_0024). A
   *  FactSet writes 4-int or 5-int records exclusively (its own stride);
   *  zones own separate arenas, so strides never mix in one buffer. */
  push5(a, b, c, d, e) {
    const c0 = this.cursor;
    if (c0 + 5 > this.buf.length) {
      const nb = new Int32Array(this.buf.length * 2);
      nb.set(this.buf);
      this.buf = nb;
    }
    this.buf[c0] = a;
    this.buf[c0 + 1] = b;
    this.buf[c0 + 2] = c;
    this.buf[c0 + 3] = d;
    this.buf[c0 + 4] = e;
    this.cursor = c0 + 5;
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
   * @param {Object} [policy] - Index policy (TODO_0265 Phase 3, D5/D13:
   *   "the index is optimization, the multiset is semantics"):
   *     groupKey: (hash) => int  — which group a fact files under
   *                                (default: the caller-passed tagIdx,
   *                                i.e. Store.tagId; till files at(A,t)
   *                                under A's predicate tag)
   *     cmp: (a, b) => int       — within-group order (default: hash
   *                                order; till: stamp, then hash — the
   *                                FIFO cohort index)
   *   Absent ⇒ bit-identical to the historical behavior. A policy may
   *   never change WHICH matches exist, only how candidates are found —
   *   see the index-equivalence acceptance test.
   */
  /**
   * maxTagId is the initial group capacity; a policy groupKey may return
   * ids beyond it (per-atom-name groups, TODO_0277) — groups grow on
   * demand and maxTagId tracks the high-water mark, so every `for t <
   * maxTagId` iteration stays exhaustive.
   */
  constructor(maxTagId, policy = null) {
    this.maxTagId = maxTagId;
    this.policy = policy;
    this._gk = (policy && policy.groupKey) || null;
    this._cmp = (policy && policy.cmp) || null;
    // Run-length representation (TODO_0277): groups hold DISTINCT hashes,
    // a parallel counts array carries multiplicity. Memory and per-op cost
    // become O(distinct facts) instead of O(total tokens) — a !_10^6 parcel
    // is one entry. Zobrist contributions are zobristMix(hash, count) in
    // both representations, so state hashes are bit-identical across them.
    // Label-column mode (THY_0024, TODO_0278 B2): rows are
    // (innerHash, stampId, count) — groups[] holds the INNER column
    // (time-stable content addresses), sids[] the stamp column (ids into
    // the per-set StampTable), counts[] the multiplicity. The public fact
    // handle is the packed 52-bit ref (labels.js). Implies run-length.
    this._lab = !!(policy && policy.labels);
    this.stamps = this._lab ? new StampTable(policy.labels) : null;
    this._rl = this._lab || !!(policy && policy.runLength);
    this.groups = new Array(maxTagId);    // Int32Array per tag (sorted)
    this.sids = this._lab ? new Array(maxTagId) : null;  // Int32Array per tag
    this.counts = this._rl ? new Array(maxTagId) : null; // Int32Array per tag
    this.lens = new Int32Array(maxTagId); // current length per group
    this.hash = 0;                        // Zobrist hash
    this.total = 0;                       // total fact count
    this.mut = 0;                         // mutation counter (monotone; any
                                          // insert/remove/undo bumps it —
                                          // deterministic change detection)
    // groups are lazily allocated on first insert
  }

  /** Resolve the group for a fact: policy groupKey wins over the passed
   *  tagIdx. Grows the group tables when the policy hands out a fresh id. */
  _key(tagIdx, hash) {
    if (!this._gk) return tagIdx;
    const k = this._gk(this._lab ? refInner(hash) : hash);
    if (k >= this.maxTagId) this._growTables(k + 1);
    return k;
  }

  _growTables(need) {
    const cap = Math.max(need, this.maxTagId * 2);
    const nl = new Int32Array(cap);
    nl.set(this.lens);
    this.lens = nl;
    this.groups.length = cap;
    if (this._rl) this.counts.length = cap;
    if (this._lab) this.sids.length = cap;
    this.maxTagId = cap;
  }

  /** lowerBound under the policy comparator (hash order when absent). */
  _lb(buf, len, val) {
    const cmp = this._cmp;
    if (!cmp) return lowerBound(buf, 0, len, val);
    let lo = 0, hi = len;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (cmp(buf[mid], val) < 0) lo = mid + 1;
      else hi = mid;
    }
    return lo;
  }

  _initGroup(tagIdx, initialCap) {
    const cap = Math.max(initialCap, DEFAULT_GROUP_CAP);
    this.groups[tagIdx] = new Int32Array(cap);
    if (this._rl) this.counts[tagIdx] = new Int32Array(cap);
    if (this._lab) this.sids[tagIdx] = new Int32Array(cap);
  }

  _grow(tagIdx) {
    const old = this.groups[tagIdx];
    const ng = new Int32Array(old.length * 2);
    ng.set(old);
    this.groups[tagIdx] = ng;
    if (this._rl) {
      const oc = this.counts[tagIdx];
      const nc = new Int32Array(oc.length * 2);
      nc.set(oc);
      this.counts[tagIdx] = nc;
    }
    if (this._lab) {
      const os = this.sids[tagIdx];
      const ns = new Int32Array(os.length * 2);
      ns.set(os);
      this.sids[tagIdx] = ns;
    }
  }

  // ── Label-column row operations (THY_0024) ──

  /** Row Zobrist key: inner ⊕ VALUE-derived stamp mix (never the id —
   *  ids are history-dependent, hashes must not be; rider 2). */
  _mixRow(inner, sid) {
    return (Math.imul(inner, 0x9e3779b1) ^ this.stamps.mix(sid)) | 0;
  }

  /** lowerBound over rows ordered (stamp-major via table cmp, inner asc). */
  _lbL(k, sid, inner) {
    const st = this.stamps, sb = this.sids[k], ib = this.groups[k];
    let lo = 0, hi = this.lens[k];
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      const c = st.cmp(sb[mid], sid) || (ib[mid] - inner);
      if (c < 0) lo = mid + 1;
      else hi = mid;
    }
    return lo;
  }

  _rlAddL(k, inner, sid, n) {
    this.mut++;
    if (!this.groups[k]) this._initGroup(k, DEFAULT_GROUP_CAP);
    let len = this.lens[k];
    if (len >= this.groups[k].length) this._grow(k);
    const ib = this.groups[k], sb = this.sids[k], cnt = this.counts[k];
    const pos = this._lbL(k, sid, inner);
    let oldCount = 0;
    if (pos < len && ib[pos] === inner && sb[pos] === sid) {
      oldCount = cnt[pos];
      cnt[pos] = oldCount + n;
    } else {
      for (let i = len; i > pos; i--) { ib[i] = ib[i - 1]; sb[i] = sb[i - 1]; cnt[i] = cnt[i - 1]; }
      ib[pos] = inner; sb[pos] = sid; cnt[pos] = n;
      this.lens[k] = len + 1;
    }
    this.total += n;
    const m = this._mixRow(inner, sid);
    if (oldCount > 0) this.hash ^= zobristMix(m, oldCount);
    this.hash ^= zobristMix(m, oldCount + n);
  }

  /** Returns the count actually removed (clamped, mirrors _rlSub). */
  _rlSubL(k, inner, sid, n) {
    const ib = this.groups[k];
    const len = this.lens[k];
    if (!ib || len === 0) return 0;
    const pos = this._lbL(k, sid, inner);
    const sb = this.sids[k];
    if (pos >= len || ib[pos] !== inner || sb[pos] !== sid) return 0;
    const cnt = this.counts[k];
    const oldCount = cnt[pos];
    this.mut++;
    const take = n < oldCount ? n : oldCount;
    if (take === oldCount) {
      for (let i = pos; i < len - 1; i++) { ib[i] = ib[i + 1]; sb[i] = sb[i + 1]; cnt[i] = cnt[i + 1]; }
      this.lens[k] = len - 1;
    } else {
      cnt[pos] = oldCount - take;
    }
    this.total -= take;
    const m = this._mixRow(inner, sid);
    this.hash ^= zobristMix(m, oldCount);
    if (oldCount > take) this.hash ^= zobristMix(m, oldCount - take);
    return take;
  }

  /**
   * Insert n instances (default 1) of fact hash into the group for tagIdx.
   * Maintains sorted order and incremental Zobrist hash.
   * Records undo entry in arena if provided.
   */
  insert(tagIdx, hash, arena, n = 1) {
    if (n <= 0) return;
    tagIdx = this._key(tagIdx, hash);
    if (this._lab) {
      const inner = refInner(hash), sid = refStamp(hash);
      if (inner >= INNER_CAP) {
        throw new Error(`FactSet label mode: inner id ${inner} exceeds the packed-ref fence (2^29) — raise STAMP_BITS budget`);
      }
      this._rlAddL(tagIdx, inner, sid, n);
      if (arena) arena.push5(INSERT_OP, tagIdx, inner, sid, n);
      return;
    }
    if (this._rl) {
      this._rlAdd(tagIdx, hash, n);
      if (arena) arena.push4(INSERT_OP, tagIdx, hash, n);
      return;
    }
    for (let c = 0; c < n; c++) {
      this._insertOne(tagIdx, hash);
      if (arena) arena.push4(INSERT_OP, tagIdx, hash, 0);
    }
  }

  _insertOne(tagIdx, hash) {
    this.mut++;
    if (!this.groups[tagIdx]) this._initGroup(tagIdx, DEFAULT_GROUP_CAP);
    const len = this.lens[tagIdx];
    if (len >= this.groups[tagIdx].length) this._grow(tagIdx);

    const buf = this.groups[tagIdx];
    const pos = this._lb(buf, len, hash);

    // Count current occurrences for Zobrist update
    const oldCount = this._countAt(buf, pos, len, hash);

    // Shift right to make room
    for (let i = len; i > pos; i--) buf[i] = buf[i - 1];
    buf[pos] = hash;
    this.lens[tagIdx] = len + 1;
    this.total++;

    // Update Zobrist: XOR out old contribution, XOR in new
    if (oldCount > 0) this.hash ^= zobristMix(hash, oldCount);
    this.hash ^= zobristMix(hash, oldCount + 1);
  }

  /** Run-length count bump: +n at hash (inserting the entry if absent). */
  _rlAdd(tagIdx, hash, n) {
    this.mut++;
    if (!this.groups[tagIdx]) this._initGroup(tagIdx, DEFAULT_GROUP_CAP);
    let len = this.lens[tagIdx];
    if (len >= this.groups[tagIdx].length) this._grow(tagIdx);
    const buf = this.groups[tagIdx];
    const cnt = this.counts[tagIdx];
    const pos = this._lb(buf, len, hash);
    let oldCount = 0;
    if (pos < len && buf[pos] === hash) {
      oldCount = cnt[pos];
      cnt[pos] = oldCount + n;
    } else {
      for (let i = len; i > pos; i--) { buf[i] = buf[i - 1]; cnt[i] = cnt[i - 1]; }
      buf[pos] = hash;
      cnt[pos] = n;
      this.lens[tagIdx] = len + 1;
    }
    this.total += n;
    if (oldCount > 0) this.hash ^= zobristMix(hash, oldCount);
    this.hash ^= zobristMix(hash, oldCount + n);
  }

  /** Run-length count drop: -n at hash (removing the entry at zero).
   *  Clamps at the available count (mirrors the classic silent no-op).
   *  Returns the count actually removed. */
  _rlSub(tagIdx, hash, n) {
    const buf = this.groups[tagIdx];
    const len = this.lens[tagIdx];
    if (!buf || len === 0) return 0;
    const pos = this._lb(buf, len, hash);
    if (pos >= len || buf[pos] !== hash) return 0;
    const cnt = this.counts[tagIdx];
    const oldCount = cnt[pos];
    this.mut++;
    const take = n < oldCount ? n : oldCount;
    if (take === oldCount) {
      for (let i = pos; i < len - 1; i++) { buf[i] = buf[i + 1]; cnt[i] = cnt[i + 1]; }
      this.lens[tagIdx] = len - 1;
    } else {
      cnt[pos] = oldCount - take;
    }
    this.total -= take;
    this.hash ^= zobristMix(hash, oldCount);
    if (oldCount > take) this.hash ^= zobristMix(hash, oldCount - take);
    return take;
  }

  /**
   * Remove n instances (default 1) of fact hash from the group for tagIdx.
   * Maintains sorted order and incremental Zobrist hash.
   * Records undo entry in arena if provided.
   */
  remove(tagIdx, hash, arena, n = 1) {
    if (n <= 0) return;
    tagIdx = this._key(tagIdx, hash);
    if (this._lab) {
      const inner = refInner(hash), sid = refStamp(hash);
      const took = this._rlSubL(tagIdx, inner, sid, n);
      if (arena && took > 0) arena.push5(REMOVE_OP, tagIdx, inner, sid, took);
      return;
    }
    if (this._rl) {
      const took = this._rlSub(tagIdx, hash, n);
      if (arena && took > 0) arena.push4(REMOVE_OP, tagIdx, hash, took);
      return;
    }
    for (let c = 0; c < n; c++) {
      if (!this._removeOne(tagIdx, hash)) return;   // absent: stop (no phantom undo)
      if (arena) arena.push4(REMOVE_OP, tagIdx, hash, 0);
    }
  }

  _removeOne(tagIdx, hash) {
    const buf = this.groups[tagIdx];
    const len = this.lens[tagIdx];
    if (!buf || len === 0) return false;

    const pos = this._lb(buf, len, hash);
    if (pos >= len || buf[pos] !== hash) return false; // not found
    this.mut++;

    // Count current occurrences for Zobrist update
    const oldCount = this._countAt(buf, pos, len, hash);

    // Shift left to fill gap
    for (let i = pos; i < len - 1; i++) buf[i] = buf[i + 1];
    this.lens[tagIdx] = len - 1;
    this.total--;

    // Update Zobrist: XOR out old contribution, XOR in new (if any remain)
    this.hash ^= zobristMix(hash, oldCount);
    if (oldCount > 1) this.hash ^= zobristMix(hash, oldCount - 1);
    return true;
  }

  /**
   * Undo operations recorded in arena from current cursor back to checkpoint.
   * Walks backward, performing symmetric insert/remove without recording.
   * The 4th arena field carries the run-length count (0 ⇒ classic 1-copy op).
   */
  undo(arena, checkpoint) {
    const buf = arena.buf;
    if (this._lab) {
      // 5-int stride: (op, group, inner, sid, count)
      for (let i = arena.cursor - 5; i >= checkpoint; i -= 5) {
        const op = buf[i], k = buf[i + 1], inner = buf[i + 2], sid = buf[i + 3];
        const n = buf[i + 4] || 1;
        if (op === INSERT_OP) this._rlSubL(k, inner, sid, n);
        else this._rlAddL(k, inner, sid, n);
      }
      arena.cursor = checkpoint;
      return;
    }
    for (let i = arena.cursor - 4; i >= checkpoint; i -= 4) {
      const op = buf[i];
      const tagIdx = buf[i + 1];
      const hash = buf[i + 2];
      const n = buf[i + 3] || 1;
      if (op === INSERT_OP) {
        // Undo insert → remove (no arena recording)
        this._removeNoArena(tagIdx, hash, n);
      } else {
        // Undo remove → insert (no arena recording)
        this._insertNoArena(tagIdx, hash, n);
      }
    }
    arena.cursor = checkpoint;
  }

  /** Internal insert without arena recording (for undo). Receives the
   *  RESOLVED group index recorded in the arena — no groupKey re-derivation. */
  _insertNoArena(tagIdx, hash, n = 1) {
    if (this._rl) { this._rlAdd(tagIdx, hash, n); return; }
    for (let c = 0; c < n; c++) {
      this.mut++;
      if (!this.groups[tagIdx]) this._initGroup(tagIdx, DEFAULT_GROUP_CAP);
      const len = this.lens[tagIdx];
      if (len >= this.groups[tagIdx].length) this._grow(tagIdx);

      const buf = this.groups[tagIdx];
      const pos = this._lb(buf, len, hash);
      const oldCount = this._countAt(buf, pos, len, hash);

      for (let i = len; i > pos; i--) buf[i] = buf[i - 1];
      buf[pos] = hash;
      this.lens[tagIdx] = len + 1;
      this.total++;

      if (oldCount > 0) this.hash ^= zobristMix(hash, oldCount);
      this.hash ^= zobristMix(hash, oldCount + 1);
    }
  }

  /** Internal remove without arena recording (for undo). Receives the
   *  RESOLVED group index recorded in the arena — no groupKey re-derivation. */
  _removeNoArena(tagIdx, hash, n = 1) {
    if (this._rl) { this._rlSub(tagIdx, hash, n); return; }
    for (let c = 0; c < n; c++) {
      this.mut++;
      const buf = this.groups[tagIdx];
      const len = this.lens[tagIdx];
      if (!buf || len === 0) return;

      const pos = this._lb(buf, len, hash);
      if (pos >= len || buf[pos] !== hash) return;

      const oldCount = this._countAt(buf, pos, len, hash);

      for (let i = pos; i < len - 1; i++) buf[i] = buf[i + 1];
      this.lens[tagIdx] = len - 1;
      this.total--;

      this.hash ^= zobristMix(hash, oldCount);
      if (oldCount > 1) this.hash ^= zobristMix(hash, oldCount - 1);
    }
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
    const fs = new FactSet(this.maxTagId, this.policy);
    fs.hash = this.hash;
    fs.total = this.total;
    // Label mode: the stamp table is SHARED (append-only during branch
    // exploration; shiftAll/compact never run under live snapshots).
    if (this._lab) fs.stamps = this.stamps;
    for (let i = 0; i < this.maxTagId; i++) {
      const len = this.lens[i];
      if (len > 0) {
        fs.groups[i] = new Int32Array(this.groups[i].buffer.slice(0, len * 4));
        if (this._rl) fs.counts[i] = new Int32Array(this.counts[i].buffer.slice(0, len * 4));
        if (this._lab) fs.sids[i] = new Int32Array(this.sids[i].buffer.slice(0, len * 4));
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
    const fs = new FactSet(this.maxTagId, this.policy);
    fs.hash = this.hash;
    fs.total = this.total;
    if (this._lab) fs.stamps = this.stamps;

    let totalLen = 0;
    for (let i = 0; i < this.maxTagId; i++) totalLen += this.lens[i];

    if (totalLen > 0) {
      const bulk = new Int32Array(totalLen);
      const cbulk = this._rl ? new Int32Array(totalLen) : null;
      const sbulk = this._lab ? new Int32Array(totalLen) : null;
      let pos = 0;
      for (let i = 0; i < this.maxTagId; i++) {
        const len = this.lens[i];
        if (len > 0) {
          bulk.set(this.groups[i].subarray(0, len), pos);
          fs.groups[i] = bulk.subarray(pos, pos + len);
          if (this._rl) {
            cbulk.set(this.counts[i].subarray(0, len), pos);
            fs.counts[i] = cbulk.subarray(pos, pos + len);
          }
          if (this._lab) {
            sbulk.set(this.sids[i].subarray(0, len), pos);
            fs.sids[i] = sbulk.subarray(pos, pos + len);
          }
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

  /** Check if hash (label mode: packed ref) exists in group. */
  has(tagIdx, hash) {
    if (this._lab) return this.count(tagIdx, hash) > 0;
    tagIdx = this._key(tagIdx, hash);
    const len = this.lens[tagIdx];
    if (!len) return false;
    const pos = this._lb(this.groups[tagIdx], len, hash);
    return pos < len && this.groups[tagIdx][pos] === hash;
  }

  /** Count occurrences of hash (label mode: packed ref) in group. */
  count(tagIdx, hash) {
    tagIdx = this._key(tagIdx, hash);
    const len = this.lens[tagIdx];
    if (!len) return 0;
    if (this._lab) {
      const inner = refInner(hash), sid = refStamp(hash);
      const pos = this._lbL(tagIdx, sid, inner);
      const ib = this.groups[tagIdx];
      if (pos >= len || ib[pos] !== inner || this.sids[tagIdx][pos] !== sid) return 0;
      return this.counts[tagIdx][pos];
    }
    const buf = this.groups[tagIdx];
    const pos = this._lb(buf, len, hash);
    if (pos >= len || buf[pos] !== hash) return 0;
    if (this._rl) return this.counts[tagIdx][pos];
    let c = 0;
    for (let i = pos; i < len && buf[i] === hash; i++) c++;
    return c;
  }

  /** Multiplicities parallel to group(tagIdx) — run-length sets only
   *  (classic sets encode multiplicity as repeated entries). */
  groupCounts(tagIdx) {
    if (!this._rl) return null;
    const len = this.lens[tagIdx];
    if (!len) return _emptyI32;
    return this.counts[tagIdx].subarray(0, len);
  }

  /** Stamp-id column parallel to group(tagIdx) — label mode only. In
   *  label mode group(tagIdx) IS the inner column (content addresses);
   *  this returns the label column beside it. */
  groupSids(tagIdx) {
    if (!this._lab) return null;
    const len = this.lens[tagIdx];
    if (!len) return _emptyI32;
    return this.sids[tagIdx].subarray(0, len);
  }

  /** Iterate all facts across all groups. Calls fn(hash, count). Classic
   *  sets call once PER COPY (count 1); run-length sets once per DISTINCT
   *  hash with its multiplicity. */
  forEach(fn) {
    for (let t = 0; t < this.maxTagId; t++) {
      const len = this.lens[t];
      if (!len) continue;
      const buf = this.groups[t];
      if (this._lab) {
        const sb = this.sids[t], cnt = this.counts[t];
        for (let i = 0; i < len; i++) fn(packRef(buf[i], sb[i]), cnt[i]);
      } else if (this._rl) {
        const cnt = this.counts[t];
        for (let i = 0; i < len; i++) fn(buf[i], cnt[i]);
      } else {
        for (let i = 0; i < len; i++) fn(buf[i], 1);
      }
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
    // Atom check. Under a groupKey policy each atom head files in its own
    // group (TODO_0277) — one keyed lookup replaces the whole-group scan.
    if (this.linear._gk) {
      const inner = Store.put('atom', [predName]);
      return this.linear.groupLen(this.linear._key(Store.TAG.atom, inner)) > 0;
    }
    // Classic: scan atom group for matching name. The group may hold
    // at(atom, t) wrappers — unwrap to the inner atom before comparing
    // (audit round 12, F1). The stamp tag comes from the linear policy
    // (cc.factSetPolicy.stampTag); default 'at', dead for untimed calculi
    // whose atom group holds no stamped facts.
    const stampTag = (this.linear.policy && this.linear.policy.stampTag) || 'at';
    const atomTagId = Store.TAG.atom;
    const atomGroup = this.linear.group(atomTagId);
    for (let i = 0; i < atomGroup.length; i++) {
      let h = atomGroup[i];
      if (Store.tag(h) === stampTag) h = Store.child(h, 0);
      if (Store.child(h, 0) === predName) return true;
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
    // Atom predicate. Policy-keyed sets file each atom head in its own
    // group (TODO_0277) — exact candidates, no population scan.
    if (this.linear._gk) {
      const inner = Store.put('atom', [predName]);
      return this.linear.group(this.linear._key(Store.TAG.atom, inner));
    }
    // Classic: return entire atom group (caller filters)
    return this.linear.group(Store.TAG.atom);
  }
}

// ─── Conversion ─────────────────────────────────────────────────────

/**
 * Build State from { linear: {hash:count}, persistent: {hash:true} } objects.
 * @param {Object} [linearPolicy] - index policy for the linear FactSet
 *   (persistent stays default: no stamped persistents, D15)
 */
function fromObject(linearObj, persistentObj, linearPolicy) {
  const maxTagId = Store.TAG_NAMES.length;
  const linear = new FactSet(maxTagId, linearPolicy || null);
  const persistent = new FactSet(maxTagId);

  if (linear._lab) {
    // Label mode (THY_0024): the at-encoding is the BOUNDARY format —
    // decode at(A, t) into (inner, stampId) rows; bare facts default to
    // the unit label (D11).
    const stampTag = (linearPolicy && linearPolicy.stampTag) || 'at';
    for (const hStr in linearObj) {
      const h = Number(hStr);
      const count = linearObj[hStr];
      if (count <= 0) continue;
      let inner = h, sid = 0;
      if (Store.tag(h) === stampTag) {
        inner = Store.child(h, 0);
        sid = linear.stamps.internTerm(Store.child(h, 1));
      }
      linear.insert(Store.tagId(inner), packRef(inner, sid), null, count);
    }
  } else {
    for (const hStr in linearObj) {
      const h = Number(hStr);
      const count = linearObj[hStr];
      if (count <= 0) continue;
      linear.insert(Store.tagId(h), h, null, count);
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

  const ls = state.linear;
  const rl = ls._rl;
  if (ls._lab) {
    // Label mode: mint the at-encoding at the boundary (O(live), the
    // representation stays invisible outside the engine — THY_0024).
    const stampTag = (ls.policy && ls.policy.stampTag) || 'at';
    for (let t = 0; t < ls.maxTagId; t++) {
      const len = ls.lens[t];
      if (!len) continue;
      const ib = ls.groups[t], sb = ls.sids[t], cnt = ls.counts[t];
      for (let i = 0; i < len; i++) {
        const h = Store.put(stampTag, [ib[i], ls.stamps.term(sb[i])]);
        linear[h] = (linear[h] || 0) + cnt[i];
      }
    }
  } else {
  for (let t = 0; t < state.linear.maxTagId; t++) {
    const len = state.linear.lens[t];
    if (!len) continue;
    const buf = state.linear.groups[t];
    const cnt = rl ? state.linear.counts[t] : null;
    for (let i = 0; i < len; i++) {
      linear[buf[i]] = (linear[buf[i]] || 0) + (rl ? cnt[i] : 1);
    }
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

export { zobristMix, lowerBound, FactSet, Arena, State, fromObject, toObject, INSERT_OP };
export default { zobristMix, lowerBound, FactSet, Arena, State, fromObject, toObject, INSERT_OP };
