---
title: "Sorted Typed-Array State Representation for Symexec"
created: 2026-03-01
modified: 2026-03-01
summary: "Replace {hash:count} object state with per-predicate sorted Int32Arrays. Eliminates stateIndex as separate structure, incremental Zobrist hashing, arena-based undo. Measured: 16.6ms → 11.6ms (−30%) on solc symbolic multisig."
tags: [symexec, performance, data-structures, forward-engine, optimization, flat-arrays, TypedArrays, architecture, content-addressing, arena-allocation]
type: design
status: done
priority: 8
cluster: Performance
depends_on: []
required_by: [TODO_0005, TODO_0052, TODO_0056]
starred: true
---

# Sorted Typed-Array State Representation

## The Problem

Symexec state is `{ linear: { hash: count }, persistent: { hash: true } }` — two JS objects with numeric keys. A separate `stateIndex` groups facts by predicate for matching. This dual representation works but has three costs:

1. **Snapshot**: `{ ...state.linear }` spreading ~760 keys = **~148 µs** per terminal node (measured). Dominates state ops at ~1.8 ms total for the symbolic multisig tree (11 terminals).
2. **Index sync**: `makeChildCtx` + `undoIndexChanges` maintain stateIndex in parallel with state. ~2 µs per rule firing = ~930 µs total.
3. **No Zig path**: JS objects have no typed-array equivalent. `delete obj[key]` deoptimizes V8 hidden classes. `for (const k in obj)` allocates string keys.

## Dismissed Alternatives

**Model A — Store trie**: Content-addressed 16-ary trie in the Store. Free identity, free snapshots, state-space DAG. But Store.put costs ~976 ns per unique node. At O(log n) depth × 10 mutations/rule = ~100 µs per rule firing — **27× worse** than current mutation. Becomes viable only if Store.put drops below ~50 ns (possible in Zig, not JS).

**Model C — Versioned delta chain**: Explicit undo-log chain. Defers snapshot cost to access time. Only saves ~1.7 ms if terminals are never materialized, which isn't guaranteed. Adds ~200 ns/node for delta objects. Net win is modest (1.14× overall) and doesn't improve the data model.

**Model D — Hybrid (mutable + Store checkpoints)**: Store encoding at boundaries costs ~164 µs per checkpoint — same as current snapshot. No performance change.

## Design: Per-Predicate Sorted Typed Arrays (Model B)

### Core Idea

State IS the index. Each predicate tag gets its own sorted `Int32Array`. No separate stateIndex.

```
// Current (dual representation):
state.linear    = { 12345: 1, 23456: 1, 34567: 2, ... }   // flat object
stateIndex      = { pc: [12345], sh: [23456], code: [34567, ...], _loli: [...] }

// New (unified):
state.linear.groups[PC_TAG]   = Int32Array [12345]           // sorted within group
state.linear.groups[SH_TAG]   = Int32Array [23456]
state.linear.groups[CODE_TAG] = Int32Array [34567, 34567]    // count=2 → 2 entries
state.linear.groups[LOLI_TAG] = Int32Array [...]
state.linear.lens[PC_TAG]     = 1
state.linear.lens[CODE_TAG]   = 2
```

### Data Structures

```javascript
// Zig: groups = [MAX_TAGS]ArrayListUnmanaged(u32), lens = [MAX_TAGS]u32, hash = u32
class FactSet {
  constructor(maxTagId) {
    this.groups = new Array(maxTagId);     // Int32Array per tag
    this.lens   = new Int32Array(maxTagId); // used length per group
    this.hash   = 0;                        // additive Zobrist (incremental)
    this.total  = 0;                        // total fact count (all groups)
    for (let i = 0; i < maxTagId; i++) this.groups[i] = new Int32Array(0);
  }

  // Capacity policy: initial × 2 (min 8), double on overflow.
  // Proportional headroom: large groups (code: 700) get large spare (700),
  // small groups (pc: 1) get minimum (8). Total overhead ~6 KB for 760 facts.
  // During DFS, produce→undo oscillation stays well within 2× headroom
  // (zero reallocs). forward.run() falls back to doubling for unbounded growth.
  // Zig: ArrayListUnmanaged.ensureTotalCapacity(max(initialCount * 2, 8))
  _initGroup(tagIdx, initialCount) {
    this.groups[tagIdx] = new Int32Array(Math.max(initialCount * 2, 8));
  }
  _grow(tagIdx) {
    const old = this.groups[tagIdx];
    const next = new Int32Array(old.length * 2);
    next.set(old.subarray(0, this.lens[tagIdx]));
    this.groups[tagIdx] = next;
    return next;
  }
}

// Zig: buf = []u32, cursor = usize
class Arena {
  constructor(capacity) {
    this.buf    = new Int32Array(capacity);  // pre-allocated once per explore()
    this.cursor = 0;
  }
  checkpoint() { return this.cursor; }
  push4(a, b, c, d) {                       // Zig: inline fn, no bounds check
    const c0 = this.cursor;
    this.buf[c0] = a; this.buf[c0+1] = b;
    this.buf[c0+2] = c; this.buf[c0+3] = d;
    this.cursor = c0 + 4;
  }
}

// Full state
// Zig: struct { linear: FactSet, persistent: FactSet }
class State {
  constructor(maxTagId) {
    this.linear     = new FactSet(maxTagId);
    this.persistent = new FactSet(maxTagId);
  }
  get stateHash() {
    // Combine linear and persistent hashes
    // Zig: hash +% (persistent_hash *% 0x9E3779B9)
    return (this.linear.hash + Math.imul(this.persistent.hash, 0x9E3779B9)) | 0;
  }
}
```

### Predicate Group Indexing

Tag ID IS the group index. `Store.tagId(hash)` returns a small integer (0–255). Pre-registered tags (0–25) include `loli` (ID 3). Dynamic predicates start at 26 (`PRED_BOUNDARY`).

```javascript
// Zig: inline fn, just Store.tagId()
function groupIdx(factHash) {
  return Store.tagId(factHash);
  // atoms (tag 0): all share group 0 — stop, invalid, revert are rare (0-1 per state)
  // loli (tag 3): natural group — replaces _loli bucket
  // predicates (≥26): pc, sh, code, mem, ... — each gets own group
}
```

Special cases:
- **Atoms** (tag 0): `stop`, `invalid`, `revert` — group 0. Rare (0-1 per state). Filter within group by `Store.child(h, 0)`.
- **Loli** (tag 3): replaces `stateIndex._loli`. `state.linear.group(3)` gives all loli facts.
- **Fingerprint `_byKey`**: kept as separate small structure. Built once from the code group at initialization. Doesn't change during execution (code facts are preserved, same hashes re-produced). Zig: simple `HashMap(u32, u32)` or even `[MAX_PC]u32` direct array.

### Operations

#### Insert (produce a fact)

```javascript
// Zig: binary search via std.sort.binarySearch, shift via @memmove
FactSet.prototype.insert = function(tagIdx, hash, arena) {
  let buf = this.groups[tagIdx];
  const len = this.lens[tagIdx];
  if (len === buf.length) { buf = this._grow(tagIdx); }

  const pos = lowerBound(buf, 0, len, hash);

  // Record undo: [OP_INSERT=1, tagIdx, pos, hash]
  arena.push4(1, tagIdx, pos, hash);

  buf.copyWithin(pos + 1, pos, len);    // Zig: @memmove
  buf[pos] = hash;
  this.lens[tagIdx] = len + 1;
  this.total++;
  this.hash = (this.hash + mix(hash)) | 0;   // Zig: +% wrapping add
};
```

#### Remove (consume a fact)

```javascript
FactSet.prototype.remove = function(tagIdx, hash, arena) {
  const buf = this.groups[tagIdx];
  const len = this.lens[tagIdx];
  const pos = lowerBound(buf, 0, len, hash);

  // Record undo: [OP_REMOVE=0, tagIdx, pos, hash]
  arena.push4(0, tagIdx, pos, hash);

  buf.copyWithin(pos, pos + 1, len);    // Zig: @memmove
  this.lens[tagIdx] = len - 1;
  this.total--;
  this.hash = (this.hash - mix(hash)) | 0;   // Zig: -% wrapping sub
};
```

#### Undo (backtrack)

```javascript
// Zig: walk arena backward, symmetric insert/remove
FactSet.prototype.undo = function(arena, checkpoint) {
  for (let i = arena.cursor - 4; i >= checkpoint; i -= 4) {
    const op   = arena.buf[i];
    const tIdx = arena.buf[i + 1];
    const pos  = arena.buf[i + 2];
    const hash = arena.buf[i + 3];
    const buf  = this.groups[tIdx];
    const len  = this.lens[tIdx];
    if (op === 1) {        // undo INSERT → remove at pos
      buf.copyWithin(pos, pos + 1, len);
      this.lens[tIdx] = len - 1;
      this.total--;
      this.hash = (this.hash - mix(hash)) | 0;
    } else {               // undo REMOVE → re-insert at pos
      buf.copyWithin(pos + 1, pos, len);
      buf[pos] = hash;
      this.lens[tIdx] = len + 1;
      this.total++;
      this.hash = (this.hash + mix(hash)) | 0;
    }
  }
  arena.cursor = checkpoint;
};
```

#### Snapshot

```javascript
// Zig: allocate snapshot from a pool, @memcpy each group
FactSet.prototype.snapshot = function() {
  const snap = { groups: new Array(this.groups.length), lens: null, hash: this.hash, total: this.total };
  snap.lens = this.lens.slice();                            // ~50 ints
  for (let i = 0; i < this.groups.length; i++) {
    const len = this.lens[i];
    snap.groups[i] = len > 0 ? this.groups[i].slice(0, len) : null;
  }
  return snap;
};
// Cost: ~50 typed-array copies of avg 15 elements each = ~250 ns
// vs current: ~148,000 ns for object spread of 760 keys (590× faster)
```

#### Group iteration (for matching)

```javascript
// Zig: return slice groups[tagIdx][0..lens[tagIdx]]
FactSet.prototype.group = function(tagIdx) {
  return this.groups[tagIdx].subarray(0, this.lens[tagIdx]); // zero-copy view
};
```

#### Existence / count

```javascript
FactSet.prototype.has = function(tagIdx, hash) {
  const buf = this.groups[tagIdx], len = this.lens[tagIdx];
  const pos = lowerBound(buf, 0, len, hash);
  return pos < len && buf[pos] === hash;
};

FactSet.prototype.count = function(tagIdx, hash) {
  const buf = this.groups[tagIdx], len = this.lens[tagIdx];
  const lo = lowerBound(buf, 0, len, hash);
  if (lo >= len || buf[lo] !== hash) return 0;
  let hi = lo + 1;
  while (hi < len && buf[hi] === hash) hi++;  // count=1 → 1 comparison
  return hi - lo;
};
```

### Hashing

**Additive Zobrist** — multiset-collision-resistant, O(1) incremental update:

```javascript
// Zig: inline fn, wrapping multiply
function mix(h) {
  // Spread bits, avoid clustering. Same as murmurhash3 finalizer.
  h = Math.imul(h ^ (h >>> 16), 0x45d9f3b) | 0;
  h = Math.imul(h ^ (h >>> 13), 0x45d9f3b) | 0;
  return (h ^ (h >>> 16)) | 0;
}
```

Insert: `hash += mix(factHash)`. Remove: `hash -= mix(factHash)`.

Multiset-safe: adding hash H twice → `2 * mix(H)`, not 0 (unlike XOR).

Order-independent: the hash of any permutation of the same multiset is identical.

Collision probability for cycle detection with ~1000 states: ~1000²/2³² ≈ 0.0002. Acceptable.

### Preserved Facts Optimization

Rules that consume and re-produce the same fact (e.g., `code` in EVM) use the "preserved" optimization. With sorted arrays: **skip the remove+insert entirely** — the fact stays in place.

Current: `skipCount`/`skipUsed` objects track which produces to skip. Same logic applies — just don't call `remove`/`insert` for preserved facts. No copyWithin, no arena entry, no hash change.

### What Disappears

| Current component | Replaced by |
|---|---|
| `buildStateIndex(linear, fpConfig, persistent)` | State IS the index. `state.linear.group(tagIdx)` replaces `stateIndex[pred]`. |
| `makeChildCtx(parentCtx, state, log)` | Hash is already updated inside `insert`/`remove`. Just read `state.stateHash`. |
| `undoIndexChanges(stateIndex, indexUndo)` | Undo on FactSet restores groups. No separate index undo. |
| `createExploreContext.fromState(state)` | Just `state.stateHash` for cycle detection. |
| `computeNumericHash(state)` | `state.stateHash` maintained incrementally. Initial computation during `createState`. |
| `hashStateString(state)` | No longer needed (numeric hash sufficient, now multiset-safe). |
| `snapshotState(state)` (object spread) | `state.linear.snapshot()` + `state.persistent.snapshot()` (~250 ns vs ~148 µs). |
| `indexAdd` / `indexRemove` | Gone. `insert`/`remove` on FactSet maintain sorted order. |

### What Stays

| Component | Why |
|---|---|
| `_byKey` fingerprint index | Maps first-argument value → fact hash. Orthogonal to sort order. Small, static. |
| `consumed` / `reserved` objects in matching | Tiny (3-5 entries), short-lived per tryMatch. Not worth optimizing yet. |
| `mutateState` function signature | Same inputs (consumed, theta, patterns, slots). Body changes to use FactSet.insert/remove. |
| `forward.applyMatch` (committed-choice path) | Can use FactSet mutation directly (no undo needed, simpler). |

## Integration Points

### matchOnePattern (match.js)

```javascript
// Current:
const candidates = index[pred] || [];
for (const h of candidates) {
  const available = (state.linear[h] || 0) - (consumed[h] || 0) - (reserved[h] || 0);
  ...
}

// New:
const group = state.linear.group(tagIdx);
for (let i = 0; i < group.length; ) {
  const h = group[i];
  let stateCount = 1;
  while (i + stateCount < group.length && group[i + stateCount] === h) stateCount++;
  const available = stateCount - (consumed[h] || 0) - (reserved[h] || 0);
  ...
  i += stateCount;
}
```

### provePersistentGoals (match.js)

```javascript
// Current: for (const h in state.persistent) { if (getPredicateHead(hn) !== pPred) continue; ... }
// New: iterate persistent group directly — no predicate filtering needed
const group = state.persistent.group(predTagId);
for (let i = 0; i < group.length; i++) {
  if (matchIdx(pattern, group[i], theta, slots)) { ... }
}
```

`_persistentPreds` set → replaced by `state.persistent.lens[tagIdx] > 0` check.

### explore() DFS (symexec.js)

```javascript
// Current (per child):
const undo = mutateState(state, m.consumed, m.theta, ...);
const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
// ... recurse ...
undoIndexChanges(ctx.stateIndex, indexUndo);
undoMutate(state, undo);

// New (per child):
const cp = arena.checkpoint();
mutateState(state, m.consumed, m.theta, ..., arena);  // writes to arena
const childHash = state.stateHash;                     // read directly
// ... recurse ...
state.linear.undo(arena, cp);                          // restores groups + hash
state.persistent.undo(arena, cpPersistent);
```

No makeChildCtx. No undoIndexChanges. No separate indexUndo log.

## Measured Results (solc symbolic multisig, 689 nodes with memo)

| Metric | Before | After | Change |
|---|---|---|---|
| Median | **16.56ms** | **11.58ms** | **−30% (1.43×)** |
| Mean | 18.02ms | 12.18ms | −32% |
| Min | 15.01ms | 10.28ms | −31% |
| Per-node cost | 24µs | 16.8µs | −30% |

Also measured on small multisig (84 nodes): **1.76ms → 1.46ms (−17%)**.

### What was estimated vs actual

| Cost center | Estimated savings | Actual | Notes |
|---|---|---|---|
| Index sync (makeChildCtx + undoIndex) | ~930 µs | **eliminated** | confirmed |
| Mutation + undo | ~186 µs | faster (Arena vs undo log) | confirmed |
| V8 megamorphic IC (5.8% of ticks) | ~800 µs | **eliminated** | Int32Array access is monomorphic |
| for-in overhead (0.9% of ticks) | ~130 µs | **eliminated** | direct array iteration |
| Terminal snapshots | ~1,625 µs | **NOT saved** | `toObject()` still builds plain objects for output |
| **Total overall** | **~1.26× (estimated)** | **1.43× (measured)** | better than estimated |

The estimate was conservative: it didn't account for V8 IC deoptimization cascades and diffuse overhead from dictionary-mode objects, which the FactSet migration also eliminates.

**Terminal snapshot savings were NOT realized** because `toObject(state)` converts FactSet → plain `{hash:count}` objects for the output tree (same cost as old `{...state.linear}`). FactSet.snapshot() is fast (~250ns) but unused for output. Fix: TODO_0058 Opt_A (skip leaf snapshots or store FactSet snapshots directly).

**Scaling**: For larger contracts (~5000 facts), the FactSet advantage grows further — sorted Int32Array insert/remove scales O(log n) vs dictionary-mode object access which scales poorly due to V8 hidden class transitions.

## Migration Stages (all DONE)

All stages completed 2026-03-01. 602 tests pass. Net −149 LOC.

- **Stage 1** — `lib/engine/fact-set.js` (FactSet, Arena, State, fromObject/toObject) + 37 unit tests
- **Stage 2** — `createState()` returns State, `forward.run()` uses State throughout
- **Stage 3** — `mutateState` uses two Arenas (linArena, perArena), no return value
- **Stage 4** — Removed `buildStateIndex`, `makeChildCtx`, `undoIndexChanges`, `indexAdd/Remove` (~190 LOC). Added `State.hasPredicate()` / `State.groupForPred()` for atom/predicate dispatch.
- **Stage 5** — Incremental Zobrist via FactSet.insert/remove. `state.stateHash` for cycle detection. `hashStateString` kept for debug/test backward compat.

## Zig Translation Notes

| JS | Zig |
|---|---|
| `Int32Array` | `[]u32` (slice) |
| `buf.copyWithin(dst, src, end)` | `@memmove(buf[dst..], buf[src..end])` |
| `lowerBound` loop | `std.sort.binarySearch` (returns `SearchResult{found, index}`) |
| `(hash + mix(h)) \| 0` | `hash +% mix(h)` (wrapping add) |
| `Math.imul(a, b)` | `@as(u32, @truncate(@as(u64, a) *% b))` |
| `new Int32Array(n)` | `allocator.alloc(u32, n)` or arena slab |
| `Arena` class | `FixedBufferAllocator` or `[]u32` + cursor |
| `groups: Array(maxTag)` | `[MAX_TAGS]std.ArrayListUnmanaged(u32)` |
| `FactSet.snapshot()` | `@memcpy` per group into snapshot pool |
| Object spread `{...obj}` | N/A — eliminated |
| `for (const k in obj)` | N/A — eliminated |
| `delete obj[k]` | N/A — eliminated |

No hash maps needed for state or index. The entire state representation is flat arrays — ideal for Zig's memory model (no GC, SIMD-friendly, cache-local).
