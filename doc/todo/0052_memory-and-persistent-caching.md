---
title: Memory Read Caching & Persistent Predicate Indexing
created: 2026-02-26
modified: 2026-02-26
summary: Three caching/indexing optimizations for the forward engine — mem_read cache (L1/L2) and persistent predicate index
tags: [performance, optimization, memory-model, forward-engine, symexec, indexing, content-addressing]
type: implementation
status: ready for implementation
priority: 3
cluster: Performance
depends_on: []
required_by: []
---

# Memory Read Caching & Persistent Predicate Indexing

Three independent optimizations. All zero-impact at current scale (solc symbolic multisig: 477 nodes, W=3, 13.6ms baseline). **0ms savings** in combined optimization pipeline. Implement when profiling shows the specific bottleneck (W>50 or 500+ persistent facts per predicate).

## Context

The write-log memory model (TODO_0049) uses `mem_read` FFI to traverse a linked list of `write(Offset, Value, Rest)` nodes. Cost per read is O(W) where W = chain depth.

**Cost model per write node:** ~195ns (3 `Store.child()` + 2 `Store.tag()` + 1 `binToInt()` + BigInt overlap arithmetic). Plus ~188ns fixed cost per call (2× `Uint8Array(32)` allocation). Exact-hit shortcut (outermost write matches offset) returns the value hash directly without byte assembly.

**Current benchmark (multisig):** W=3, 6 reads, ~5μs total. Negligible vs 11.7ms.

## TODO_0052.Opt_1 — Global `(mem_hash, offset)` Cache

**What:** A `Map<key, valueHash>` where key combines `memHash` and `offsetHash`. Before traversing the write chain, check the cache. On success, store the result.

**Why it works:** Write-logs are content-addressed — same write sequence = same Store hash. The pair `(memHash, offset)` uniquely determines the read result. No invalidation needed (content-addressed terms are immutable). Clear on `Store.clear()`.

**Trigger:** W > 50 writes per MLOAD.

**Where:** `lib/engine/ffi/memory.js`, ~20 lines.

```javascript
const readCache = new Map();

function mem_read(args) {
  const [memHash, offsetHash, valueSlot] = args;
  const key = memHash * 2654435761 + offsetHash;  // Knuth multiplicative hash
  const cached = readCache.get(key);
  if (cached !== undefined)
    return { success: true, theta: [[valueSlot, cached]] };
  // ... existing traversal ...
  readCache.set(key, resultHash);
  return { success: true, theta: [[valueSlot, resultHash]] };
}

// Export clearReadCache for Store.clear() integration
function clearReadCache() { readCache.clear(); }
```

**Estimated savings:**

| Scale | Without | With | Savings |
|-------|---------|------|---------|
| Current (W=3, 6 reads) | 5μs | 5μs | 0 (no hits) |
| Medium (W=50, 100 reads) | 1ms | 0.2ms | ~80% |
| Large (W=500, 200 reads) | 19.5ms | ~1ms | ~95% |

Hit rate depends on read patterns. Solidity's free-memory-pointer (`MLOAD(0x40)`) always hits the same `(mem, 0x40)` pair within a branch. Across branches, different root `mem` hashes = different keys — no cross-branch hits at this level (that's what Opt_2 solves).

## TODO_0052.Opt_2 — Per-Term Read Cache (Structural Sharing)

**What:** Attach read results to individual write-log nodes, not just roots. A `Map<termHash, Map<offset, valueHash>>` keyed on inner Store terms.

**Why it works:** When branch A has `mem = write(96, X, M)` and branch B has `mem = write(96, Y, M)`, both share the sub-term `M`. If branch A computed `read(M, 0) = V`, branch B finds it cached on `M` — skips the entire shared prefix.

Content-addressed terms are immutable, so a read result cached on an inner node is valid forever. Any term containing that node as a sub-term produces the same result for that offset from that node downward.

**Trigger:** 50+ symexec branches sharing memory prefixes. The L1 cache (Opt_1) misses here because root hashes differ across branches.

**Where:** `lib/engine/ffi/memory.js`, ~50 lines. During `mem_read` traversal, before descending into `Rest`, check the cache on `Rest`. On completion, populate the cache for every node visited (walk back up the chain).

```javascript
const termCache = new Map();  // termHash → Map<offset, valueHash>

// Inside mem_read, before descending:
const innerCache = termCache.get(current);
if (innerCache) {
  const hit = innerCache.get(offset);
  if (hit !== undefined) { /* use hit, apply to covered bytes */ }
}

// After completing traversal, populate for visited nodes:
for (const visited of visitedNodes) {
  if (!termCache.has(visited.hash)) termCache.set(visited.hash, new Map());
  termCache.get(visited.hash).set(offset, resultForThisNode);
}
```

**Estimated savings:**

| Scale | Without L2 | With L1+L2 | Savings |
|-------|-----------|-----------|---------|
| Current | 5μs | 5μs | 0 |
| 50 branches, W=500, shared prefix=400 | 78ms | ~1.7ms | ~98% |
| 200 branches, W=1000, shared prefix=800 | 624ms | ~4ms | ~99% |

**Implementation order:** Opt_1 first (trivial). Opt_2 only when profiling confirms branch-prefix duplication is the bottleneck.

## TODO_0052.Opt_3 — Indexed Persistent Predicates

**What:** Build a hash-map index `pred → { firstArg → factHash }` for persistent facts. Replace the O(N) scan in `provePersistentGoals` with O(1) lookup.

**Why:** `provePersistentGoals` (match.js:273-359) resolves `!P` goals via: state lookup → FFI → clause resolution. The state lookup scans all persistent facts with matching predicate name. A predicate-set guard (`persistentPreds.has(pred)`) makes it O(1) when the predicate isn't in state. But when it IS in state, the inner loop is O(N) where N = facts with that predicate.

**Trigger:** 50+ persistent facts per predicate (e.g., 500 storage slots, 200 calldata facts, memoization tables).

**Where:** `lib/engine/match.js`, ~30 lines.

```javascript
// In buildStateIndex — build secondary index:
const persistentIdx = {};
for (const h in state.persistent) {
  const pred = getPredicateHead(Number(h));
  if (!pred) continue;
  if (!persistentIdx[pred]) persistentIdx[pred] = {};
  const firstArg = Store.child(Number(h), 0);
  persistentIdx[pred][firstArg] = Number(h);
}
stateIndex._persistentIdx = persistentIdx;

// In provePersistentGoals — indexed lookup:
const pidx = state.index._persistentIdx;
if (pidx && pidx[pPred]) {
  const goalFirstArg = subApplyIdx(Store.child(pattern, 0), theta, slots);
  const candidate = pidx[pPred][goalFirstArg];
  if (candidate !== undefined) {
    // matchIdx against candidate only — O(1)
  }
}
```

Update incrementally when persistent facts are added (in `mutateState`).

**Note:** `code PC Opcode` is linear (not persistent) and already indexed O(1) via the fingerprint strategy. This targets persistent facts only.

**Estimated savings:**

| Scale | Without | With | Savings |
|-------|---------|------|---------|
| Current (2 persistent facts) | 0μs | 0μs | 0 |
| 500 storage facts, 100 lookups/branch | ~1.25ms | ~5μs | ~99% |
| 10K memoization entries, 500 lookups/branch | ~12.5ms | ~25μs | ~99% |

## Combined Impact at 1000× Scale

For a multi-contract benchmark (200K nodes, 50 branches, 1000 writes, 500 storage slots):

| Component | Without any | With all three | Savings |
|-----------|-----------|---------------|---------|
| mem_read traversal | ~100ms | ~3ms (L1+L2) | 97% |
| Persistent state lookup | ~12.5ms | ~25μs (Opt_3) | 99% |
| **Total memory subsystem** | **~112ms** | **~3ms** | **97%** |

The rest of the engine (unification, mutation/undo, substitution, DFS) scales linearly with node count — addressed by separate TODOs (TODO_0035 delta-driven, TODO_0037 compiled matching, TODO_0044 semi-naive).

## Zig Rewrite Projection

Caching is algorithmic (same hit rates regardless of language). The per-lookup and per-traversal costs shrink ~10× in Zig (flat hash maps, no GC, native u256 arithmetic):

| Component | JS (with caching) | Zig (with caching) |
|---|---|---|
| mem_read cache hit | ~50ns | ~5ns |
| mem_read traverse (W=500, miss) | ~100µs | ~10µs |
| Persistent index lookup | ~50ns | ~5ns |
| **1000× scale total** | **~3ms** | **~0.3ms** |

At current multisig scale (W=3): zero impact in both JS and Zig.
