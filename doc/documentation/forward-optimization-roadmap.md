# Forward Chaining Optimization Roadmap

## Architecture

Forward chaining: rules `A * B * !C -o { D * E }` consume linear facts, produce new ones. Persistent facts (`!C`) proved via backward chaining / FFI. Execution proceeds until quiescence.

Key files: `forward.js` (engine), `symexec.js` (tree exploration), `rule-analysis.js` (compile-time analysis), `disc-tree.js` (discrimination tree indexing), `unify.js` (matching), `substitute.js` (substitution), `store.js` (content-addressed terms).

## Completed Stages

| Stage | What | Result |
|-------|------|--------|
| 1 | Flat TypedArray SoA store | 5.59ms → 3.47ms (−38%) |
| 2 | Preserved/delta detection (compile-time) | Infrastructure for 3, 7 |
| 3 | Preserved optimization (skip consume/produce) | −6-16% |
| 4 | Allocation reduction (reusable buffers, flat worklist) | P90 −9.3% |
| 5 | Theta format unification (3→2 formats) | −138 LOC, 0% perf |
| 6 | De Bruijn indexed theta (O(1) metavar lookup) | −53% |
| 7 | Delta bypass + compiled substitution | −8% |
| 9 | Discrimination tree (general rule indexing) | O(depth) vs O(R) |
| 10 | Flat undo log + matchAlts elimination | −13% |
| 11 | Numeric tag IDs + slots-based metavar check | ~2% (Zig-ready) |
| — | Generalized fingerprint layer (auto-detect) | Non-EVM programs |

**Current stack:** `fingerprintLayer` (O(1) for ground-discriminated rules) → `discTreeLayer` (O(depth) catch-all) → `predicateLayer` (safety net, never activates).

**Current bottleneck:** evenly distributed — no single dominant cost. 74 tryMatch calls for 63 nodes (strategy stack very effective). matchIndexed + substitute = 10%, state.linear access = ~20%, mutations/undo = ~15%, FFI = ~6%, DFS/alloc = ~10%, other overhead = ~40%.

## Key Learnings

1. **CALC's engine IS TREAT-like.** No beta memories, full re-evaluation from alpha memories (stateIndex). Correct for linear logic — Rete's cached partial matches are pure overhead when facts are consumed. See `doc/research/forward-chaining-networks.md`.

2. **CHR simpagation IS ILL forward rules.** Kept head = `!A`, removed head = linear, guard = FFI/backward proving. 25+ years of CHR compilation research applies. See `doc/research/forward-chaining-networks.md`.

3. **Strategy stack IS a manually compiled decision tree.** The fingerprint layer does what Maranget's algorithm would automate. The disc-tree layer generalizes to arbitrary patterns. Together they handle the full range from 44 to 400+ rules without manual tuning.

4. **Semi-naive for linear logic is fundamentally harder than Datalog.** Fact consumption invalidates matches — needs provenance tracking ≈ Rete beta network. Dirty predicate tracking (Stage 5a) would be the cheap approximation, but the disc-tree already prunes candidates by pattern structure, making 5a redundant for symexec. See `doc/research/incremental-matching.md`.

5. **V8 handles numeric-key objects efficiently.** Plain objects with ~178 numeric keys use V8's sparse array storage, NOT dictionary mode. Microbenchmark: object reads 1.85x faster, writes 5.3x faster, clone 8.6x faster than Map. Map only wins on iteration (5.25x). Don't convert to Map for the state representation.

6. **Disc-tree must filter by relevant predicates.** Naive implementation scans all state facts — 47% regression at 44 rules (178 facts, only 4 unclaimed rules). Fix: at build time collect which predicates appear in indexed rules, only scan those facts. Result: 0% regression. Lesson: catch-all layers must not do O(total_facts) work when they only have a few rules.

7. **Store.arity includes non-term children.** `atom('e')` has `arity=1` (string child) but 0 term children. Flatten functions must use `Store.isTermChild()` to filter, otherwise trie paths are wrong. This applies to any code that recursively walks Store terms.

8. **V8 string interning makes string-based tag comparison nearly as fast as numeric.** `Store.tag()` returns `TAG_NAMES[tags[id]]` — the same interned string object every time. String comparison `===` between interned strings is a pointer comparison. Adding `Store.tagId()` (raw numeric ID) and replacing `isVar()` with `slots[p] !== undefined` gives only ~2% improvement in V8. However, these changes eliminate string allocation in the hot path, which is essential for the Zig port.

9. **At 44 rules, the strategy stack reduces tryMatch calls to 74 for a 63-node tree (1.2×/node).** Only 18 failures out of 74 calls (76% success rate). The remaining failures are inherent: both JUMPI branches must be tried, and calldatasize has overlapping trigger predicates. No further candidate filtering improvement is possible at this scale.

## What's Next

All optimizations that matter at current scale (44 rules, ~20 facts, depth-2 terms) are done. The remaining items are tracked as TODOs, triggered by specific scaling scenarios:

| Optimization | Trigger | TODO |
|-------------|---------|------|
| Persistent proving order (FFI before state) | Mixed FFI + state predicates | See note below |
| Delta-driven activation | 100+ rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Compiled matching (Maranget) | 1000+ rules | [TODO_0037](../todo/0037_compiled-pattern-matching.md) |
| Semi-naive for linear logic | 100K+ facts | [TODO_0044](../todo/0044_semi-naive-linear-logic.md) |
| Join ordering | 4+ antecedent rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Path-based nested access | depth 4+ terms | [TODO_0022](../todo/0022_forward-optimization-research.md) |
| Memoized mem_read cache | W > 50 writes per MLOAD | See [Memory Read Optimizations](#memory-read-optimizations) |
| Per-term read cache in Store | Shared prefixes across branches | See [Memory Read Optimizations](#memory-read-optimizations) |
| Indexed persistent predicates | O(N) persistent fact scan | See [Indexed Persistent Predicates](#indexed-persistent-predicates) |

### Persistent proving order

Current order: state lookup → FFI → clause resolution. Reversing to FFI → state → clauses yields ~2.5% improvement on the EVM benchmark (n=100, p=0.012) because all 153 persistent goals per tree are FFI-resolvable (inc, plus, neq) — the state lookup always misses.

However, FFI-first is only optimal when all persistent predicates are FFI-backed. Programs with user-defined persistent facts (e.g. lookup tables, memoization) would benefit from state-first order, since state lookup is O(1) via the predicate set guard vs backward proving overhead. The right long-term answer may be per-predicate dispatch: at compile time classify each persistent predicate as FFI-only, state-only, or mixed, and generate the appropriate proving order. For now, keeping state-first as the default is the more general choice.

### Memory Read Optimizations

The write-log memory model (TODO_0049) uses `mem_read` FFI to traverse a linked list of `write(Offset, Value, Rest)` nodes. Cost is O(W) per read where W = writes in the chain. At current scale (W=3, 6 reads) this is negligible (~5μs total). At scale it dominates.

**Cost model:** Each write node costs ~195ns to traverse (3 `Store.child()` + 2 `Store.tag()` + 1 `binToInt()` + BigInt overlap arithmetic). The Uint8Array allocation (2×32 bytes) costs ~188ns per call regardless of chain depth. Exact-hit shortcut (outermost write matches) returns directly without byte assembly.

#### Level 1: Global `(mem_hash, offset)` Cache

Write-logs are content-addressed: same write sequence = same Store hash. A global `Map<(memHash, offset), valueHash>` gives O(1) amortized reads. No cache invalidation needed (content-addressed terms are immutable). Clear on `Store.clear()`.

**When:** W > 50 writes per MLOAD. Before that, the FFI traversal itself is fast enough.

**How:** ~20 lines in `memory.js`. Before the while-loop in `mem_read`, check `cache.get(memHash * PRIME + offsetHash)`. On FFI success, store the result. The cache key combines both hashes into a single number (both are small content-addressed integers).

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
```

**Estimated savings:**

| Scale | Without | With | Savings |
|-------|---------|------|---------|
| Current (W=3, 6 reads) | 5μs | 5μs | 0 (no cache hits) |
| Medium (W=50, 100 reads) | 1ms | 0.2ms | ~80% |
| Large (W=500, 200 reads) | 19.5ms | ~1ms | ~95% |

Cache hit rate depends on read patterns. Solidity's free-memory-pointer read (`MLOAD(0x40)`) is the most common MLOAD and always hits the same `(mem, 0x40)` pair within a branch. Across branches, different `mem` hashes mean different keys — no cross-branch hits at this level.

#### Level 2: Per-Term Read Cache (Structural Sharing)

Attach read results to individual write-log nodes, not just roots. When branch A has `mem = write(96, X, M)` and branch B has `mem = write(96, Y, M)`, both share the sub-term `M`. If branch A already computed `read(M, 0) = V`, branch B finds it cached on `M` without traversing.

**When:** Branchy symexec trees (50+ branches) with shared memory prefixes. The Level 1 cache misses here because root hashes differ across branches even when they share deep prefixes.

**How:** ~50 lines. A `WeakMap<termHash, Map<offset, valueHash>>` (or a flat array on Store terms). During `mem_read` traversal, before descending into `Rest`, check the cache on `Rest`. On completion, populate the cache for every node visited during traversal (walk back up the chain).

The key insight: content-addressed terms are immutable, so a read result cached on an inner node is valid forever — any term that contains that node as a sub-term will produce the same read result for that offset from that node downward.

**Estimated savings:**

| Scale | Without L2 | With L1+L2 | Savings |
|-------|-----------|-----------|---------|
| Current | 5μs | 5μs | 0 |
| 50 branches, W=500, shared prefix=400 | 78ms | ~1.7ms | ~98% |
| 200 branches, W=1000, shared prefix=800 | 624ms | ~4ms | ~99% |

**Implementation order:** Level 1 first (trivial, catches the common case). Level 2 only when profiling shows branch-prefix duplication is the bottleneck.

### Indexed Persistent Predicates

`provePersistentGoals` (match.js:273-359) resolves `!P` goals in three steps: state lookup → FFI → clause resolution. The state lookup scans all persistent facts with matching predicate name. A predicate-set guard (`persistentPreds.has(pred)`) makes this O(1) when the predicate isn't in state at all. But when it IS in state, the scan is O(N) where N = facts with that predicate.

**Current benchmark:** Only 2 persistent facts in state (`eq`, `gt`). All `inc`/`plus`/`neq`/`mem_read` goals skip the scan via the predicate-set guard. Zero impact.

**When:** Contracts with many persistent facts of the same predicate — e.g., 500 `sload` facts (storage slots), 200 `calldata` facts, or memoization tables. The scan becomes the bottleneck when N > 50 facts per predicate and goals are frequent.

**How:** ~30 lines in `match.js`. At `buildStateIndex` time, build a secondary index: `_persistentByPred[pred][firstArg] = factHash`. In `provePersistentGoals`, replace the linear scan (lines 298-308) with an indexed lookup when the first argument of the goal is ground.

```javascript
// In buildStateIndex:
const persistentIdx = {};
for (const h in state.persistent) {
  const pred = getPredicateHead(Number(h));
  if (!pred) continue;
  if (!persistentIdx[pred]) persistentIdx[pred] = {};
  const firstArg = Store.child(Number(h), 0);
  persistentIdx[pred][firstArg] = Number(h);
}
stateIndex._persistentIdx = persistentIdx;

// In provePersistentGoals (state lookup):
const pidx = state.index._persistentIdx;
if (pidx && pidx[pPred]) {
  const goalFirstArg = subApplyIdx(Store.child(pattern, 0), theta, slots);
  const candidate = pidx[pPred][goalFirstArg];
  if (candidate !== undefined) {
    // try matchIdx against candidate only — O(1)
  }
}
```

Update the index incrementally when persistent facts are added (in `mutateState` / forward rule application).

**Estimated savings:**

| Scale | Without | With | Savings |
|-------|---------|------|---------|
| Current (2 persistent facts) | 0μs | 0μs | 0 |
| 500 storage facts, 100 lookups/branch | ~1.25ms | ~5μs | ~99% |
| 10K memoization entries, 500 lookups/branch | ~12.5ms | ~25μs | ~99% |

**Note:** `code PC Opcode` is linear (not persistent) and already indexed via the fingerprint strategy at O(1). This optimization targets persistent facts only.

## Profiling History

| Milestone | Median | Notes |
|-----------|--------|-------|
| Original | 181ms | Before strategy stack |
| Strategy stack | 14ms | 12.7x |
| + incremental context | 8.4ms | 1.7x |
| + mutation+undo | 4.7ms | 1.8x |
| + index+set undo | 3.8ms | 1.25x |
| + direct FFI bypass | 5.9ms | 1.2x (different baseline) |
| Stage 6 (de Bruijn theta) | 1.19ms | −53% |
| Stage 7 (compiled sub) | 1.09ms | −8% |
| Stage 9 (disc-tree) | ~1.9ms | 0% at 44 rules |
| Stage 10 (flat undo + matchAlts) | 1.05ms | −13% |
| Stage 11 (numeric tagId + slots) | ~1.0ms | ~2%, Zig-ready |

## Zig Port Mapping

| JS concept | Zig equivalent |
|-----------|---------------|
| `Store.put/get/tag/child/arity/tagId` | SoA `MultiArrayList` + dedup `HashMap` |
| `theta = new Array(N)` | `[MAX_METAVARS]?u32` (stack) |
| `_Gp/_Gt` worklist | `[MAX_WORKLIST]u32` (stack) |
| `metavarSlots` | `comptime` lookup table |
| `compiledConseq` | `comptime` array of `ChildSource` unions |
| `stateIndex` | `AutoHashMap(u32, ArrayList(u32))` |
| Discrimination tree | Flat array with offset-based children; `comptime` if rules static |
| `pathVisited` | `AutoHashMap(u64, void)` or bloom filter |

## References

- Abadi, Cardelli, Curien & Levy (1991) — *Explicit substitutions*
- Baader & Nipkow (1998) — *Term Rewriting and All That*
- Christian (1993) — *Flatterms, discrimination nets, and fast term rewriting*
- Conchon & Filliatre (2006) — *Type-safe modular hash-consing*
- de Bruijn (1972) — *Lambda calculus notation with nameless dummies*
- Forgy (1982) — *Rete: A fast algorithm for the many pattern/many object match problem*
- Fruhwirth (2009) — *Constraint Handling Rules*
- Graf (1995) — *Substitution tree indexing*
- Maranget (2008) — *Compiling pattern matching to good decision trees*
- McCune (1992) — *Experiments with discrimination-tree indexing and path indexing*
- Miranker (1987) — *TREAT: A better match algorithm for AI production systems*
- Rawson — [discrimination-tree (Rust crate)](https://github.com/MichaelRawson/discrimination-tree)
- Voronkov (2001) — *Term indexing* (Handbook of Automated Reasoning)
