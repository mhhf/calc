---
title: "Symexec Sub-4ms: Per-Step Optimization Analysis"
created: 2026-02-28
modified: 2026-02-28
summary: Deep profiling of symbolic multisig explore() identifies 8 concrete optimizations to reduce 14ms → 4ms
tags:
  - symexec
  - optimization
  - performance
  - forward-chaining
  - profiling
  - evm
type: design
status: researching
priority: 5
cluster: Performance
depends_on: []
required_by: []
starred: true
---

# TODO 0058: Symexec Sub-4ms — Per-Step Optimization Analysis

## Benchmark Target

MultisigNoCall.sol (solc 0.8.28, 1040 bytes), symbolic sender + nonce, `structuralMemo: true`.

| Metric | Current | Target |
|---|---|---|
| Nodes | 477 (444 deterministic + 22 multi-alt + 11 terminal) | 477 |
| Leaves | 11 (2 real + 9 memo) | 11 |
| Median time | **13.6ms** | **4ms** |
| Per-node cost | 29µs | 8.5µs |

## Profiling Results

### Instrumented breakdown (scaled from 20.8ms instrumented to 13.6ms real)

| Function | Time | % | Calls | Per-call |
|---|---|---|---|---|
| findAllMatches | 5.9ms | 43% | 468 | 12.7µs |
| snapshotState | 2.5ms | 18% | 11 | 228µs |
| mutateState | 2.2ms | 16% | 476 | 4.6µs |
| undoMutate | 0.4ms | 3% | 476 | 0.8µs |
| makeChildCtx | 0.3ms | 2% | 476 | 0.6µs |
| drainPersistentLolis | 0.3ms | 2% | 476 | 0.6µs |
| solver (all ops) | 0.3ms | 2% | 520 | 0.5µs |
| undoIndexChanges | 0.2ms | 1% | 476 | 0.4µs |
| computeControlHash | 0.1ms | 1% | 477 | 0.2µs |
| DFS overhead | 1.4ms | 10% | — | — |

### Inside findAllMatches (CALC_PROFILE)

| Operation | Time | Calls | Per-call |
|---|---|---|---|
| unify.matchIndexed | 1.19ms | 8169 | 145ns |
| substitute (goal instantiation) | 0.42ms | 1547 | 268ns |
| backward prove (clauses) | 0.20ms | 15 | 13.4µs |
| **other (dispatch, FFI, alloc)** | **~4ms** | — | — |

**Key finding:** Matching and proving are only **14%** of findAllMatches time. The **86%** overhead is dispatch, FFI machinery, object allocation, and predicate guard checks.

### V8 CPU Profile (top hotspots)

| Ticks | % | Function |
|---|---|---|
| 138 | 5.8% | `KeyedLoadIC_Megamorphic` — sparse numeric key access on state.linear |
| 89 | 3.7% | `matchIndexed` — core unification |
| 56 | 2.4% | `FindOrderedHashMapEntry` — Map/Set lookups (solver, visited sets) |
| 54 | 2.3% | `LoadIC` — standard property loads |
| 27 | 1.1% | `KeyedLoadIC` — keyed loads |
| 26 | 1.1% | `provePersistentGoals` |
| 22 | 0.9% | `ForInFilter` — for-in loop overhead |
| 22 | 0.9% | `mutateState` |

**Insight:** V8 megamorphic inline cache is the #1 single hotspot. This is caused by sparse numeric-keyed objects (`state.linear[hash]`). V8 falls back to hash-table-mode property access.

### Structural findings

- **444/468 explored nodes are fully deterministic** (1 match, 1 alt). The strategy stack returns exactly 1 candidate rule per node.
- **Average matches per node: 1.00** — the fingerprint layer is perfectly selective.
- **0 loli facts** in the symbolic multisig state → drainPersistentLolis does nothing.
- **17.1 matchIdx calls per node** — from matching 5.3 linear patterns per rule across candidates.
- **69/73 rules** claimed by fingerprint layer; 4 by disc-tree layer.
- Persistent antecedents: inc (82 uses), plus (37), mem_expand (5), neq (2), mem_read (2).

### Validated experiments

| Experiment | Median | vs Baseline | Correctness |
|---|---|---|---|
| Baseline (explore, structuralMemo=true) | 13.57ms | — | 477 nodes, 11 leaves |
| Skip leaf snapshots | 11.40ms | −16% | 477 nodes, 11 leaves |
| Iterative deterministic chain + no snapshot | 11.41ms | −16% | 33 nodes, 11 leaves |

**Critical finding:** Converting 444 recursive DFS calls to an iterative loop produces **zero additional improvement**. V8's function call overhead and children array allocation are negligible. The cost is entirely in per-step work (findAllMatches + mutateState).

### FFI dispatch cost (micro-benchmarks)

| Operation | Via dispatch | Direct (inlined) | Speedup |
|---|---|---|---|
| inc(5, X) | 489ns | 54ns | 9× |
| plus(5, 6, X) | 399ns | 120ns | 3.3× |
| Full prove path (subApplyIdx + tryFFIDirect) | 478ns | 46ns | **10.4×** |

## Optimization Plan

### Phase 1: Low-hanging fruit (13.6ms → ~9ms)

#### Opt_A: Skip leaf snapshots (save ~2.2ms)

`snapshotState()` copies ~780 linear + persistent entries at each terminal node (11 calls). Most callers never access `.state` on memo/leaf nodes.

**Implementation:** Add `opts.snapshotLeaves = false` (default). When disabled, terminal nodes store `state: null`. Add a replay API to reconstruct leaf state on demand.

**Risk:** Low — only affects callers that inspect leaf state (inspect tool, classifyLeaf). Those paths already tolerate the overhead.

#### Opt_B: Skip drainPersistentLolis early exit (save ~0.3ms)

476 calls × 0.6µs/call. The symbolic multisig has 0 loli facts — every call is pure overhead (checking `_loli.length`, sometimes copying empty arrays with `[...arr]`).

**Implementation:** One-line early exit: `if (!loliList || loliList.length === 0) return { ctx: parentCtx, undoLogs: [], indexUndoLogs: [] };`

Already partially done but the array copy `[...currentCtx.stateIndex._loli]` still happens inside the loop.

#### Opt_C: Per-predicate persistent dispatch (save ~0.7ms)

`provePersistentGoals` does a state lookup scan for every persistent pattern, even for predicates like `inc`/`plus` that are **never** in `state.persistent` (they're FFI-only). The `persistentPreds` guard helps but still has overhead per call.

**Implementation:** At compile time, classify each persistent antecedent predicate:
- **FFI-only** (`inc`, `plus`, `neq`, `mul`, `mem_expand`): skip state lookup entirely, go directly to FFI.
- **State-first** (user-defined): check state first, then FFI/clauses.
- **Mixed**: current behavior.

Store a `persistentModes` array on the compiled rule: `[FFI_ONLY, FFI_ONLY, STATE_FIRST, ...]`.

#### Opt_D: Inline FFI for common predicates (save ~1.0ms)

The prove path for `inc(PC, PC')` is: `subApplyIdx(pattern, theta, slots)` → `tryFFIDirect(goal)` → tag dispatch → mode check → isGround check → FFI fn call → build result theta. Total: **478ns/call**.

Direct inline: `theta[pc2Slot] = Store.put('s', [theta[pcSlot]])`. Total: **46ns/call**. **10.4× faster.**

**Implementation:** At compile time, for each persistent antecedent, generate an "inline prover" closure:

```javascript
rule.inlineProvers = [
  // inc(PC, PC') → PC' = s(PC)
  (theta) => { theta[3] = Store.put('s', [theta[0]]); return true; },
  // plus(PC, 2, PC') → PC' = binlit(toInt(PC) + 2)
  (theta) => { ... },
];
```

Falls back to generic provePersistentGoals when inline prover is not available.

#### Opt_E: Skip solver for non-oplus rules (save ~0.2ms)

`solver.checkpoint()` + `solver.restore()` are called for every rule match (520 calls). For single-alt rules (444/468), the solver is never checked. We could skip the checkpoint/restore for these.

**Implementation:** Conditional: only checkpoint/restore when `alts.length > 1` or when new persistent facts include eq/neq.

### Phase 2: Medium effort (~9ms → ~6ms)

#### Opt_F: Reusable tryMatch buffers (save ~0.5ms)

`tryMatch` allocates per call: `new Array(metavarCount)`, `consumed = {}`, `reserved = {}`, `preservedCount = {}`. At 468 calls, that's ~1870 object allocations. V8 is fast at allocation but not free.

**Implementation:** Pre-allocate per-rule buffers. The `consumed` object can be replaced with a flat array indexed by antecedent position (only 2-13 entries).

#### Opt_G: Compiled hot-path matching (save ~1.5ms)

For the 10 most-fired rules (covering ~80% of deterministic steps), generate a specialized match function that:
1. Reads directly from `stateIndex[predicate]` — no dispatch through matchOnePattern
2. Uses delta bypass logic inline — no function call overhead
3. Inlines the FFI computation (Opt_D) — no prove dispatch
4. Returns a pre-allocated theta — no allocation

Each compiled match function is ~20 lines of specialized JavaScript.

**Estimated per-call cost reduction:** 12.7µs → ~5µs for hot rules.

### Phase 3: High effort (~6ms → 4ms)

#### Opt_H: Threaded code / fingerprint prediction (save ~2ms)

After applying a rule, the new `pc` value is known (computed during substitution). This value determines the next fingerprint, which determines the next candidate rule.

**Implementation:** At compile time, for each rule:
1. Identify which theta slot produces the new `pc` value (from consequent pattern analysis)
2. Store `rule.nextFingerprintSlot = pcSlotIdx`
3. After mutateState, compute `nextFP = theta[rule.nextFingerprintSlot]`
4. Look up `fpIndex[nextFP]` → if exactly 1 rule, try it directly without calling `findAllMatches`

**Estimated savings:** Skip `getCandidateRules` (1µs) + loli scan (0.5µs) + candidate loop overhead (1µs) = 2.5µs per predicted step. For 444 predicted steps: 1.1ms.

Combined with Opt_G (compiled matching on the predicted rule): skip the entire findAllMatches + tryMatch dispatch for deterministic steps.

## Performance Projection

| Level | Optimizations | Estimated time | Improvement |
|---|---|---|---|
| Current | — | 13.6ms | — |
| Phase 1 | A+B+C+D+E | ~8.9ms | 1.5× |
| Phase 2 | + F+G | ~6.4ms | 2.1× |
| Phase 3 | + H | ~4.5ms | 3× |
| Phase 3 + tuning | All + V8 tuning | ~4ms | 3.4× |

### Combined with other TODOs (JS)

| Addition | Time | vs baseline |
|---|---|---|
| + TODO_0054 Layer 2 (loli fusion) | ~3.5ms | 3.9× |
| + TODO_0005 L0+L1 (constraint propagation) | ~3.3ms | 4.1× |
| + TODO_0052/0056 (zero impact at current scale) | ~3.3ms | 4.1× |

### Zig rewrite projection

V8-specific overhead identified by profiling (megamorphic IC 5.8%, Map/Set 2.4%, property loads 3.4%, GC ~3-5%) totals ~20% of named hotspots but diffuse overhead is much larger. A Zig rewrite eliminates all JS runtime costs:

| Operation | JS (after all opts) | Zig | Speedup |
|---|---|---|---|
| Pattern match (5 linear) | ~1.5µs | ~0.15µs | 10× |
| Inline FFI (inc, plus) | ~0.1µs | ~0.01µs | 10× |
| State mutation (5 facts) | ~1.5µs | ~0.15µs | 10× |
| Index maintenance | ~0.5µs | ~0.05µs | 10× |
| Hash/memo check | ~0.3µs | ~0.03µs | 10× |
| **Per deterministic step** | **~4µs** | **~0.4µs** | **10×** |

Key Zig advantages: Store as flat struct array (one pointer offset vs dictionary lookup), state as bitset (100 bytes `@memcpy` vs 780-entry spread copy at 228µs), enum-indexed stateIndex (vs string-keyed property access), arena allocators (zero GC), native u256 (no BigInt boxing).

| Level | JS time | Zig time | vs JS baseline |
|---|---|---|---|
| All TODO_0058 phases | ~4ms | ~0.4ms | 34× |
| + all other TODOs | ~3.3ms | ~0.3ms | **45×** |

## Theoretical minimum

The irreducible per-step work (JS):
1. Pattern matching: 5 linear patterns × ~300ns (delta bypass) = 1.5µs
2. Persistent proving: 2 patterns × ~50ns (inlined FFI) = 0.1µs
3. State mutation: 5 consequent patterns × ~300ns (subCompiled + state update) = 1.5µs
4. Index maintenance: 5 adds + 5 removes × ~50ns = 0.5µs
5. Hash update + cycle check: ~0.3µs

**JS minimum per step: ~4µs. For 468 steps: ~1.9ms.**
**Zig minimum per step: ~0.4µs. For 468 steps: ~0.19ms.** (Memory bandwidth floor: ~0.1ms from ~21K cache line accesses at 5ns/L1-hit.)

Below 2ms (JS) / 0.2ms (Zig) requires basic block compilation (TODO_0057 Level 3b+) which composes multiple steps into composite transformations, eliminating the per-step overhead entirely.

## Key Insights

1. **Recursion is free.** V8's JIT makes recursive DFS calls essentially zero-cost. Iterative chains save no time. This invalidates TODO_0057 Level 1 as a performance optimization (it's still useful for tree compression).

2. **The bottleneck is dispatch, not computation.** Matching (145ns/call) and FFI arithmetic (50-120ns) are fast. The cost is in the orchestration: checking which rule to try, dispatching through provePersistentGoals, allocating theta/consumed objects, iterating candidates.

3. **V8 megamorphic IC is the #1 JavaScript hotspot.** Sparse numeric-keyed objects (`state.linear`) trigger V8's slowest property access path. This is inherent to the data structure choice and can't be fixed without changing the representation.

4. **Snapshot cost is disproportionate.** 11 snapshot calls take 18% of total time because `{...state.linear}` copies 780+ entries from a dictionary-mode V8 object. Eliminating this is the single easiest win.

5. **FFI dispatch is 10× more expensive than the computation.** The `provePersistentGoals → subApplyIdx → tryFFIDirect → fn` chain adds 430ns of overhead around a 46ns computation. Inlining eliminates 90% of this cost.

## Connection to Other TODOs

- **TODO_0057 (Ephemeral Transit States):** Level 1 (iterative loop) is now **invalidated** as a performance optimization by experimental evidence. Level 3b (threaded code) corresponds to Opt_H here.
- **TODO_0054 (Commuting Match Reduction):** Layer 2 (loli fusion) reduces node count 477→~430 by eliminating commuting branches. Saves ~0.5ms on top of Phase 3 optimized per-node cost (430 × ~1µs fewer). Orthogonal to per-node optimization.
- **TODO_0005 (Constraint Propagation):** Levels 0+1 reduce state size (~50 constraints → ~5-10). Saves ~0.2ms from faster matching at multi-alt points. At larger scale (k-dss, 5000+ nodes): 3-10× from reduced state + branch pruning.
- **TODO_0052 (Persistent Caching):** Not relevant at current scale (3 memory writes, 6 reads). Triggers at W>50. At large scale (W=500): saves ~97% of mem_read cost.
- **TODO_0056 (Speculative Merge):** Explicitly ineffective for multisig pattern (no short convergence). Useful for contracts with short if/else divergences.
