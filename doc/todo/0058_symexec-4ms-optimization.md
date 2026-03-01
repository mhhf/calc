---
title: "Symexec Sub-4ms: Per-Step Optimization Analysis"
created: 2026-02-28
modified: 2026-03-01
summary: Deep profiling of symbolic multisig explore() identifies 8 concrete optimizations to reduce 14ms → 4ms. TODO_0059 (FactSet) done — 16.6ms → 11.6ms (−30%).
tags:
  - symexec
  - optimization
  - performance
  - forward-chaining
  - profiling
  - evm
type: design
status: in progress
priority: 5
cluster: Performance
depends_on: []
required_by: []
starred: true
---

# TODO 0058: Symexec Sub-4ms — Per-Step Optimization Analysis

## Benchmark Target

MultisigNoCall.sol (solc 0.8.28, 1040 bytes), symbolic sender + nonce, `structuralMemo: true`.

| Metric | Original (pre-0059) | After TODO_0059 | Target |
|---|---|---|---|
| Nodes | 689 (670 deterministic + 9 multi-alt + 10 terminal) | 689 | 689 |
| Leaves | 10 (2 leaf + 8 bound) | 10 | 10 |
| Median time | **16.6ms** | **11.6ms** | **4ms** |
| Per-node cost | 24µs | 16.8µs | 5.8µs |

## Completed: TODO_0059 — FactSet Migration

**Status: DONE** (2026-03-01). Measured improvement: **16.6ms → 11.6ms (−30%, 1.43×)**.

Replaced `{hash:count}` JS objects + parallel `stateIndex` with sorted typed-array `FactSet` groups. State IS the index. Arena-based undo for DFS backtracking.

### What was eliminated

| Old component | Replacement | Savings |
|---|---|---|
| `buildStateIndex` | State IS the index — `state.linear.group(tagIdx)` | ~1ms (index rebuild) |
| `makeChildCtx` + `undoIndexChanges` | FactSet.undo restores groups + hash | ~0.5ms (index sync) |
| `computeNumericHash` / `hashPair` | Incremental Zobrist in FactSet.insert/remove | ~0.1ms |
| `snapshotState` (`{...state.linear}`) | `toObject(state)` — still builds plain objects for output | **NOT saved** — see below |
| V8 megamorphic IC (5.8% of ticks) | Int32Array indexed access | eliminated |
| `for-in` loop overhead (0.9% of ticks) | Direct array iteration | eliminated |

### What was NOT saved

`toObject(state)` at leaf nodes still converts FactSet back to `{hash:count}` plain objects for the output tree. This is comparable to the old `snapshotState` cost. Opt_A (skip leaf snapshots) remains the fix.

## Original Profiling Results (pre-TODO_0059)

### Instrumented breakdown (scaled from 20.8ms instrumented to 13.6ms real)

| Function | Time | % | Calls | Per-call | Post-0059 |
|---|---|---|---|---|---|
| findAllMatches | 5.9ms | 43% | 468 | 12.7µs | ~similar |
| snapshotState | 2.5ms | 18% | 11 | 228µs | → toObject (~similar) |
| mutateState | 2.2ms | 16% | 476 | 4.6µs | faster (FactSet) |
| undoMutate | 0.4ms | 3% | 476 | 0.8µs | → Arena undo (faster) |
| makeChildCtx | 0.3ms | 2% | 476 | 0.6µs | **eliminated** |
| drainPersistentLolis | 0.3ms | 2% | 476 | 0.6µs | ~similar |
| solver (all ops) | 0.3ms | 2% | 520 | 0.5µs | ~similar |
| undoIndexChanges | 0.2ms | 1% | 476 | 0.4µs | **eliminated** |
| computeControlHash | 0.1ms | 1% | 477 | 0.2µs | ~similar |
| DFS overhead | 1.4ms | 10% | — | — | reduced |

### Inside findAllMatches (CALC_PROFILE)

| Operation | Time | Calls | Per-call |
|---|---|---|---|
| unify.matchIndexed | 1.19ms | 8169 | 145ns |
| substitute (goal instantiation) | 0.42ms | 1547 | 268ns |
| backward prove (clauses) | 0.20ms | 15 | 13.4µs |
| **other (dispatch, FFI, alloc)** | **~4ms** | — | — |

**Key finding:** Matching and proving are only **14%** of findAllMatches time. The **86%** overhead is dispatch, FFI machinery, object allocation, and predicate guard checks.

### V8 CPU Profile (top hotspots, pre-TODO_0059)

| Ticks | % | Function | Post-0059 |
|---|---|---|---|
| 138 | 5.8% | `KeyedLoadIC_Megamorphic` — sparse numeric key access | **fixed** (Int32Array) |
| 89 | 3.7% | `matchIndexed` — core unification | still present |
| 56 | 2.4% | `FindOrderedHashMapEntry` — Map/Set lookups | still present |
| 54 | 2.3% | `LoadIC` — standard property loads | reduced |
| 27 | 1.1% | `KeyedLoadIC` — keyed loads | reduced |
| 26 | 1.1% | `provePersistentGoals` | still present |
| 22 | 0.9% | `ForInFilter` — for-in loop overhead | **fixed** (no for-in) |
| 22 | 0.9% | `mutateState` | still present (less) |

### Structural findings

- **670/689 explored nodes are fully deterministic** (1 match, 1 alt). The strategy stack returns exactly 1 candidate rule per node.
- **Average matches per node: ~1.0** — the fingerprint layer is perfectly selective.
- **0 loli facts** in the symbolic multisig state → drainPersistentLolis does nothing.
- **~17 matchIdx calls per node** — from matching ~5 linear patterns per rule across candidates.
- Persistent antecedents: inc (dominant), plus, mem_expand, neq, mem_read.

### Validated experiments (pre-TODO_0059)

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

## Remaining Optimization Plan

Savings re-estimated from the new 11.6ms baseline with 689 nodes (679 rule firings, 670 single-alt, 10 terminals). FactSet changed cost structure: state lookup is O(1) via groupLen, mutation is faster, but toObject at leaves and FFI dispatch overhead are unchanged.

### Phase 1: Low-hanging fruit (11.6ms → ~7.5ms)

#### Opt_A: Skip leaf snapshots (save ~1.5ms)

`toObject(state)` converts FactSet → plain `{hash:count}` object at each terminal (10 calls). Estimated ~150µs/call × 10 = ~1.5ms. Most callers never access `.state` on memo/leaf/bound nodes.

**Implementation:** Add `opts.snapshotLeaves = false` (default). When disabled, terminal nodes store `state: null`. Add a replay API to reconstruct leaf state on demand.

**Risk:** Low — only affects callers that inspect leaf state (inspect tool, classifyLeaf).

#### ~~Opt_B: Skip drainPersistentLolis early exit~~ — **DONE** (part of TODO_0059)

drainPersistentLolis now reads `state.linear.group(TAG_LOLI)` directly — O(1) check, no array copy. Already exits early when no lolis. Remaining cost negligible.

#### Opt_C: Per-predicate persistent dispatch (save ~0.5ms)

`provePersistentGoals` still calls `subApplyIdx` + `tryFFIDirect` for every persistent pattern, even for predicates like `inc`/`plus` that are **never** in `state.persistent`. The FactSet `groupLen` guard is now O(1) (was O(n) set check), so the state-lookup overhead is already reduced. Remaining savings are from skipping the function call chain entirely for FFI-only predicates.

679 firings × ~2 persistent antecedents × ~0.4µs dispatch overhead = ~0.5ms.

**Implementation:** At compile time, classify each persistent antecedent predicate:
- **FFI-only** (`inc`, `plus`, `neq`, `mul`, `mem_expand`): skip state lookup entirely, go directly to FFI.
- **State-first** (user-defined): check state first, then FFI/clauses.

Store a `persistentModes` array on the compiled rule: `[FFI_ONLY, FFI_ONLY, STATE_FIRST, ...]`.

#### Opt_D: Inline FFI for common predicates (save ~1.4ms)

The prove path for `inc(PC, PC')` is: `subApplyIdx(pattern, theta, slots)` → `tryFFIDirect(goal)` → tag dispatch → mode check → isGround check → FFI fn call → build result theta. Total: **478ns/call**.

Direct inline: `theta[pc2Slot] = Store.put('s', [theta[pcSlot]])`. Total: **46ns/call**. **10.4× faster.**

679 firings × ~2 persistent antecedents × ~430ns saved = ~0.58ms from dispatch savings alone. Additional savings from eliminating `subApplyIdx` goal instantiation (268ns × 1358 calls = ~0.36ms) and simpler control flow (~0.5ms). Total: ~1.4ms.

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

#### Opt_E: Skip solver for non-oplus rules (save ~0.3ms)

`solver.checkpoint()` + `solver.restore()` called for every rule match. For single-alt rules (670/679), the solver is never checked. 670 × ~0.4µs = ~0.3ms.

**Implementation:** Conditional: only checkpoint/restore when `alts.length > 1` or when new persistent facts include eq/neq.

**Phase 1 total: −(1.5 + 0.5 + 1.4 + 0.3) ≈ −3.7ms → ~7.9ms** (reduced from ~4.5ms estimated pre-0059 because FactSet already eliminated some of the state lookup overhead that Opt_C counted)

### Phase 2: Medium effort (~7.9ms → ~5.0ms)

#### Opt_F: Reusable tryMatch buffers (save ~0.7ms)

`tryMatch` allocates per call: `new Array(metavarCount)`, `consumed = {}`, `reserved = {}`, `preservedCount = {}`. At 679 calls, that's ~2700 object allocations.

679 calls × ~1µs alloc overhead = ~0.7ms.

**Implementation:** Pre-allocate per-rule buffers. The `consumed` object can be replaced with a flat array indexed by antecedent position (only 2-13 entries).

#### Opt_G: Compiled hot-path matching (save ~2.2ms)

For the 10 most-fired rules (covering ~80% of 670 deterministic steps), generate a specialized match function that:
1. Reads directly from `state.linear.group(tagIdx)` — no dispatch through matchOnePattern
2. Uses delta bypass logic inline — no function call overhead
3. Inlines the FFI computation (Opt_D) — no prove dispatch
4. Returns a pre-allocated theta — no allocation

536 hot-path steps × (16.8µs current − ~5µs compiled) ≈ ~6.3ms theoretical. But Opt_D already saves ~1.4ms of this, and overhead is shared. Realistic: ~2.2ms additional on top of Phase 1.

**Phase 2 total: −(0.7 + 2.2) ≈ −2.9ms → ~5.0ms**

### Phase 3: High effort (~5.0ms → ~3.3ms)

#### Opt_H: Threaded code / fingerprint prediction (save ~1.7ms)

After applying a rule, the new `pc` value is known (computed during substitution). This value determines the next fingerprint, which determines the next candidate rule.

670 predicted steps × ~2.5µs saved (skip getCandidateRules + loli scan + candidate loop) = ~1.7ms.

**Implementation:** At compile time, for each rule:
1. Identify which theta slot produces the new `pc` value (from consequent pattern analysis)
2. Store `rule.nextFingerprintSlot = pcSlotIdx`
3. After mutateState, compute `nextFP = theta[rule.nextFingerprintSlot]`
4. Look up `fpIndex[nextFP]` → if exactly 1 rule, try it directly without calling `findAllMatches`

Combined with Opt_G (compiled matching on the predicted rule): skip the entire findAllMatches + tryMatch dispatch for deterministic steps.

**Phase 3 total: −1.7ms → ~3.3ms**

## Performance Projection

| Level | Optimizations | Estimated time | vs original 16.6ms |
|---|---|---|---|
| Original (pre-0059) | — | 16.6ms | — |
| **After TODO_0059** | **FactSet migration (measured)** | **11.6ms** | **1.43×** |
| Phase 1 | + A+C+D+E (−3.7ms) | ~7.9ms | 2.1× |
| Phase 2 | + F+G (−2.9ms) | ~5.0ms | 3.3× |
| Phase 3 | + H (−1.7ms) | ~3.3ms | 5× |

### Combined with other TODOs (JS)

| Addition | Time | vs original |
|---|---|---|
| + TODO_0054 Layer 2 (loli fusion, −5% nodes) | ~3.1ms | 5.4× |
| + TODO_0005 L0+L1 (constraint propagation) | ~2.9ms | 5.7× |
| + TODO_0052/0056 (zero impact at current scale) | ~2.9ms | 5.7× |

### Zig rewrite projection

V8-specific overhead identified by profiling: megamorphic IC was 5.8% (**fixed** by FactSet), Map/Set 2.4%, property loads 3.4%, GC ~3-5%. FactSet already moves state ops closer to Zig-style (flat sorted arrays, arena undo, no index maintenance). A Zig rewrite eliminates the remaining JS runtime costs:

| Operation | JS (after all opts) | Zig | Speedup |
|---|---|---|---|
| Pattern match (5 linear) | ~1.5µs | ~0.15µs | 10× |
| Inline FFI (inc, plus) | ~0.1µs | ~0.01µs | 10× |
| State mutation (5 facts) | ~1.0µs | ~0.10µs | 10× |
| Hash/memo check | ~0.2µs | ~0.02µs | 10× |
| **Per deterministic step** | **~2.8µs** | **~0.3µs** | **~10×** |

| Level | JS time | Zig time | vs JS original |
|---|---|---|---|
| All TODO_0058 phases | ~3.3ms | ~0.3ms | 55× |
| + all other TODOs | ~2.9ms | ~0.3ms | **55×** |

## Theoretical minimum

The irreducible per-step work (JS, after all optimizations):
1. Pattern matching: 5 linear patterns × ~300ns (delta bypass) = 1.5µs
2. Persistent proving: 2 patterns × ~50ns (inlined FFI) = 0.1µs
3. State mutation: 5 consequent patterns × ~200ns (subCompiled + FactSet insert) = 1.0µs
4. Hash update + cycle check: ~0.2µs (Zobrist incremental — maintained by FactSet)

**JS minimum per step: ~2.8µs. For 679 steps: ~1.9ms.**
**Zig minimum per step: ~0.3µs. For 679 steps: ~0.2ms.** (Memory bandwidth floor: ~0.1ms from ~21K cache line accesses at 5ns/L1-hit.)

Below 2ms (JS) / 0.2ms (Zig) requires basic block compilation (TODO_0057 Level 3b+) which composes multiple steps into composite transformations, eliminating the per-step overhead entirely.

## Key Insights

1. **Recursion is free.** V8's JIT makes recursive DFS calls essentially zero-cost. Iterative chains save no time. This invalidates TODO_0057 Level 1 as a performance optimization (it's still useful for tree compression).

2. **The bottleneck is dispatch, not computation.** Matching (145ns/call) and FFI arithmetic (50-120ns) are fast. The cost is in the orchestration: checking which rule to try, dispatching through provePersistentGoals, allocating theta/consumed objects, iterating candidates.

3. ~~**V8 megamorphic IC is the #1 JavaScript hotspot.**~~ **FIXED by TODO_0059.** Sparse numeric-keyed objects (`state.linear`) were replaced by sorted Int32Array groups. V8 can now use monomorphic IC on typed array access.

4. **Snapshot cost persists.** `toObject(state)` at leaf nodes is still expensive (~1ms for 10 terminals) because it converts FactSet → plain `{hash:count}` objects. FactSet.snapshot() itself is fast (~250ns), but the output tree expects plain objects. Opt_A (skip leaf snapshots) is the fix.

5. **FFI dispatch is 10× more expensive than the computation.** The `provePersistentGoals → subApplyIdx → tryFFIDirect → fn` chain adds 430ns of overhead around a 46ns computation. Inlining eliminates 90% of this cost.

## Connection to Other TODOs

- **TODO_0059 (FactSet Migration): DONE.** 16.6ms → 11.6ms (−30%). Eliminated stateIndex, makeChildCtx, undoIndexChanges. State IS the index. Arena-based undo. V8 megamorphic IC fixed.
- **TODO_0057 (Ephemeral Transit States):** Level 1 (iterative loop) is **invalidated** as a performance optimization by experimental evidence. Level 3b (threaded code) corresponds to Opt_H here.
- **TODO_0054 (Commuting Match Reduction):** Layer 2 (loli fusion) reduces node count by eliminating commuting branches. Orthogonal to per-node optimization.
- **TODO_0005 (Constraint Propagation):** Levels 0+1 reduce state size. At larger scale (k-dss, 5000+ nodes): 3-10× from reduced state + branch pruning.
- **TODO_0052 (Persistent Caching):** Not relevant at current scale (3 memory writes, 6 reads). Triggers at W>50.
- **TODO_0056 (Speculative Merge):** Explicitly ineffective for multisig pattern (no short convergence). Useful for contracts with short if/else divergences.
