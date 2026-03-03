---
title: "Symexec Per-Step Optimization Analysis"
created: 2026-02-28
modified: 2026-03-03
summary: "Deep profiling of symbolic multisig explore(). All JS-level optimizations complete: TODO_0059 (FactSet), Opt_A (snapshots), Opt_G (persistent steps), FFI-first proving, Opt_H (fingerprint prediction). 16.6ms → 5.3ms (3.1×). Inline predicted step analyzed and rejected (marginal gain, damages architecture). JS-level optimization is exhausted; remaining gains require Zig port."
tags:
  - symexec
  - optimization
  - performance
  - forward-chaining
  - profiling
  - evm
type: design
status: done
priority: 5
cluster: Performance
depends_on: []
required_by: []
---

# TODO 0058: Symexec Per-Step Optimization Analysis

## Benchmark

MultisigNoCall.sol (solc 0.8.28, 1040 bytes), symbolic sender + nonce, `structuralMemo: true`.

| Metric | Original | After 0059 | After Opt_A | After Opt_G + FFI-first | + arrlit (0063) + Opt_H |
|---|---|---|---|---|---|
| Nodes | 689 | 689 | 689 | 689 | 477 |
| Median time | **16.6ms** | **11.6ms** | **~9.2ms** | **~8.1ms** | **~5.3ms** |
| Per-node cost | 24µs | 16.8µs | ~13.3µs | ~11.8µs | ~11.1µs |
| vs original | — | 1.43× | 1.8× | 2.0× | 3.1× |

## Completed Optimizations

### TODO_0059 — FactSet Migration (DONE, 2026-03-01)

**Measured: 16.6ms → 11.6ms (−30%, 1.43×).**

Replaced `{hash:count}` JS objects + parallel `stateIndex` with sorted typed-array `FactSet` groups. State IS the index. Arena-based undo for DFS backtracking.

| Old component | Replacement | Savings |
|---|---|---|
| `buildStateIndex` | `state.linear.group(tagIdx)` | ~1ms |
| `makeChildCtx` + `undoIndexChanges` | FactSet.undo via Arena | ~0.5ms |
| V8 megamorphic IC (5.8% of ticks) | Int32Array access | eliminated |
| `for-in` loop overhead (0.9% of ticks) | Direct array iteration | eliminated |

### Opt_A — FactSet Snapshots at Terminal Nodes (DONE, 2026-03-01)

**Measured: −20.9% geometric mean** (multisig 1.81ms, solc_symbolic 8.94ms).

Replaced `toObject(state)` with `state.snapshot()` at all 5 terminal return sites in `symexec.explore()`. Only 31 terminal nodes (of 2125 total) get snapshots — the 2094 branch nodes store `state: null`.

### ~~Opt_B: Skip drainPersistentLolis early exit~~ — DONE (part of TODO_0059)

### Opt_G — Persistent Step Fast Path (DONE, 2026-03-02)

**Measured: -32% matchIdx calls, -61% substitute calls, ~6-12% wall-clock.**

| Metric | Before | After | Change |
|---|---|---|---|
| matchIdx calls | 10,376 | 7,021 | **-32%** (-3,355) |
| substitute calls | 2,262 | 893 | **-61%** (-1,369) |
| Profiled time | 6.08ms | 5.13ms | **-15.6%** |

Files: `compile.js` (~50 LOC), `match.js` (10 LOC), `index.js` (1 LOC), `compiled-matcher.test.js` (16 tests).

Pre-compiled FFI closures (`rule.persistentSteps`) attached at `compileRule()` time. Called from the monomorphic `matchAllLinear` path, bypassing `subApplyIdx` + `tryFFIDirect` for ground FFI goals (inc, plus, neq, mul). Only ~4 distinct closure types → within V8's polymorphic IC threshold (≤4 shapes).

#### What failed along the way

**Per-rule compiled matchers** — 59 per-rule closures dispatched from one call site in `tryMatch` caused **~25% regression** (V8 megamorphic dispatch, >4 shapes at one IC site). See [RES_0069](../research/0069_v8-megamorphic-dispatch.md).

**Flat bypass for consumed patterns** — Extended delta bypass to all flat patterns. Reduced matchIdx calls by 27% but **regressed wall time**. For simple 2-child patterns, JS-level bypass is not faster than the tight recursive `matchIdx`.

**Key lesson:** dispatch overhead IS the bottleneck (86%), but eliminating it requires staying within V8's IC monomorphism constraints. Only the persistent proving path (≤4 FFI types) could be compiled.

### FFI-First Persistent Proving (DONE, 2026-03-02)

Swapped proving order in `provePersistentGoals` from state lookup → FFI → clauses to **FFI → state lookup → clauses**. For EVM, persistent goals (inc, plus, neq, mul) are all FFI-backed and state lookup always misses — trying the state first added ~50ns per goal for a guaranteed miss. Also fixed `solc_symbolic` benchmark maxDepth 200→400 (actual tree depth is 387; old limit prevented structural memoization from activating).

### ~~Opt_E: Skip solver for non-oplus rules~~ — REVERTED

Attempted (commit `647583c`) and reverted (commit `266b7b5`). The conditional EqNeqSolver skip for non-oplus rules produced no measurable performance gain — solver checkpoint/restore is already ~0.5µs per call, negligible at 477 calls total.

## Completed (post-arrlit)

### Opt_H: Fingerprint prediction (DONE, stage 16 in roadmap)

After applying a rule, the new PC value is known from the consequent → determines the next fingerprint and candidate rule. Skips `findAllMatches` for 87% of nodes. Measured ~3% improvement (per-call cost is small at ~2µs).

Combined with TODO_0063 (arrlit), the benchmark moved from ~8.1ms (pre-arrlit, 689 nodes) to ~5.3ms (477 nodes, 11.1µs/node). The arrlit representation change halved absolute cost by reducing cloning and matching overhead.

### ~~Inline predicted step~~ — REJECTED

Analyzed and rejected (2026-03-03). Fusing tryMatch + mutateState into one pass saves only ~0.3ms (intermediate allocs), not the ~0.8ms originally estimated. Irreducible work (FactSet binary search, Zobrist, FFI, Store.put) dominates. Damages the clean `strategy → match → mutate` separation. See `doc/documentation/forward-optimization-roadmap.md` lesson #13.

### ~~Opt_C: Per-predicate persistent dispatch~~ — SUBSUMED

Subsumed by Opt_G for all EVM persistent predicates (inc, plus, neq, mul). No remaining value for the current benchmark target.

## JS-Level Optimization: Exhausted

The profile is flat at ~5.3ms / 477 nodes (~11µs/node). No single component dominates. Micro-allocation optimizations (pooling, precomputed tagIds, inline predicted step) have all been tested or analyzed and shown to be below the noise floor. The remaining path to sub-1ms is the Zig port (estimated 5-8× overall speedup, dominated by BigInt → u256 elimination in FFI arithmetic).

## Key Insights

1. **The bottleneck is dispatch, not computation.** Matching (145ns/call) and FFI arithmetic (50-120ns) are fast. The 86% overhead is orchestration: dispatch, allocation, guard checks.
2. **V8's 4-closure IC threshold is the fundamental constraint.** >4 distinct closures at a call site → megamorphic → ~25% regression. Blocks "compile each rule to a closure". Must stay within the monomorphic pipeline.
3. **matchIdx is already fast for flat patterns.** JS-level bypass doesn't beat tight recursive unification for simple 2-child patterns.
4. **Only 31 of 2125 nodes store snapshots.** FactSet.snapshot (~250ns) is 600× cheaper than toObject (~150µs).

## Appendix: Profiling Data

<details>
<summary>Original instrumented breakdown (pre-TODO_0059)</summary>

Scaled from 20.8ms instrumented to 13.6ms real:

| Function | Time | % | Calls | Per-call | Current status |
|---|---|---|---|---|---|
| findAllMatches | 5.9ms | 43% | 468 | 12.7µs | reduced (Opt_G) |
| snapshotState | 2.5ms | 18% | 11 | 228µs | **eliminated** (Opt_A) |
| mutateState | 2.2ms | 16% | 476 | 4.6µs | faster (FactSet) |
| undoMutate | 0.4ms | 3% | 476 | 0.8µs | Arena undo |
| makeChildCtx | 0.3ms | 2% | 476 | 0.6µs | **eliminated** (0059) |
| drainPersistentLolis | 0.3ms | 2% | 476 | 0.6µs | ~similar |
| solver (all ops) | 0.3ms | 2% | 520 | 0.5µs | ~similar |
| undoIndexChanges | 0.2ms | 1% | 476 | 0.4µs | **eliminated** (0059) |
| computeControlHash | 0.1ms | 1% | 477 | 0.2µs | ~similar |
| DFS overhead | 1.4ms | 10% | — | — | reduced |

</details>

<details>
<summary>findAllMatches before vs after Opt_G</summary>

| Operation | Before Opt_G | After Opt_G | Change |
|---|---|---|---|
| matchIdx | 10,376 calls / 3.51ms | 7,021 calls / 2.94ms | -32% / -0.57ms |
| substitute | 2,262 calls / 1.89ms | 893 calls / 0.79ms | -61% / -1.10ms |
| backward prove | 13 calls / 0.68ms | 13 calls / 1.40ms | same calls (variance) |
| **Total profiled** | **6.08ms** | **5.13ms** | **-15.6%** |

</details>

<details>
<summary>Structural findings</summary>

- **670/689 explored nodes are fully deterministic** (1 match, 1 alt).
- **Average matches per node: ~1.0** — fingerprint layer is perfectly selective.
- **~17 matchIdx calls per node** → ~15 after Opt_G.
- Persistent antecedents: inc (dominant), plus, mem_expand, neq, mem_read.

</details>

**Theoretical JS minimum: ~2.8µs/step × 679 = ~1.9ms.**

## Connection to Other TODOs

- **TODO_0059 (FactSet Migration): DONE.** 16.6ms → 11.6ms.
- **TODO_0057 (Ephemeral Transit States):** Level 1 invalidated. Level 3b = Opt_H.
- **TODO_0054 (Commuting Match Reduction):** Orthogonal (reduces node count).
- **TODO_0005 (Constraint Propagation):** Orthogonal (reduces state size).
