---
title: "Symexec Sub-4ms: Per-Step Optimization Analysis"
created: 2026-02-28
modified: 2026-03-02
summary: "Deep profiling of symbolic multisig explore(). TODO_0059 done (16.6→11.6ms). Opt_A done (11.6→9.2ms). Opt_G done (persistent steps: -32% matchIdx, -61% substitute, ~6-12% wall-clock). Next: Opt_E (skip solver) + Opt_H (threaded code)."
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

| Metric | Original | After 0059 | After Opt_A | After Opt_G | Target |
|---|---|---|---|---|---|
| Nodes | 689 | 689 | 689 | 689 | 689 |
| Leaves | 10 | 10 | 10 | 10 | 10 |
| Median time | **16.6ms** | **11.6ms** | **~9.2ms** | **~8.3ms** | **4ms** |
| Per-node cost | 24µs | 16.8µs | ~13.3µs | ~12µs | 5.8µs |

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

### Opt_G — Compiled Matching → Persistent Step Fast Path (DONE, 2026-03-02)

**Measured: -32% matchIdx calls, -61% substitute calls, ~6-12% wall-clock.**

| Metric | Before | After | Change |
|---|---|---|---|
| matchIdx calls | 10,376 | 7,021 | **-32%** (-3,355) |
| substitute calls | 2,262 | 893 | **-61%** (-1,369) |
| Profiled time | 6.08ms | 5.13ms | **-15.6%** |

Files changed: `compile.js` (~50 LOC), `match.js` (10 LOC), `index.js` (1 LOC), `compiled-matcher.test.js` (new, 16 tests).

#### What shipped: `persistentSteps`

Pre-compiled FFI closures attached to each rule at `compileRule()` time. Called from the existing monomorphic `matchAllLinear` path, bypassing `subApplyIdx` + `tryFFIDirect` + theta transfer for ground FFI goals (inc, plus, neq, mul).

Only ~4 distinct closure types → stays within V8's polymorphic IC threshold (≤4 shapes).

```javascript
// In matchAllLinear Phase 2, before generic provePersistentGoals:
const step = rule.persistentSteps[persistentIdx];
if (step) {
  const r = step(theta);       // compiled FFI closure
  if (r === true) continue;    // success: skip subApplyIdx + tryFFIDirect
  if (r === false) return -1;  // definitive failure (e.g. neq with equal args)
  // null → fall through to generic path (non-ground input, etc.)
}
```

#### What failed: per-rule compiled matchers

The original plan generated 59 per-rule closures dispatched from one call site in `tryMatch`:

```javascript
if (rule.compiledMatcher) return rule.compiledMatcher(state, calc);
```

This caused **~25% regression** due to V8 megamorphic dispatch. V8's inline cache degrades after 4+ distinct closures at a call site (`--max-polymorphic-map-count=4`). With 59 closures, the IC transitions to megamorphic: hash-table lookup (~3.5× slower), TurboFan can't inline the callee, can't propagate types through the call, may decline to optimize the containing function.

See [RES_0069](../research/0069_v8-megamorphic-dispatch.md) for full analysis.

**Workarounds considered:**
- **Switch dispatch** (each case monomorphic) — would work but requires rewriting the entire matching pipeline as a single switch on rule opcode
- **Defunctionalization** (single function + data descriptor) — the generic `tryMatch` IS already defunctionalized; closures were an attempt to go beyond it
- **`new Function()` codegen** — CSP restrictions, debugging pain
- **Hot-path split** (if-else for top rules) — only works for skewed distributions

All viable workarounds require fundamentally different architecture. The persistent step approach extracts what's possible within the current monomorphic pipeline.

#### What failed: flat bypass for consumed patterns

Extended Strategy A (delta bypass) from delta-only to all flat patterns. Reduced matchIdx calls by 27% (4,941 → 3,611) but **regressed wall time**. Root cause: for simple 2-child patterns like `stack(SH, B)`, the JS-level bypass code (ground check loop + binding loop + undo tracking) is not faster than `matchIdx` (tight recursive unification). The bypass only wins for delta patterns where it additionally avoids the undo mechanism.

#### Why 3.5ms → ~0.9ms actual

The 3.5ms projection assumed:
- Compiled linear matchers eliminate `matchOnePattern` dispatch: ~1.5ms → **blocked by V8 megamorphic**
- Inline FFI (persistent steps): ~1.0ms → **delivered ~0.9ms**
- Reusable buffers (Opt_F): ~0.5ms → **not implemented** (marginal: V8 array alloc is ~10-20ns)
- Flat bypass for consumed patterns: ~0.3ms → **regressed**

The "86% dispatch overhead in findAllMatches" finding remains valid — dispatch IS the bottleneck — but eliminating it requires staying within V8's IC monomorphism constraints. Per-rule closures violate this. Only the persistent proving path could be compiled (≤4 FFI types).

## Remaining Optimizations

### Opt_E: Skip solver for non-oplus rules (~0.3ms)

Currently `explore()` checkpoints/restores the constraint solver on every node. For non-oplus rules (most rules), this is wasted. Simple 3-line conditional in `symexec.js`.

### Opt_H: Threaded code / fingerprint prediction (~1.7ms) — biggest remaining win

After applying a rule, the new PC value is known from the consequent. This determines the next fingerprint and candidate rule. 670 predicted deterministic steps × ~2.5µs = ~1.7ms saved by skipping `findAllMatches` entirely.

Does NOT hit the megamorphic wall: prediction is a lookup table (PC → rule), not closure dispatch. The predicted rule uses the same monomorphic `tryMatch` path.

### Opt_C: Per-predicate persistent dispatch (~0.5ms) — partially subsumed

Subsumed by Opt_G for FFI predicates (inc, plus, neq, mul). Remaining value: non-FFI persistent predicates that still go through generic `provePersistentGoals`.

## Performance Projection

| Level | Optimizations | Estimated time | vs original |
|---|---|---|---|
| Original (pre-0059) | — | 16.6ms | — |
| **After TODO_0059** | FactSet migration (measured) | **11.6ms** | **1.43×** |
| **After Opt_A** | FactSet snapshots (measured) | **~9.2ms** | **1.8×** |
| **After Opt_G** | Persistent step fast path (measured) | **~8.3ms** | **2.0×** |
| After Opt_E | Skip solver for non-oplus (−0.3ms) | ~8.0ms | 2.1× |
| After Opt_H | Threaded code (−1.7ms) | ~6.3ms | 2.6× |

## Key Insights

1. **The bottleneck is dispatch, not computation.** Matching (145ns/call) and FFI arithmetic (50-120ns) are fast. The 86% overhead is orchestration: dispatch, allocation, guard checks.

2. **V8's 4-closure IC threshold is the fundamental constraint.** Any optimization that creates >4 distinct closures/shapes at a single call site will regress. This blocks the obvious "compile each rule to a closure" approach. Staying within the monomorphic pipeline and specializing only small, bounded pieces (≤4 FFI types) is the viable path.

3. **FFI dispatch is 10× more expensive than the computation.** `provePersistentGoals → subApplyIdx → tryFFIDirect → fn` adds 430ns around a 46ns computation. Persistent steps eliminate this for ground goals.

4. **matchIdx is already fast for flat patterns.** JS-level bypass code (child extraction loops) does not beat the tight recursive `matchIdx` for simple 2-child patterns. Bypass only wins for delta patterns where it additionally skips undo bookkeeping.

5. **Recursion is free.** V8 JIT makes DFS calls zero-cost. Iterative loops save nothing.

6. **Only 31 of 2125 nodes store snapshots.** Branch nodes have `state: null`. FactSet.snapshot (~250ns) is 600× cheaper than toObject (~150µs).

## Original Profiling Results (pre-TODO_0059)

### Instrumented breakdown (scaled from 20.8ms instrumented to 13.6ms real)

| Function | Time | % | Calls | Per-call | Current status |
|---|---|---|---|---|---|
| findAllMatches | 5.9ms | 43% | 468 | 12.7µs | partially reduced (Opt_G) |
| snapshotState | 2.5ms | 18% | 11 | 228µs | **eliminated** (Opt_A) |
| mutateState | 2.2ms | 16% | 476 | 4.6µs | faster (FactSet) |
| undoMutate | 0.4ms | 3% | 476 | 0.8µs | → Arena undo (faster) |
| makeChildCtx | 0.3ms | 2% | 476 | 0.6µs | **eliminated** (0059) |
| drainPersistentLolis | 0.3ms | 2% | 476 | 0.6µs | ~similar |
| solver (all ops) | 0.3ms | 2% | 520 | 0.5µs | ~similar (target: Opt_E) |
| undoIndexChanges | 0.2ms | 1% | 476 | 0.4µs | **eliminated** (0059) |
| computeControlHash | 0.1ms | 1% | 477 | 0.2µs | ~similar |
| DFS overhead | 1.4ms | 10% | — | — | reduced |

### Inside findAllMatches — before vs after Opt_G (CALC_PROFILE)

| Operation | Before Opt_G | After Opt_G | Change |
|---|---|---|---|
| matchIdx | 10,376 calls / 3.51ms | 7,021 calls / 2.94ms | -32% / -0.57ms |
| substitute | 2,262 calls / 1.89ms | 893 calls / 0.79ms | -61% / -1.10ms |
| backward prove | 13 calls / 0.68ms | 13 calls / 1.40ms | same calls (variance) |
| **Total profiled** | **6.08ms** | **5.13ms** | **-15.6%** |

### Structural findings

- **670/689 explored nodes are fully deterministic** (1 match, 1 alt).
- **Average matches per node: ~1.0** — the fingerprint layer is perfectly selective.
- **~17 matchIdx calls per node** → ~15 after Opt_G.
- Persistent antecedents: inc (dominant), plus, mem_expand, neq, mem_read.

## Theoretical Minimum

Per-step irreducible work (JS, after all optimizations):
1. Pattern matching: 5 linear × ~300ns = 1.5µs
2. Persistent proving: 2 × ~50ns (inlined FFI) = 0.1µs
3. State mutation: 5 × ~200ns (subCompiled + FactSet) = 1.0µs
4. Hash/cycle check: ~0.2µs

**JS minimum: ~2.8µs/step × 679 = ~1.9ms.**

## Connection to Other TODOs

- **TODO_0059 (FactSet Migration): DONE.** 16.6ms → 11.6ms.
- **TODO_0057 (Ephemeral Transit States):** Level 1 invalidated. Level 3b = Opt_H.
- **TODO_0054 (Commuting Match Reduction):** Orthogonal (reduces node count).
- **TODO_0005 (Constraint Propagation):** Orthogonal (reduces state size).
