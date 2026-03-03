---
title: "Zig Port Preparation — Closure Elimination and Allocation Reduction"
created: 2026-03-02
modified: 2026-03-02
completed: 2026-03-02
summary: "Systematic refactoring of JS engine code toward Zig-portable patterns: replace closures with dispatch structs, pool hot-path allocations, and document the porting order. Estimated 3,600 JS LOC → ~6,000 Zig LOC across kernel + engine layers."
tags:
  - architecture
  - performance
  - optimization
  - symexec
  - forward-chaining
  - data-structures
  - arena-allocation
type: design
status: done
priority: 4
cluster: Performance
depends_on: []
required_by: []
---

# TODO 0061: Zig Port Preparation

## Motivation

The CALC engine core (~3,600 LOC across kernel + engine) is the performance-critical path. The current JS implementation already uses Zig-friendly patterns in some places (SoA TypedArrays in Store, Arena undo logs in FactSet) but relies heavily on JS-specific features elsewhere (closures in compiled matching, object-per-call allocations in tryMatch, dynamic dispatch). A Zig port of the core would eliminate GC pauses, enable SIMD group scanning, and give predictable cache behavior.

This TODO prepares the JS code for porting by:
1. Replacing closures with data-driven dispatch (directly portable to Zig `fn` pointers + context structs)
2. Pooling hot-path allocations (maps to Zig arena allocators)
3. Documenting the porting order and expected performance profile

**Non-goal:** actually writing Zig code. This is JS refactoring that makes the eventual port mechanical.

## Current State — What's Already Zig-Friendly

| Component | LOC | Zig Score | Notes |
|---|---|---|---|
| `store.js` (SoA arena) | 450 | 92% | TypedArray arena, tag registry, dedup Map |
| `fact-set.js` (FactSet + Arena) | 443 | 90% | Sorted Int32Array groups, Zobrist hash, checkpoint/restore |
| `constraint.js` (EqNeqSolver) | 184 | 88% | Union-find + forbid list, array-based rollback |
| `substitute.js` | 260 | 93% | Flat theta arrays, de Bruijn indexed, no closures |
| `state-ops.js` | 127 | 95% | Pure functions, typed-array mutations, no closures |

These modules port nearly 1:1. The SoA layout maps to Zig `MultiArrayList`, Arena to `FixedBufferAllocator`, sorted groups to `std.sort.sort`.

## What Needs Refactoring

### TODO_0061.Stage_1 — Closure Elimination in compile.js (311 LOC)

**Problem:** `compilePatternMatch` and `compilePersistentStep` generate closures at rule compile time. Each closure captures its pattern structure as closed-over variables. In Zig, closures don't exist — you need a function pointer + context struct.

**Current (closure):**
```js
function compilePatternMatch(hash, slots) {
  const tid = Store.tagId(hash);
  const a = Store.arity(hash);
  const cm0 = compilePatternMatch(Store.child(hash, 0), slots);
  return (h, theta) =>
    Store.tagId(h) === tid && Store.arity(h) === a &&
    cm0(Store.child(h, 0), theta);
}
```

**Target (data-driven dispatch):**
```js
// Instruction: { op: 'compound', tagId, arity, children: [Instruction] }
//            | { op: 'bind', slot }
//            | { op: 'check', slot }
//            | { op: 'ground', expected }
function compilePatternInstructions(hash, slots) { ... }
function executePatternMatch(instructions, h, theta) { ... }
```

Three instruction types suffice:
- `BIND(slot)` — bind metavar to fact child
- `CHECK(slot)` — check metavar equals fact child
- `GROUND(hash)` — identity check (content-addressed)
- `COMPOUND(tagId, arity, children[])` — tag check + recurse

**Performance expectation:** Neutral or slight regression in JS (indirect dispatch vs direct closure call), but the instruction array is a flat serializable struct — directly portable to Zig `[]const Instruction`.

**Files touched:** `lib/engine/compile.js`

### TODO_0061.Stage_2 — Closure Elimination in compilePersistentStep (compile.js)

**Problem:** `compilePersistentStep` generates a closure per persistent antecedent pattern for FFI fast-path. Each captures: ffi function, mode array, arg specs, slots.

**Target:** Replace with a struct `{ ffiFn, modes, argSpecs[], slots[] }` and a single `executePersistentStep(spec, theta)` interpreter. The spec is a plain object — no closures.

**Performance expectation:** Neutral. The FFI dispatch itself dominates.

**Files touched:** `lib/engine/compile.js`, `lib/engine/match.js` (call site in `matchAllLinear`)

### TODO_0061.Stage_3 — Allocation Pooling in tryMatch (match.js)

**Problem:** Every `tryMatch` call allocates 4 fresh objects:
```js
const consumed = {};      // hash → count map
const reserved = {};      // hash → count map
const theta = new Array(metavarCount);  // substitution
const preservedCount = {}; // hash → count map
```

In solc_symbolic, `tryMatch` is called ~500× per explore. That's 2,000 object allocations per tree, all short-lived (GC pressure).

**Target:** Pre-allocate and reuse via a pool:
```js
// Module-level reusable buffers
const _consumed = {};
const _reserved = {};
const _theta = new Array(MAX_SLOTS);  // 32 is current max
const _preservedCount = {};

function tryMatch(rule, state, calc, matchOpts) {
  // Clear instead of allocate
  for (const k in _consumed) delete _consumed[k];
  for (const k in _reserved) delete _reserved[k];
  _theta.fill(undefined, 0, rule.metavarCount);
  ...
}
```

**V8 caveat:** Object property deletion triggers hidden class transitions. Alternative: use `Map` (clear() is O(1)) or parallel Int32Array keyed by hash.

**Zig equivalent:** Stack-allocated `[MAX_SLOTS]?u32` array + `AutoHashMap(u32, u32)` for consumed/reserved.

**Performance expectation:** 5–15% speedup in JS (reduced GC pressure). In Zig, these become stack allocations — zero cost.

**Files touched:** `lib/engine/match.js`

### TODO_0061.Stage_4 — State Snapshot Elimination

**Problem:** `explore()` calls `toObject(state)` at every terminal node (31 of 477 nodes in solc_symbolic). `toObject` walks all FactSet groups building `{ hash: count }` objects. This is the conversion from Zig-friendly TypedArrays back to JS objects.

**Current terminal:**
```js
if (matches.length === 0) {
  return { type: 'leaf', state: state.snapshot() };
}
```

**Target:** Return arena pointer (checkpoint) instead of materialized state. Materialize only on demand (e.g., when the user inspects a specific leaf).

```js
if (matches.length === 0) {
  return { type: 'leaf', checkpoint: linArena.checkpoint(), perCheckpoint: perArena.checkpoint() };
}
```

**Complication:** Current arena is stack-scoped (undo restores on DFS backtrack). To keep terminal snapshots, need either: (a) copy arena segment at terminal, (b) use persistent data structure, or (c) materialize eagerly but into a typed format (not JS objects).

**Recommendation:** Option (c) for now — serialize terminal state as `Int32Array` pairs `[tag, hash, count]` instead of JS objects. This is what the Zig port would use anyway.

**Performance expectation:** 10–20% for terminal-heavy trees. Eliminates O(groups) object construction.

**Files touched:** `lib/engine/symexec.js`, `lib/engine/fact-set.js`

### TODO_0061.Stage_5 — String Interning Table

**Problem:** Store uses JS `Map` for string dedup (`_strings`, `_bigints`). In Zig, need a proper string interning table.

**Current:** Strings referenced by index into `_stringTable` array, deduped via `_stringDedup` Map. This is close to Zig's `StringHashMap` pattern.

**Preparation:** Extract string table into its own module with a clean interface:
```js
class StringTable {
  intern(s) → index
  get(index) → string
  size() → count
}
```

**Zig equivalent:** `std.StringHashMap(u32)` + `ArrayList([]const u8)`.

**Files touched:** `lib/kernel/store.js`

## Porting Order

Phase 1 (kernel, no dependencies):
```
store.js → substitute.js → unify.js
```

Phase 2 (state primitives):
```
fact-set.js → state-ops.js → constraint.js
```

Phase 3 (matching, depends on Phase 1+2):
```
compile.js → match.js → prove.js
```

Phase 4 (execution, depends on Phase 3):
```
strategy.js → forward.js → symexec.js
```

Each phase is independently testable via FFI bridge (Zig compiled to shared library, called from JS test harness).

## Performance Projections

| Component | JS (current) | Zig (estimated) | Speedup | Basis |
|---|---|---|---|---|
| Store.put | 0.3µs | 0.05µs | 6× | No GC, no Map overhead |
| FactSet.insert | 0.15µs | 0.03µs | 5× | Binary search on raw memory |
| matchAllLinear | 4µs | 0.8µs | 5× | No allocation, branch-free |
| provePersistentGoals | 2µs | 0.15µs | **13×** | BigInt→u256 (20-40× for arithmetic), state lookup same |
| mutateState | 1µs | 0.2µs | 5× | Arena insert is ~4 writes |
| **explore() total** | **5.3ms** | **~0.7ms** | **~7.5×** | solc_symbolic, 477 nodes |

The provePersistentGoals speedup is higher than other components because V8 BigInt is heap-allocated with GC tracking (~100-200ns per arithmetic op) while Zig u256 is stack-allocated (`[4]u64`, ~5ns per op). All EVM persistent goals (inc, plus, neq, mul) are FFI arithmetic — this is where the Zig port gains most.

Conservative estimate: **5–8× overall speedup** for symexec workloads. The per-component table underestimates BigInt elimination: V8 BigInt arithmetic (~100-200ns/op, heap-allocated) → Zig u256 (`[4]u64`, stack-allocated, ~5ns/op) is 20-40× for FFI arithmetic alone (inc, plus, neq, mul). Since persistent proving is ~34% of explore time, the 4× estimate for `provePersistentGoals` should be 8-15×. Additionally, GC pause elimination removes the bimodal 2× variance, and SIMD group scanning could add another 2× within the Zig baseline.

Main wins: BigInt → u256 elimination (dominant), GC pause elimination (intermittent 2× spikes visible in current benchmarks), cache-friendly SoA iteration, branch-free matching dispatch, deterministic performance (no JIT warmup/variance).

## V8 Deoptimization Learnings

Documented during audit (2026-03-02):

1. **`new Array(n).fill(0)` vs `[0, 0, 0, 0]`** — 2× regression on hot-path buffer. V8 optimizes literal arrays with known element types; `new Array(n).fill(0)` produces a generic (holey) internal representation that defeats TurboFan's type specialization. Fixed: keep literal + load-time arity assertion.

2. **Cross-module calls are fine** — TurboFan inlines across `require()` boundaries based on bytecode size and call frequency, not file boundaries. Empirically verified: `mutateState` delegating to `state-ops.js` shows identical performance to inline code (4.8ms vs 4.8ms over 8 processes). The `state-ops.js` deduplication is safe.

3. **Bimodal JIT behavior** — solc_symbolic shows 5ms or 14ms depending on V8 JIT decisions (nondeterministic). Same code, same data, ~2× variance across process invocations. Zig eliminates this class of issue entirely.

These findings reinforce the case for Zig: the current performance ceiling is V8's optimization nondeterminism, not algorithmic.

## Cleanup After Port

Once the Zig core is operational:

1. **JS engine becomes thin FFI wrapper** — `lib/engine/*.js` replaced by `lib/engine/native.js` calling compiled `.so`
2. **Keep JS for**: parser pipeline (convert.js, declarations.js), browser bundle (out/ill.json), UI layer
3. **Remove**: TypedArray workarounds in store.js (direct Zig memory), Arena class (Zig allocator), fact-set.js (Zig struct)
4. **Test strategy**: run existing JS test suite against Zig FFI bridge — same inputs, same expected outputs

Estimated post-port deletions: ~2,000 LOC JS (replaced by ~6,000 LOC Zig + ~200 LOC FFI bridge).

## Completion Results (2026-03-02)

All 5 stages implemented. 688 tests passing throughout.

### Commits
1. `6e86287` Stage 2: compilePersistentStep closure → spec struct
2. `98ff462` Stage 3: tryMatch allocation pooling via Map pools
3. `1685f8f` Stage 1: compilePatternMatch closure → instruction array
4. `ae10aea` Stage 4: FactSet.snapshotBulk() — single allocation for terminal states
5. `3581775` Stage 5: extract StringTable class in store.js

### Benchmark (40 iterations, `bench:diff:symexec` vs pre-0061)

| Benchmark | Before | After | Change |
|---|---|---|---|
| multisig | 1.26ms | 1.17ms | −6.9% |
| solc_symbolic | 4.88ms | 4.94ms | ~neutral |
| **geometric mean** | | | **−2.9%** |

Full end-to-end solc_symbolic (load + decompose + explore): ~26ms median.
