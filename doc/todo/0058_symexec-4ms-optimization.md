---
title: "Symexec Sub-4ms: Per-Step Optimization Analysis"
created: 2026-02-28
modified: 2026-03-01
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

Replaced `toObject(state)` with `state.snapshot()` at all 5 terminal return sites in `symexec.explore()`. Only 31 terminal nodes (of 2125 total) get snapshots — the 2094 branch nodes store `state: null`. Made `show.js` (`classifyLeaf`, `showInteresting`) polymorphic via duck-typing (`state.linear.group` for FactSet path, plain-object fallback for hand-built test fixtures).

| File | Change |
|---|---|
| `lib/engine/fact-set.js` | Added `State.hasLinear(hash)` |
| `lib/engine/symexec.js` | 5× `toObject(state)` → `state.snapshot()`, removed `toObject` import |
| `lib/engine/show.js` | Polymorphic `classifyLeaf`/`showInteresting` (FactSet + plain object) |
| `tests/engine/explore.test.js` | 1 site → `state.hasLinear()` |
| `tests/engine/solc-benchmark.test.js` | 1 site → `linear.groupLen()` |
| `tests/engine/memory.test.js` | 7 blocks → FactSet group access |

**Not changed:** `forward.js` still returns plain objects via `toObject()` (single call at API boundary, different use case). `toObject` remains exported from `fact-set.js` — used by `forward.js` (2 calls), `fact-set.test.js` (4 roundtrip tests), `symexec-bench.js` (3 calls in instrumented profiler).

### ~~Opt_B: Skip drainPersistentLolis early exit~~ — DONE (part of TODO_0059)

### Opt_C, Opt_E — standalone low-risk optimizations

Opt_C (per-predicate persistent dispatch, ~0.5ms) and Opt_E (skip solver for non-oplus, ~0.3ms) remain viable as standalone changes. Both are also naturally subsumed by Opt_G.

## Opt_G: Compiled Matching — DONE (2026-03-02)

### Outcome: Persistent Step Fast Path

**Measured: -32% matchIdx calls, -61% substitute calls, ~6-12% wall-clock improvement.**

The original plan for per-rule closure dispatch (59 closures at one call site) caused **V8 megamorphic regression** (~25% slower). V8's inline cache degrades after 4+ distinct closures at a call site (see [RES_0069](../research/0069_v8-megamorphic-dispatch.md)).

**Pivot**: Removed compiled linear matching entirely. Kept only `persistentSteps` — pre-compiled FFI closures (~4 types, stays within V8's polymorphic threshold). These are called from the existing monomorphic `matchAllLinear` path.

| Metric | Before | After | Change |
|---|---|---|---|
| matchIdx calls | 10,376 | 7,021 | **-32%** |
| substitute calls | 2,262 | 893 | **-61%** |
| Profiled time | 6.08ms | 5.13ms | **-15.6%** |

Files changed: `compile.js` (~50 LOC), `match.js` (10 LOC), `index.js` (1 LOC), `compiled-matcher.test.js` (new, 16 tests).

### Why 3.5ms → ~0.9ms actual

The original 3.5ms projection assumed compiled linear matchers would eliminate matchOnePattern dispatch (~1.5ms) AND inline FFI (~1.0ms) AND reuse buffers (~0.5ms). V8 megamorphic dispatch blocked the linear matcher component. Only the FFI inlining (persistent steps) was viable, yielding ~0.9ms. The flat bypass for consumed patterns (Strategy A extension) was attempted but regressed wall-clock despite 27% fewer matchIdx calls — the JS-level bypass code is not faster than matchIdx for simple 2-child patterns.

## Remaining Optimizations

### Opt_E: Skip solver for non-oplus rules (~0.3ms)

Independent of G. Simple conditional in `symexec.js`.

### Opt_H: Threaded code / fingerprint prediction (~1.7ms)

After applying a rule, predict next rule from new PC value → skip `findAllMatches` for deterministic chains. Biggest remaining opportunity.

## Original Opt_G Specification (archived)

### What It Is

Auto-generate specialized match closures at `compileRule()` time. Each eligible rule gets a `rule.compiledMatcher` closure that replaces the generic `tryMatch` dispatch chain. Same semantics, less dispatch.

**This is NOT a JIT compiler or code generator.** No files generated, no new build steps. Closures are plain JavaScript functions created in-memory during `mde.load()`. Changing `.ill` files requires no manual recompilation — `mde.load()` already parses, compiles, and generates closures in one pass.

**Timing context:** `mde.load()` is one-time setup (~50-200ms for file I/O, tree-sitter parsing, Store population). The benchmark only measures `explore()` (~9ms). Adding ~0.5ms for closure generation goes into the one-time setup cost. Eager precompilation for all eligible rules — no lazy/warmup needed.

### What It Eliminates Per Node (~5.3µs)

| Eliminated overhead | Saving |
|---|---|
| `matchOnePattern` role dispatch × 5 patterns | ~1.5µs |
| `state.linear.count()` binary searches × 5 | ~0.5µs |
| `consumed[h] \|\| 0` property lookups × 5 | ~0.3µs |
| `subApplyIdx` recursive walk for FFI goals × 2 | ~0.6µs |
| `tryFFIDirect` 3 map lookups + mode loop × 2 | ~0.8µs |
| FFI result object alloc + theta pair processing | ~0.3µs |
| `matchAllLinear` worklist + phase switching | ~0.3µs |
| `tryMatch` allocation (consumed, reserved, theta) | ~0.8µs |

For ~536 hot-path nodes: 536 × 5.3µs ≈ **2.8ms**. Non-hot firings save ~0.7ms more. **Total: ~3.5ms.**

### Background: tryMatch Flow and De Bruijn Slots

Understanding how the generic `tryMatch` works is essential for the generator.

**De Bruijn slots.** At compile time, `compileRule` collects all metavars (freevars starting with `_`) and assigns each a numeric slot index:

```
Rule: code PC Opcode * !inc PC PC2 -o { bar PC2 }

Metavars collected: _PC, _Opcode, _PC2
Slot assignment:    _PC → 0, _Opcode → 1, _PC2 → 2

rule.metavarSlots = { hash_of_PC: 0, hash_of_Opcode: 1, hash_of_PC2: 2 }
rule.metavarCount = 3
```

`theta` is a flat array `[binding_0, binding_1, binding_2]` indexed by slot number. At match time:

1. **Allocate:** `theta = new Array(3)`, `consumed = {}`, `reserved = {}`
2. **Match linear patterns:** For each pattern, call `matchOnePattern` → dispatch by role → `matchIdx(pattern, fact, theta, slots)` → unify, binding metavar hashes into theta via slot lookup
3. **Prove persistent antecedents:** Call `provePersistentGoals` → for each pattern, 3-level fallback:
   - Level 1: State lookup (scan `state.persistent.group(tagId)`, unify against each)
   - Level 2a: FFI (`subApplyIdx(pattern, theta, slots)` → `tryFFIDirect(goal)`)
   - Level 2b: Clause resolution (`backward.prove(goal, clauses, types)`)
4. **Return:** `{ rule, theta, slots, consumed, optimized }`

FFI returns metavar hashes, not slot indices: `{ theta: [[metavar_hash, result_hash]] }`. The slot transfer loop converts: `slot = slots[metavar_hash]; theta[slot] = result_hash`.

### Persistent Proving: FFI-First vs State-Lookup-First

The current code always does state lookup first, then FFI. This is suboptimal:

- **Ground goal** `!plus(5, 3, Z)`: FFI computes the answer in nanoseconds. State lookup scans ~10-30 persistent `plus` facts with full `matchIdx` per entry. FFI-first is faster.
- **Symbolic goal** `!plus(X, 3, Z)` where X is unbound: FFI can't compute (input not ground). State lookup is the only option.

**Key insight:** Groundness of FFI input slots is known at **compile time** from slot dependency analysis. If all input slots are bound by prior linear matching, the goal will always be ground at runtime. The generator bakes this decision:

```javascript
// Compile-time: inc's input (slot 0) is always bound by linear match → emit FFI-first
theta[2] = Store.put('s', [theta[0]]);  // no state lookup, no dispatch

// Compile-time: myPred's input may be symbolic → emit state-lookup-first
const grp = state.persistent.group(MY_PRED_TAG);
for (...) { if (matchIdx(...)) { found = true; break; } }
if (!found) { backward.prove(...); }  // clause fallback
```

### Eligibility Criteria (Relaxed)

A rule qualifies for compiled matching if:

1. All linear patterns have known predicate tags (no wildcards)
2. All patterns are flat (children are metavars or ground constants)
3. No persistent dependencies between linear patterns (no deferred matching)
4. Single-alt consequent (no oplus/with branching in consequent)

**Criterion 4 from original spec ("all persistent antecedents have FFI") is dropped.** Non-FFI persistent antecedents are handled by:

- Inlining Level 1 (state lookup) with tag ID baked as compile-time constant
- Calling Level 2b (clause resolution via `prove.js`) as fallback — not inlined, but still called from the closure

This means **any rule with flat independent linear patterns** qualifies, regardless of FFI availability. For EVM: ~38/44 rules qualify (up from ~35). For pure-logic programs without FFI: all rules with flat patterns qualify (savings smaller — only linear dispatch overhead eliminated, not FFI dispatch).

**Partial specialization** for ineligible rules (complex patterns, oplus consequents): inline linear matching only, fall back to generic `provePersistentGoals`. Still saves linear dispatch overhead.

### Concrete Examples

**EVM rule (with FFI):** `code PC Op * !inc PC PC2 -o { ... }`

```javascript
// Generated closure:
const CODE_TAG = Store.TAG['code'];  // baked constant
rule.compiledMatcher = function(state) {
  const theta = this._theta;
  theta[0] = 0; theta[1] = 0; theta[2] = 0;

  const grp = state.linear.group(CODE_TAG);
  if (grp.length === 0) return null;
  const fact = grp[0];
  theta[0] = Store.child(fact, 0);            // PC → slot 0
  theta[1] = Store.child(fact, 1);            // Op → slot 1
  theta[2] = Store.put('s', [theta[0]]);      // PC2 = inc(PC), FFI inlined

  return { consumed: { [fact]: 1 }, theta, slots: this._slots };
};
```

**Non-EVM rule (no FFI):** `token X * !myCheck X -o { result X }`

```javascript
const TOKEN_TAG = Store.TAG['token'];
const CHECK_TAG = Store.TAG['myCustomCheck'];
rule.compiledMatcher = function(state) {
  const theta = this._theta;
  theta[0] = 0;

  const grp = state.linear.group(TOKEN_TAG);
  if (grp.length === 0) return null;
  theta[0] = Store.child(grp[0], 0);          // X → slot 0

  // Level 1: state lookup (inlined, tag constant baked)
  const checkGrp = state.persistent.group(CHECK_TAG);
  let found = false;
  for (let i = 0; i < checkGrp.length; i++) {
    if (Store.child(checkGrp[i], 0) === theta[0]) { found = true; break; }
  }
  if (!found) {
    // Level 2b: backward prove (called, not inlined)
    const goal = Store.put('myCustomCheck', [theta[0]]);
    const r = this._prove(goal);
    if (!r.success) return null;
  }

  return { consumed: { [grp[0]]: 1 }, theta, slots: this._slots };
};
```

**Rule with structural matching:** `plus X (s Y) (s Z) -o { !plus X Y Z }`

```javascript
const PLUS_TAG = Store.TAG['plus'];
const S_TAG = Store.TAG['s'];
rule.compiledMatcher = function(state) {
  const theta = this._theta;
  theta[0] = 0; theta[1] = 0; theta[2] = 0;

  const grp = state.linear.group(PLUS_TAG);
  for (let i = 0; i < grp.length; i++) {
    const h = grp[i];
    const c1 = Store.child(h, 1);
    const c2 = Store.child(h, 2);
    if (Store.tagId(c1) !== S_TAG) continue;  // must be s(...)
    if (Store.tagId(c2) !== S_TAG) continue;
    theta[0] = Store.child(h, 0);             // X
    theta[1] = Store.child(c1, 0);            // Y (inside s)
    theta[2] = Store.child(c2, 0);            // Z (inside s)
    return { consumed: { [h]: 1 }, theta, slots: this._slots };
  }
  return null;
};
```

### Insertion Point

The cleanest insertion is **per-rule** in the strategy layer. `tryMatch` API unchanged:

```javascript
// In match.js tryMatch (existing function):
function tryMatch(rule, state, calc, matchOpts) {
  if (rule.compiledMatcher) {
    const result = rule.compiledMatcher(state, calc);
    if (DEBUG_VERIFY) {
      const ref = genericTryMatch(rule, state, calc, matchOpts);
      assertEquivalent(result, ref);
    }
    return result;
  }
  return genericTryMatch(rule, state, calc, matchOpts);
}
```

The existing `tryMatch` body is renamed to `genericTryMatch` (no other changes). The compiled matcher returns the exact same shape: `{ rule, theta, slots, consumed, optimized }` or `null`.

### Files to Modify

| File | Change |
|---|---|
| `lib/engine/compile.js` | Add `generateMatcher(rule)` (~150 LOC). Call from `compileRule`. |
| `lib/engine/match.js` | Rename `tryMatch` → `genericTryMatch`. New `tryMatch` dispatches to compiled or generic. |
| `tests/engine/` | Add compiled matcher tests. Enable `DEBUG_VERIFY` in existing tests. |

**No other files change.** `strategy.js`, `forward.js`, `symexec.js` call `tryMatch` unchanged. No new modules, no new exports. The generator lives entirely inside `compile.js`.

### Correctness Verification

**Dual-run protocol:** Run both compiled and generic paths, assert identical results.

```javascript
// DEBUG_VERIFY=true in tests — always check both paths
// A single symexec run of the multisig tree exercises all compiled matchers
```

The generic `tryMatch` path is **never removed**. It stays as the reference implementation. Compiled matchers are an optimization layer that can be disabled without affecting correctness.

### What Makes a Rule "Hard to Compile"

These cases are excluded by eligibility and fall back to generic `tryMatch`:

| Case | Why hard | Fallback |
|---|---|---|
| Cross-pattern shared metavars with backtracking | `foo(X) * bar(X)` needs choice points across candidates | Generic `matchAllLinear` with undo log |
| oplus/with consequents | Multi-alt rules need solver integration | Generic `tryMatch` in symexec |
| Deferred patterns (persistent deps) | Pattern matching order depends on runtime binding | Generic `matchAllLinear` worklist |
| Nested non-flat patterns | Deep structural matching needs full `matchIdx` recursion | Generic path |

## Remaining Optimizations (Post Opt_G)

### Opt_C: Per-predicate persistent dispatch (~0.5ms)

Subsumed by G for compiled rules. Only matters for ineligible rules using generic path.

### Opt_E: Skip solver for non-oplus rules (~0.3ms)

Independent of G. Still worth doing as a 3-line conditional in `symexec.js`.

### Opt_H: Threaded code / fingerprint prediction (~1.7ms)

After applying a rule, the new `pc` value is known. This determines the next fingerprint and candidate rule. 670 predicted steps × ~2.5µs = ~1.7ms. Combines naturally with G: the compiled matcher for the predicted rule is called directly, skipping `findAllMatches` entirely.

## Performance Projection

| Level | Optimizations | Estimated time | vs original |
|---|---|---|---|
| Original (pre-0059) | — | 16.6ms | — |
| **After TODO_0059** | FactSet migration (measured) | **11.6ms** | **1.43×** |
| **After Opt_A** | FactSet snapshots (measured) | **~9.2ms** | **1.8×** |
| **After Opt_G** | Persistent step fast path (measured) | **~8.3ms** | **2.0×** |
| After Opt_E | Skip solver for non-oplus (−0.3ms) | ~8.0ms | 2.1× |
| After Opt_H | Threaded code (−1.7ms) | ~6.3ms | 2.6× |

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

**Key finding:** Matching and proving are only **14%** of findAllMatches time. The **86%** overhead is dispatch, FFI machinery, object allocation, and predicate guard checks. This is what Opt_G eliminates.

### FFI dispatch cost (micro-benchmarks)

| Operation | Via dispatch | Direct (inlined) | Speedup |
|---|---|---|---|
| inc(5, X) | 489ns | 54ns | 9× |
| plus(5, 6, X) | 399ns | 120ns | 3.3× |
| Full prove path (subApplyIdx + tryFFIDirect) | 478ns | 46ns | **10.4×** |

### V8 CPU Profile (top hotspots, pre-TODO_0059)

| Ticks | % | Function | Post-0059 |
|---|---|---|---|
| 138 | 5.8% | `KeyedLoadIC_Megamorphic` | **fixed** (Int32Array) |
| 89 | 3.7% | `matchIndexed` | still present |
| 56 | 2.4% | `FindOrderedHashMapEntry` | still present |
| 54 | 2.3% | `LoadIC` | reduced |
| 26 | 1.1% | `provePersistentGoals` | still present |
| 22 | 0.9% | `ForInFilter` | **fixed** (no for-in) |

### Structural findings

- **670/689 explored nodes are fully deterministic** (1 match, 1 alt).
- **Average matches per node: ~1.0** — the fingerprint layer is perfectly selective.
- **0 loli facts** in symbolic multisig state → drainPersistentLolis is no-op.
- **~17 matchIdx calls per node** — from matching ~5 linear patterns per rule.
- Persistent antecedents: inc (dominant), plus, mem_expand, neq, mem_read.

### Validated experiments (pre-TODO_0059)

| Experiment | Median | vs Baseline |
|---|---|---|
| Baseline (structuralMemo=true) | 13.57ms | — |
| Skip leaf snapshots | 11.40ms | −16% |
| Iterative deterministic chain + no snapshot | 11.41ms | −16% |

**Critical finding:** Converting 444 recursive DFS calls to an iterative loop produces **zero improvement**. V8 JIT makes recursion free. The cost is entirely per-step work.

## Key Insights

1. **The bottleneck is dispatch, not computation.** Matching (145ns/call) and FFI arithmetic (50-120ns) are fast. The 86% overhead is orchestration: dispatch, allocation, guard checks. Opt_G eliminates this.

2. **FFI dispatch is 10× more expensive than the computation.** `provePersistentGoals → subApplyIdx → tryFFIDirect → fn` adds 430ns around a 46ns computation.

3. **FFI-first for ground goals, state-lookup for symbolic.** Current code always does state lookup first. With ~10-30 persistent facts per predicate group, this O(n) scan is wasteful when FFI can answer in nanoseconds. Opt_G bakes this decision at compile time via slot dependency analysis.

4. **Compiled matchers specialize the interpreter, not the rules.** Same semantics, less dispatch. Generic `tryMatch` stays as reference. Dual-run verification catches divergence.

5. **Recursion is free.** V8 JIT makes DFS calls zero-cost. Iterative loops save nothing.

6. **Only 31 of 2125 nodes store snapshots.** Branch nodes have `state: null`. Terminal snapshots (leaf/cycle/memo/bound) are the only allocation. FactSet.snapshot (~250ns) is 600× cheaper than toObject (~150µs).

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
