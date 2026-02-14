# Hybrid Addressing for Forward Chaining Optimization

Optimizing forward chaining execution while keeping everything as plain linear logic. The engine detects patterns at compile time and applies transparent shortcuts at runtime.

## The Core Idea

Forward chaining rules like `f(X) * !plus(X, 2, X') -o f(X') * B()` preserve the predicate `f` — it appears on both sides of `-o` with a small change to its argument. The engine can detect this at compile time and, instead of full match + consume + substitute + produce, just navigate to the changed argument, apply the transform, and swap the hash.

For deeply nested types like `a(b(c(X), d(...)), e(f(Y, g(...))))` where a rule changes X and Y but preserves the structure — paths `[0,0,0]` and `[1,0,0]` identify the changed positions. Only nodes along those paths need new hashes (incremental Merkle update). Everything else keeps its content-addressed hash.

The hybrid: **content-addressed values everywhere, path-based access for navigating to what changes.**

## Quantified: Where the Waste Is

Analysis of all 44 EVM rules (`evm.ill`):

| Category | Facts | % of LHS | Description |
|----------|-------|----------|-------------|
| **Preserved** | 57 | 27% | Same predicate, identical args both sides |
| **Delta** | 97 | 46% | Same predicate, arg(s) change. In-place update possible |
| **Consumed** | 56 | 27% | Left-only, truly removed |
| **Produced** | 32 | — | Right-only, truly new |

**73.4% of all antecedent patterns** (154 of 210) could be optimized away or reduced to cheap field access.

Top preserved predicates:
- `code PC (opcode)` — **42 of 44 rules**. Every step consumes+reproduces the SAME bytecode fact.
- `address`, `sender`, `callvalue`, `timestamp`, `gaslimit`, `calldatasize` — environment singletons, read-only lookups disguised as consume+produce.

Top delta predicates:
- `pc` — 38 rules. arg0: PC → PC' (via `!inc` or jump target)
- `sh` — 34 rules. arg0: unwrap `s()` constructor (functionally `-1`)
- `gas` — 19 rules. arg0: GAS → GAS' (via `!inc` or `!plus`)

## Three Optimization Levels

All three are transparent — rules don't change, the engine just gets smarter.

### Level 1: Preserved Predicate Optimization

At compile time, detect predicates that appear identically on both sides of `-o`.

**IMPORTANT: Preserved predicates still need matching/unification.** We must verify the fact exists in state with the correct values and bind variables for use by other patterns. What we skip is the consume/reproduce/index-update cycle.

Two sub-cases:
1. **All vars already bound** (by non-preserved patterns): verification-only — "does state contain this fully-ground fact?" → O(1) index check. Skip consume/produce/index-update.
2. **Some vars not yet bound**: must match to bind variables, but still skip consume/produce/index-update.

Currently:
```
1. match(code_pattern, candidate)     — Store.get × 3-5
2. consume code fact from state       — delete from multiset
3. subApply(code_pattern, theta)      — Store.get × 3-5, Store.put
4. produce code fact into state       — insert into multiset
5. update index (remove + add)        — 2 index ops
```

With preserved detection:
```
1. match(code_pattern, candidate)     — still needed for variable binding
(steps 2-5 eliminated — fact stays in state unchanged)
```

**Saving per rule:** 2 multiset ops + 2 index ops + ~5 Store.get/put (substitute) per preserved predicate. With 1.3 preserved facts per rule average, significant savings on steps 2-5 but match cost remains.

**Note:** For `code PC OPCODE` specifically, the opcodeLayer strategy already handles the existence verification via `codeByPC` index. The remaining saving is eliminating the consume/reproduce cycle.

### Level 2: Delta Application

At compile time, compare antecedent and consequent patterns for same-predicate facts. Extract which arguments change and what transforms them.

Example — rule `evm/add` has `pc PC` → `pc PC'` where `!inc PC PC'`:
```
Delta: pc.arg0 changes via inc
```

Currently:
```
1. match pc pattern against state     — Store.get, unify
2. consume pc fact                    — delete from multiset
3. subApply(pc(PC'), theta)           — Store.get, Store.put
4. produce new pc fact                — insert into multiset
```

With delta:
```
1. find pc fact in state              — O(1) index lookup
2. read arg0 (current PC value)      — Store.child (flat store: 4ns)
3. apply inc                          — FFI, O(1)
4. create pc(PC')                     — Store.put('pc', [newPC])
5. swap in state: old hash → new hash — O(1)
```

Steps 1-5 are all O(1). No full pattern matching, no unification, no full substitution.

**Open question: can we skip full theta for delta predicates?** When a delta's transform (e.g. `!inc`) is an FFI with known mode (input+, output-), we can compute the output directly without building a substitution. This eliminates the need for a full theta — we read the input from state, apply the FFI, and produce the output. This is what `tryFFIDirect()` already does for persistent patterns. Further research needed to formalize when this is safe.

**`sh` as delta:** The `sh` predicate appears to be a structural change (`s(s(SH)) → s(SH)`) but is functionally `-1` — it unwraps one `s()` constructor. As a delta: `arg0 → Store.child(arg0, 0)`, which is O(1). The match still verifies the precondition (stack height ≥ N required by the opcode).

### Level 3: Path-Based Access for Nested Types

For deeply nested linear terms where a rule preserves the outer structure but changes values at specific paths.

Given a term `a(b(c(X), d(Y)), e(Z))` and a rule that changes X→X' and Z→Z':

**Paths (precomputed at compile time):**
- `[0, 0, 0]` — navigates a→b→c→X
- `[1, 0]` — navigates a→e→Z

**Incremental update (runtime):**
```
1. Navigate path [0,0,0]: read X     — 3 array lookups (flat store: 12ns)
2. Compute X' = transform(X)         — FFI / arithmetic
3. Navigate path [1,0]: read Z       — 2 array lookups (8ns)
4. Compute Z' = transform(Z)         — FFI / arithmetic
5. Rebuild bottom-up along changed paths:
   new_c = put('c', [X'])            — reuse d(Y) unchanged
   new_b = put('b', [new_c, d_hash]) — reuse d's hash
   new_e = put('e', [Z'])
   new_a = put('a', [new_b, new_e])
```

Only 4 `Store.put` calls instead of walking+rebuilding the entire term. Unchanged subtrees (d, Y, g) keep their content-addressed hashes — zero work.

For term size N with K changes at depth D: O(K×D) vs O(N).

## Flat Array Store: The Foundation

All three optimization levels benefit from replacing `Map<hash, {tag, children}>` with TypedArray arena.

```javascript
// Current: ~25ns per access
const node = Store.get(hash);  // Map.get
const tag = node.tag;           // string comparison

// Flat store: ~4ns per access
const tag = tags[id];            // Uint8Array[index]
const c0 = child0[id];          // Uint32Array[index]
```

**7-12x faster reads.** Content-addressing preserved via dedup Map on `put()` (cold path only). Tag comparison becomes integer `===`. String interning makes all children homogeneous uint32.

See `doc/research/flat-array-store.md` for full design.

## How Delta Extraction Works

At compile time, for each forward rule:

```
For each linear predicate P in antecedent:
  If P also in consequent with same predicate head and arity:
    Compare argument patterns pairwise:
      For position i:
        If ante.args[i] ≡ cons.args[i] (same metavar):
          → invariant at position i
        If ante.args[i] is metavar V and cons.args[i] is metavar V':
          Look for persistent fact linking V to V' (e.g. !inc V V'):
          → delta: position i, transform = inc
        If both have same tag but differ in subtrees:
          → recurse: compute sub-deltas with paths
        Else:
          → full recomputation at position i

    Classification:
      All positions invariant → PRESERVED (match for vars, skip consume/produce)
      Some positions have deltas → DELTA (in-place update)
      Structure changes (different arity/tag) → FULL (regular match)
```

Output per rule:
```javascript
{
  preserved: ['code'],              // match only, skip consume/produce
  deltas: [
    { pred: 'pc', position: 0, transform: 'inc', via: '!inc PC PC\'' },
    { pred: 'sh', position: 0, structural: 'unwrap_s' },
    { pred: 'gas', position: 0, transform: 'plus', args: ['(o(i e))'] },
  ],
  consumed: ['stack'],              // full match needed
  produced: ['stack'],              // full substitute needed
}
```

This metadata is stored alongside compiled rules — zero overhead at runtime.

## Staged Implementation Plan

**Process for EVERY stage:**
1. Clean git (no uncommitted changes)
2. All tests pass (523 tests)
3. Benchmark BEFORE implementing (baseline measurement)
4. Implement the change
5. Verify all tests still pass
6. Benchmark AFTER (measure improvement)
7. Assess code complexity change
8. Commit with clear message
9. Wait for approval before next stage

**Benchmark note:** Separate precomputation time (constant, amortized) from execution time (scales with input). We optimize for execution.

### Stage 1: Flat Array Store

Replace `lib/kernel/store.js` internals with TypedArray SoA arena.

**Sub-phases (to minimize risk):**
- **1a:** Add tag enum, string interning, BigInt side table internally. Keep `Store.get()` returning `{tag, children}` wrapper for backward compat. All callers unchanged.
- **1b:** Migrate hot-path callers (unify.js `match()`, forward.js `tryMatch()`) from `Store.get(h).tag` → `Store.tag(h)` / `Store.child(h, i)` patterns for direct TypedArray access.
- **1c:** Swap internal storage from `Map` to TypedArray SoA. `Store.get()` still works (allocates wrapper, cold-path only).

**What changes:**
- `Store.put()` returns sequential index instead of hash
- Internal storage: `Map<hash, {tag, children}>` → TypedArray SoA + dedup Map
- Tag comparison: string `===` → integer `===`
- String interning for atom/variable names
- BigInt side table for `binlit` values
- Content-address dedup Map on `put()` only (cold path)

**What doesn't change:**
- `a === b` equality still works (same content → same index via dedup)
- Hashes as object keys in state (`state.linear[hash]`) still works — just numbers
- Hashes in Maps/Sets still works — sequential indices are still numbers
- `Store.isTermChild(c)` still returns `typeof c === 'number'` — `getChild()` returns mixed types (number for term refs, string for string children) via bitmask dispatch
- No changes to rule format, prover, or engine logic

**Scope:** ~280 LOC (new store internals + hot-path accessor migration)
**Benefit:** 7-12x faster Store reads (hot path only; cold path keeps wrapper allocation)
**Risk:** Low. Sequential index is a drop-in for hash. Content-addressing preserved via dedup.

**Migration concerns identified from code audit:**
- 41 `Store.get()` → `node.tag`/`node.children` sites need assessment (hot vs cold path)
- `node.children.map()` / `node.children.length` patterns need arity accessor
- `node.children.some()` in occurs check needs iteration accessor
- `Store.clear()` must reset: arena + dedup Map + string table + bigint table
- Arena growth: pre-allocate generous initial size (8192 terms), resize if needed
- `childTypes` bitmask needed for string/BigInt/term child discrimination

### Stage 2: Preserved/Delta Detection (compile-time analysis)

Add analysis pass in `compileRule()` (forward.js) or a new module.

**What changes:**
- Each compiled rule gets `preserved: [...]`, `deltas: [...]`, metadata
- Analysis compares antecedent vs consequent patterns
- Classification: preserved (match-only), delta (in-place update), full (unchanged)
- No execution changes yet — just metadata generation

**What doesn't change:**
- Execution still uses full match/consume/produce
- Rules unchanged
- No API changes

**Scope:** ~150 LOC analysis code
**Benefit:** None yet (just metadata). Validates the approach — can inspect which rules have what optimizations.
**Risk:** Very low. Pure addition.

### Stage 3: Optimized Execution (preserved skip + delta apply)

Modify `tryMatch` and `applyMatch` to use the metadata from Stage 2.

**What changes:**
- `tryMatch`: for preserved predicates with all vars bound, verify existence only. For preserved with unbound vars, match normally but mark as non-consumed. For delta predicates, read+transform+swap.
- `applyMatch`: skip consume/produce for preserved. Apply deltas for delta predicates. Full substitute for unclassified.
- Fallback to full match/substitute for non-optimizable predicates.

**What doesn't change:**
- Rules unchanged
- Exploration tree unchanged
- Cycle detection, depth bounds, choice expansion unchanged
- General prover (backward chaining, manual proving) unchanged

**Scope:** ~200 LOC modifications to forward.js hot path
**Benefit:** ~2-5x on forward chaining (73% of antecedent patterns optimized). Combined with Stage 1: ~15-30x total.
**Risk:** Medium. Must ensure correctness — the optimized path must produce identical state as the full path. Test by running both and comparing.

### Stage 4: Path-Based Nested Access (future)

For rules with deeply nested preserved types, precompute paths to changed leaves and use incremental Merkle update.

**Prerequisite:** Rules must actually USE deeply nested types. Current EVM rules use flat predicates (depth 1-2). This stage becomes valuable when:
- EVM facts are merged into one `evm(...)` type, or
- Other calculi use deeply nested linear types

**Scope:** ~300 LOC
**Benefit:** O(K×D) instead of O(N) per preserved nested term.
**Risk:** Low (additive optimization).

## Complexity Summary

| Stage | Code Change | Performance Impact | Risk |
|-------|-----------|-------------------|------|
| 1: Flat store | ~280 LOC (new store + migrations) | 7-12x on Store reads | Low |
| 2: Detection | ~150 LOC (analysis pass) | None (metadata only) | Very low |
| 3: Optimized exec | ~200 LOC (hot path mods) | 2-5x on forward chaining | Medium |
| 4: Nested paths | ~300 LOC (path navigation) | O(K×D) vs O(N) per nested term | Low |

**Cumulative estimate:**
- After Stage 1: ~0.5ms (from 3.1ms)
- After Stage 3: ~0.1-0.2ms
- After Stage 4 (with merged types): ~0.05-0.1ms

## Code Audit: Store Migration Impact

From audit of all 14 files with Store API call sites:

**Store.get() call patterns (grouped by migration urgency):**

| Category | Files | Pattern | Migration |
|----------|-------|---------|-----------|
| **Hot path** | unify.js, forward.js, symexec.js | `Store.get(h)` in match/tryMatch loop | Must convert to tag/child accessors |
| **Cold path** | convert.js, prove.js, builders.js | `Store.get(h)` for parsing/rendering/indexing | Can keep wrapper `Store.get()` |
| **One-time** | rules2-parser.js, calculus/index.js | `Store.get(h)` during load/compile | Irrelevant for perf |

**Hash-as-key patterns (no migration needed — works with sequential indices):**
- `state.linear[hash] = count` — object keys: numbers auto-convert to strings, `Number(h)` converts back ✓
- `Map.set(hash, value)` in UnionFind, substitution — Map works with any number ✓
- `Set.add(hash)` in pathVisited, freevars — Set works with any number ✓
- `consumed[hash] = count` — same as state.linear ✓

**Potential issues identified:**
1. `Store.clear()` — must reset 5 data structures (arena, dedup, string table, bigint table, nextId)
2. Arena growth — TypedArray resize requires creating new array + copying. Generous initial allocation (8192) avoids this for all current use cases
3. `node.children.map()` pattern — 12 call sites; need `Store.mapChildren(h, fn)` or inline loops
4. `node.children.length` — 8 call sites; need `Store.arity(h)` accessor
5. `node.children.some()` — 3 call sites (occurs check); need `Store.someChild(h, fn)` or inline
6. Renderer receives `{tag, children}` objects AND hashes — already handles both (line 236-239 of builders.js)

## Relation to Content vs Path Addressing

The original question: should CALC use path-addressed trees instead of content-addressed trees?

**Answer:** Both, at different levels.

- **Content-addressed:** All values (symbolic expressions, binary numbers, formulas). Essential for O(1) equality, structural sharing, multiset keys. This does NOT change.
- **Path-addressed:** Access patterns within preserved terms. The engine knows WHERE in a term to read/write, without searching. Paths are precomputed at compile time from rule structure.

This IS the hybrid. Content-addressing answers "WHAT is this value?" Path-addressing answers "WHERE in this term do I find the value that changes?"

The incremental Merkle update along changed paths is exactly where the original intuition ("hash changes propagate from leaf to root") is correct and useful — within a single preserved term, updating a leaf DOES require rehashing up to the root, and doing it incrementally (only the changed path) is cheaper than rebuilding everything.

## Open Research Questions

1. **Full theta elimination for deltas:** When all delta transforms are FFI with known modes, can we skip building a substitution entirely? The delta reads inputs directly from state, applies FFI, and writes outputs. No theta needed. This could eliminate the match+unify overhead for the 46% of patterns classified as deltas.

2. **sh/stack representation:** Currently Peano-encoded (`s(s(SH))`). A native uint32 representation would make delta arithmetic trivial (-1/+1) but changes the matching semantics. Trade-off: simpler deltas vs. breaking the pure linear logic representation.

3. **When are preserved predicates truly free?** If ALL variables in a preserved pattern are already bound by non-preserved patterns (which is true for `code PC OPCODE` when `pc PC` is also matched), the preserved match reduces to an existence check. Can we statically determine this at compile time and eliminate the match entirely?

## References

- Baader & Nipkow (1998) — Term rewriting positions and paths
- Stickel (1989) — Path indexing for theorem provers
- Conchon & Filliâtre (2006) — Type-safe modular hash-consing
- Sampson (2019) — Flattening ASTs (arena allocation)
- BitECS — SoA TypedArray architecture for JS
- See also: `doc/research/flat-array-store.md`, `doc/research/path-addressed-trees.md`
