# Hybrid Addressing for Forward Chaining Optimization

Optimizing forward chaining execution while keeping everything as plain linear logic. The engine detects patterns at compile time and applies transparent shortcuts at runtime.

## The Core Idea

Forward chaining rules like `f(X) * !plus(X, 2, X') -o f(X') * B()` preserve the predicate `f` — it appears on both sides of `-o` with a small change to its argument. The engine can detect this at compile time and, instead of full match + consume + substitute + produce, just navigate to the changed argument, apply the transform, and swap the hash.

The hybrid: **content-addressed values everywhere, path-based access for navigating to what changes.**

## Quantified: Where the Waste Is

Analysis of all 44 EVM rules (`evm.ill`):

| Category | Facts | % of LHS | Description |
|----------|-------|----------|-------------|
| **Preserved** | 60 | 27% | Same predicate, identical args both sides |
| **Delta** | 108 | 46% | Same predicate, arg(s) change. In-place update possible |
| **Consumed** | 50 | 21% | Left-only, truly removed |
| **Produced** | 27 | — | Right-only, truly new |

Delta by predicate: pc(35), sh(28), gas(24), stack(17), code(1), storage(1), others(2).

## Implementation Status

### Stage 1: Flat Array Store (done)

TypedArray SoA arena in `lib/kernel/store.js`. **Result:** 5.59ms → 3.47ms (38%).

### Stage 2: Preserved/Delta Detection (done)

`lib/prover/strategy/rule-analysis.js` — `analyzeRule` (v1: preserved) and `analyzeDeltas` (v2: delta detection). Wired into `compileRule()` as `rule.analysis`. 67 tests.

### Stage 3: Preserved Optimization (done)

`tryMatch`: preserved patterns reserved (not consumed), availability tracked via `reserved` counter. `applyMatch`/`mutateState`: preserved consequent patterns skipped. Both `forward.run` and `symexec.explore` optimized. **Result:** ~6-16% improvement. Cross-check tests verify identical results with `optimizePreserved: false`.

### Stage 3b: Delta Optimization (deferred — medium priority)

**Estimated speedup: ~7.5%** (320µs out of 4.25ms). Cost/benefit ratio is poor given the complexity.

**What it would do:** For delta patterns (same pred, different args), replace full unify + substitute with direct Store.child reads + Store.put. Saves ~140 match calls and ~140 subApply calls per symexec run.

**Does NOT break content-addressing:** `Store.put('pc', [newVal])` produces the same hash as substituting `pc _PC'` with theta. Dedup guarantees this.

**Complexities that need solving before implementation:**

1. **Variable flow:** Matching `pc _PC` binds `_PC` into theta. Downstream patterns like `code _PC OP` depend on this binding. Delta optimization must still bind variables — either via direct reads (extract args from matched fact) or a lightweight "bind-only" match. Requires distinguishing "bind-only delta" from "full match" in the worklist.

2. **Per-pattern role metadata:** Current `analyzeDeltas` returns aggregate lists. tryMatch needs to know the role of EACH antecedent pattern (preserved/delta/consumed). Need a pattern→role map in compiled rules.

3. **Multi-match identity:** When `stack` appears twice in antecedent (evm/add), one is delta and one is consumed. tryMatch processes them from a flat list — no way to know which is which. Need stable pairing between analysis results and antecedent pattern positions.

4. **Ordering guarantees:** The worklist defers patterns with unbound persistent deps. Replacing match() with direct reads changes when variables enter theta, potentially breaking ordering invariants.

5. **Additive choice:** If consequent has `A & B`, delta analysis was on the full consequent. Different alternatives may have different delta structure. Currently not an issue for EVM rules (no additive choice), but a correctness concern for general calculi.

**Recommendation:** Defer until the findAllMatches overhead (45% of total time) is addressed. That overhead dominates and is unaffected by delta optimization.

### Stage 4: Path-Based Nested Access (future)

For deeply nested types. O(K*D) vs O(N). Valuable when facts are merged into compound types.

## Profiling Snapshot (2026-02-14)

Symexec median: 2.3ms (was 5.59ms original).

findAllMatches breakdown (71.3% of total):
- **Overhead (loop, index, theta copy, FFI, deferred):** 63.4% of findAllMatches (1.92ms)
- **unify.match:** 28.3% (857µs, 605 calls, 1.4µs/call)
- **substitute:** 8.3% (250µs, 251 calls)

Other: mutateState 13.6%, makeChildCtx 8.1%, undo 5.2%.

**Next target:** The 1.92ms findAllMatches overhead — theta copying, candidate iteration, availability checks.

## References

- Baader & Nipkow (1998) — Term rewriting positions and paths
- Conchon & Filliatre (2006) — Type-safe modular hash-consing
- Sampson (2019) — Flattening ASTs (arena allocation)
