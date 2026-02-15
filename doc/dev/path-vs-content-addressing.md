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

### Stage 3b: Delta Optimization + Compiled Substitution (deferred — medium priority)

**Estimated speedup: ~5-8%** at current 0.95ms median (was ~7.5% at 4.25ms). Saves ~140 match calls and ~140 subApply calls per symexec run.

**Core idea:** For delta patterns (same pred, different args), replace full match + substitute with direct Store.child reads + Store.put. For rule consequents, compile the substitution to a direct Store.put chain at compile time.

**Content-addressing safety:** `Store.put('pc', [newVal])` produces the same hash as substituting `pc _PC'` with theta. Dedup guarantees this — provably correct.

**Two sub-optimizations that share prerequisites:**

**3b-i. Delta bypass (antecedent side):**
For a delta pattern like `pc _PC` where pc appears on both sides, instead of full `match(pattern, fact, theta)`, extract the child directly: `theta[pcSlot] = Store.child(fact, 0)`. This is a "bind-only" operation — no pattern decomposition needed.

**3b-ii. Compiled substitution (consequent side):**
For a consequent pattern like `pc _PC'`, instead of `applyFlat(pattern, theta)` which walks the tree and scans theta, compile to: `Store.put('pc', [theta[pcPrimeSlot]])`. Zero traversal, zero scan. This requires knowing which theta slot each metavar occupies (see Stage 6 below).

**Estimated LOC:** ~200 added, ~50 removed. Touches rule-analysis.js, forward.js, tryMatch.

**Dynamic rules consideration:** Rules loaded from .calc/.rules files are compiled once at load time. If rules change at runtime (e.g., new rules added dynamically), `compileRule()` must be called again. The delta/compiled paths would be part of compileRule output, so dynamic rule addition works — each call to compileRule independently precomputes its delta/compiled data. No global state to invalidate.

**Complexities that need resolving (research required before implementation):**

1. **Variable flow:** Matching `pc _PC` binds `_PC` into theta. Downstream patterns like `code _PC OP` depend on this binding. Delta bypass must still write bindings into theta — it just skips the full match machinery. With indexed slots (Stage 6), this is: `theta[slots._PC] = Store.child(fact, 0)`.

2. **Per-pattern role metadata:** Current `analyzeDeltas` returns aggregate lists. tryMatch needs to know the role of EACH antecedent pattern (preserved/delta/consumed). Need a `patternRoles` map: `{ [patternHash]: 'preserved' | 'delta' | 'consumed' }` with delta entries referencing their consequent counterpart.

3. **Multi-match identity:** When `stack` appears twice in antecedent (evm/add), one is delta and one is consumed. tryMatch processes them from a flat list. Solution: use position indices (pattern index in `antecedent.linear[]`) rather than pattern hashes as role keys. This makes pairing unambiguous.

4. **Ordering guarantees:** Deferred patterns change theta binding order. Delta bypass must NOT assume any particular binding order — it must work regardless of when the pattern is processed. With indexed slots (Stage 6), this is automatically safe: each metavar has a fixed slot, independent of processing order.

5. **Additive choice:** If consequent has `A & B`, delta analysis was on the full consequent. Different alternatives may have different delta structure. Solution: compute delta analysis per consequentAlt, not per rule. `consequentAlts` is already precomputed; extend each alt with its own delta metadata.

**Safety verification strategy:**
- Cross-check test: run every symexec with both optimized and unoptimized paths, assert identical trees
- Property: for every delta pattern, `Store.put(pred, [directRead]) === applyFlat(pattern, theta)`
- Fuzz: generate random states, verify delta+compiled produces same result as full match+substitute

**Dependency:** Stage 6 (indexed theta slots) should be implemented first — it resolves complexities 1 and 4.

### Stage 4: Path-Based Nested Access (future)

For deeply nested types. O(K*D) vs O(N). Valuable when facts are merged into compound types.

## Profiling Snapshot (2026-02-14, pre-Stage 5)

Symexec median: 2.3ms (was 5.59ms original). 63 nodes, 7 leaves, depth 38.

### V8 Profile Breakdown (node --prof, 500 runs)

Top ticks (945 total, 48% unaccounted):

| Source | Ticks | % | Where |
|--------|-------|---|-------|
| Map ops (construct+get+set) | 53 | 5.6% | `substitute.apply` `new Map(theta)` + `linearMeta.get()` |
| match() | 27 | 2.9% | unify.js core |
| KeyedLoadIC_Megamorphic | 26 | 2.8% | `state.linear[h]`, `consumed[h]` in tryMatch |
| Array ops (push+grow+splice) | 23 | 2.4% | match theta, expandConsequentChoices |
| tryMatch self | 18 | 1.9% | forward.js loop overhead |
| computeHash | 13 | 1.4% | Store.put via FFI (inc, plus) + substitute |
| ForInFilter | 9 | 1.0% | `for...in` in mutateState/undoMutate |
| undoIndexChanges | 7 | 0.7% | symexec DFS undo |

### Allocation Pressure (pre-Stage 5)

~4,737 allocations per run (63-node tree):

| Source | Count | % | What |
|--------|-------|---|------|
| match() | 1815 | 38% | theta copies + [var,val] pairs + goal stack |
| tryMatch | 1512 | 32% | consumed/reserved/preservedCount objects + theta spreads |
| substitute.apply | 1004 | 21% | `new Map(theta)` + newChildren arrays |
| explore | 406 | 9% | undo logs, indexUndo, snapshots |

GC spikes: 2% of runs >2x median (3.4ms max vs 1.2ms median).

After Stage 5: ~70% of these allocations eliminated (flat theta, flat worklist, arity-specialized substitute). GC spikes reduced to <5% tail variance.

### Stage 5: Allocation Reduction (done)

Implemented in multiple passes. See `doc/documentation/symexec-optimizations.md` and `doc/documentation/buffer-limits.md`.

**What was done (cumulative):**
- linearMeta as plain object (not Map) — eliminates Map.get overhead
- Reusable _workPatterns buffer — eliminates [...antecedent.linear] copy
- Theta truncate-on-failure — eliminates [...theta] copy per match attempt
- FFI theta push loop — eliminates spread allocation
- indexRemove swap-with-last — O(1) removal
- Flat interleaved theta [v,t,v,t,...] — eliminates ~1500 pair allocs/run
- Flat parallel worklist _Gp/_Gt — eliminates ~2000 pair allocs/run
- Arity-specialized applyFlat — eliminates newChildren[] for arity 0/1/2
- analyzeBufferLimits precomputes maxWorklist/maxTheta per rule
- expandConsequentChoices moved to compileRule (precomputed)

**Result:** P75 -6.6%, P90 -9.3%, tail -20%. Median ~0.95ms (100-run, 20 warmup).

**Remaining tech debt:** Two theta formats coexist (flat for hot path, paired for cold path). See Stage 5-cleanup below.

### Stage 5-cleanup: Unify theta format (todo — low priority)

Unify all theta consumers to flat interleaved `[v,t,v,t,...]` format. Currently the cold path (backward prover, sequent prover, FFI, tests) uses paired `[[v,t],...]`. The hot path uses flat. Conversion happens at 2 points in tryMatch.

**Risk of keeping two formats:** Silent data corruption if wrong format is passed to wrong consumer. `applyFlat` vs `apply` are separate functions which helps, but it's still a footgun.

**Estimated work:** ~40 mechanical edits across ~15 files (UnionFind.toTheta, all 14 FFI functions, prove.js, context.js, sequent.js, generic.js, ~20 test assertions). No algorithmic changes.

**When to do it:** Before any major architectural change (Zig port, new provers, TypeScript migration). Not blocking current optimization work.

### Stage 6: Indexed theta slots (todo — medium priority)

Replace the flat interleaved theta `[v,t,v,t,...]` with a fixed-size indexed array where each metavar has a pre-assigned slot. Substitution lookup becomes O(1) instead of O(n).

**Estimated speedup:** ~3-5% from eliminating theta linear scans in applyFlat (currently ~6-8 entries, scanned ~50 times per symexec run). More significant for rules with many metavars.

**Core design:**

```
// Compile time (compileRule):
metavarSlots = { [metavarHash]: slotIndex }  // e.g. {_PC: 0, _OP: 1, _PC': 2}
metavarCount = 3

// Runtime (tryMatch):
theta = new Array(metavarCount)  // fixed size, no push/scan
// In match: theta[metavarSlots[p]] = t   (O(1) write)
// In applyFlat: return theta[slotIdx]     (O(1) read)
```

**Why this is safe (and why raw position-based indexing is NOT):**

Theta positions in the current flat format are **not stable** — the deferral mechanism in tryMatch changes binding order. If pattern A is deferred because it depends on a persistent output var, pattern B matches first, and the positions flip. Same rule, different binding order depending on deferral.

Indexed slots avoid this entirely: each metavar gets a compile-time slot independent of match order. Whether A matches before or after B, `_X` always goes to slot 0.

**Implementation plan (~150 LOC added, ~30 removed):**

1. In `compileRule()`: collect all metavar hashes across antecedent + consequent patterns. Assign sequential slot indices. Store as `compiled.metavarSlots` (plain object) and `compiled.metavarCount` (number).

2. In `tryMatch()`: create `theta = new Array(rule.metavarCount)` instead of `theta = []`. Pass `rule.metavarSlots` alongside theta.

3. In `match()`: accept an optional `slots` parameter. When provided, use `theta[slots[p]] = t` instead of `theta.push(p, t)`. Binding check: `theta[slots[p]] !== undefined` instead of linear scan.

4. In `applyFlat()`: accept an optional `slots` parameter. When provided, use `const idx = slots[hash]; if (idx !== undefined) return theta[idx]` instead of linear scan.

5. FFI/backward prover boundary: when converting paired results to indexed theta, use `theta[slots[pair[0]]] = pair[1]`.

**Safety verification:**
- **Compile-time proof:** Every metavar that appears in any pattern gets a slot. `collectMetavars` already exists in rule-analysis.js. If a metavar appears at runtime that wasn't seen at compile time, the slot lookup returns `undefined` — same as "not bound" — so it fails gracefully (no silent corruption).
- **Determinism proof:** Slot assignments are derived from pattern structure (hash → index), which is immutable per compiled rule. No runtime state can change the mapping.
- **Cross-check test:** Run symexec with both flat-scan and indexed-slot implementations, assert identical trees. This catches any case where the slot mapping disagrees with the scan.
- **Assertion guard:** In debug mode, after match completes, verify that every non-undefined slot corresponds to the expected metavar: `assert(slots[metavarHash] === slotIndex)`.

**Dependency for Stage 3b:** Indexed slots resolve the "variable flow" and "ordering guarantees" complexities in Stage 3b. Should be implemented first.

**Dynamic rules:** Slot assignments are per-rule, computed in `compileRule()`. Adding new rules at runtime just calls `compileRule()` which independently assigns slots. No global state, no invalidation.

### Stage 7: Discrimination tree indexing (todo — low priority)

Replace predicate-head filtering with a discrimination tree (trie) for rule selection. Currently `findAllMatches` tries each candidate rule via `tryMatch` — the rule selection itself is fast (opcode layer gives O(1) for 40/44 EVM rules), but `tryMatch` is called for every candidate.

**Estimated speedup:** Small for 44 rules with the current opcode layer (~2-3%). Potentially significant (20-40%) for calculi with hundreds of rules or without the opcode shortcut.

**What it does:** Build a trie from all rule patterns. Each trie path corresponds to a term structure position. When a state fact changes, walk the trie with the fact to find all rules whose patterns match — O(depth) per fact instead of O(rules).

**Implementation complexity:** ~300 LOC. Well-studied technique (Vampire, E prover, Maude all use variants).

**Design outline:**

1. Build trie from first linear antecedent pattern of each rule (the "trigger" pattern):
   - Each trie node branches on: tag, arity, child[0] value, child[1] value, or "wildcard" (metavar)
   - Leaf nodes store the rule(s) that match this path
   - Wildcards match any term

2. On each forward step, walk the trie with each new/changed fact:
   - Start at root, descend through tag → arity → children
   - At wildcard branches, follow both wildcard and concrete paths
   - Collect all matching rules at leaves

3. Only call `tryMatch` for trie-selected rules (instead of all predicate-matched rules).

**Safety:**
- **Soundness:** Trie only eliminates rules that CANNOT match. If a fact doesn't match the trigger pattern's structure, the full match would also fail. No false negatives.
- **Completeness:** All rules with a matching trigger pattern are returned. Wildcards ensure no rules are missed.
- **Verification:** Cross-check test — run with and without trie, assert same set of matching rules.
- **Dynamic rules:** Trie must be rebuilt when rules change. Incremental trie insertion is straightforward (add a path). Deletion requires reference counting at leaf nodes.

**When to implement:** When the number of rules grows beyond ~100, or when targeting a new calculus without opcode-style indexing. For the current 44-rule EVM calculus, the opcode layer already provides O(1) selection for most rules.

**Risk:** Complexity. The current predicate-head indexing is ~20 lines. A discrimination tree would be ~300 lines with edge cases around wildcards, multi-pattern rules, and incremental updates. The opcode layer already covers the dominant case.

## Profiling Snapshot (2026-02-15)

Symexec median: 0.95ms (100-run, 20 warmup). Was 5.59ms original. 63 nodes, 7 leaves, depth 38.

Current bottleneck: `findAllMatches` → `tryMatch` → `match` + `applyFlat` dominate. GC pressure reduced by ~70% from Stage 5 flat formats.

## References

- Baader & Nipkow (1998) — Term rewriting positions and paths
- Conchon & Filliatre (2006) — Type-safe modular hash-consing
- Sampson (2019) — Flattening ASTs (arena allocation)
- Voronkov (2001) — Discrimination trees for term indexing
- Grabmayer et al. (2003) — Efficient matching modulo associativity/commutativity
