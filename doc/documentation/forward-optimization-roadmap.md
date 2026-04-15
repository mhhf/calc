# Forward Chaining Optimization Roadmap

## Architecture

Forward chaining: rules `A * B * !C -o { D * E }` consume linear facts, produce new ones. Persistent facts (`!C`) proved via backward chaining / FFI. Execution proceeds until quiescence.

Key files: `forward.js` (engine), `explore.js` (tree exploration), `rule-analysis.js` (compile-time analysis), `disc-tree.js` (discrimination tree indexing), `unify.js` (matching), `substitute.js` (substitution), `store.js` (content-addressed terms).

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
| 12 | Tensor-in-oplus encoding + EqNeqSolver (TODO_0055) | Enables branch pruning for symbolic values |
| 13 | Single-survivor oplus collapsing (TODO_0055) | Eliminates fork nodes when solver prunes one alt |
| 14 | Structural memoization via (PC, SH) control hash | 49ms → 11ms (4.4×) for symbolic multisig |
| 15 | Arrlit bytecode representation | ~10ms → ~5.3ms (data representation, not per-step) |
| 16 | Fingerprint prediction (Opt_H) | Skips findAllMatches for 87% of nodes (~3% improvement) |

**Current stack:** `fingerprintLayer` (O(1) for ground-discriminated rules) → `discTreeLayer` (O(depth) catch-all) → `predicateLayer` (safety net, never activates). Fingerprint prediction skips the strategy stack entirely for predicted nodes.

**Current bottleneck (solc_symbolic, 477 nodes, 5.3ms median, 11.1µs/node):**

| Component | Est. time | % | Per-node | Notes |
|---|---|---|---|---|
| tryMatch | ~1.8ms | 34% | ~3.8µs × 468 | 415 prediction hits + 53 findAllMatches |
| mutateState | ~1.3ms | 24% | ~2.8µs × 456 | consume + produce + tagId lookups |
| other/overhead | ~1.2ms | 23% | | DFS frames, alloc, Set/Map ops |
| undo | ~0.28ms | 5% | | Arena restore |
| hashing | ~0.27ms | 5% | | stateHash + controlHash |
| solver | ~0.17ms | 3% | | EqNeq checkpoint/restore |
| drain+predict+snap | ~0.3ms | 6% | | Loli drain, prediction lookup, leaf snapshots |

No single component dominates. Target: 4ms (8.4µs/node).

## Key Learnings

1. **CALC's engine IS TREAT-like.** No beta memories, full re-evaluation from alpha memories (stateIndex). Correct for linear logic — Rete's cached partial matches are pure overhead when facts are consumed. See `doc/research/forward-chaining-networks.md`.

2. **CHR simpagation IS ILL forward rules.** Kept head = `!A`, removed head = linear, guard = FFI/backward proving. 25+ years of CHR compilation research applies. See `doc/research/forward-chaining-networks.md`.

3. **Strategy stack IS a manually compiled decision tree.** The fingerprint layer does what Maranget's algorithm would automate. The disc-tree layer generalizes to arbitrary patterns. Together they handle the full range from 44 to 400+ rules without manual tuning.

4. **Semi-naive for linear logic is fundamentally harder than Datalog.** Fact consumption invalidates matches — needs provenance tracking ≈ Rete beta network. Dirty predicate tracking (Stage 5a) would be the cheap approximation, but the disc-tree already prunes candidates by pattern structure, making 5a redundant for symexec. See `doc/research/incremental-matching.md`.

5. **V8 handles numeric-key objects efficiently.** Plain objects with ~178 numeric keys use V8's sparse array storage, NOT dictionary mode. Microbenchmark: object reads 1.85x faster, writes 5.3x faster, clone 8.6x faster than Map. Map only wins on iteration (5.25x). Don't convert to Map for the state representation.

6. **Disc-tree must filter by relevant predicates.** Naive implementation scans all state facts — 47% regression at 44 rules (178 facts, only 4 unclaimed rules). Fix: at build time collect which predicates appear in indexed rules, only scan those facts. Result: 0% regression. Lesson: catch-all layers must not do O(total_facts) work when they only have a few rules.

7. **Store.arity includes non-term children.** `atom('e')` has `arity=1` (string child) but 0 term children. Flatten functions must use `Store.isTermChild()` to filter, otherwise trie paths are wrong. This applies to any code that recursively walks Store terms.

8. **V8 string interning makes string-based tag comparison nearly as fast as numeric.** `Store.tag()` returns `TAG_NAMES[tags[id]]` — the same interned string object every time. String comparison `===` between interned strings is a pointer comparison. Adding `Store.tagId()` (raw numeric ID) and replacing `isMetavar()` with `slots[p] !== undefined` gives only ~2% improvement in V8. However, these changes eliminate string allocation in the hot path, which is essential for the Zig port.

9. **At 44 rules, the strategy stack reduces tryMatch calls to 74 for a 63-node tree (1.2×/node).** Only 18 failures out of 74 calls (76% success rate). The remaining failures are inherent: both JUMPI branches must be tried, and calldatasize has overlapping trigger predicates. No further candidate filtering improvement is possible at this scale.

10. **Structural memoization via control hash is cheap and effective for symmetric programs.** The EVM multisig checks 6 members with identical post-check logic. A hash of just `(PC, SH)` — O(1), two lookups — detects isomorphic subtrees and skips 5 of 6 member bodies. Savings: 2125→477 nodes, 49ms→11ms. Exact state memoization can't match because evars have unique hashes from a global counter; predicate histogram hashing can't match because `code` fact counts differ between member bodies (741, 739, ..., 733). The minimal control hash works precisely because it captures execution position without caring about concrete values.

11. **Micro-allocation optimizations are invisible at ~5ms/477-node scale.** Pooling match result objects (skip `theta.slice()` + `consumed` copy, ~1245 allocs/explore) and precomputing `Store.tagId()` for consequent patterns (skip one array lookup per produce) were tested empirically: 0% improvement, 3×200 interleaved samples. V8's nursery GC handles short-lived <100-byte objects at ~10-20ns each. The total allocation cost is <25µs — unmeasurable against 5ms total. Adding pool-management branches actually trends slower (+2.2%). **Lesson: when the profile is flat and per-node cost is ~10µs, individual operation savings under ~50ns/call × ~500 calls = <25µs are permanently below the noise floor.**

12. **hevm's compactness is representation, not branching.** hevm and calc have identical branching: 30 branch points, 31 leaves, same 5 behavioral outcomes × 6 members. hevm's 61 total nodes vs calc's 477 (memo) / 2125 (no memo) reflects representation granularity: hevm collapses 50+ deterministic opcodes between JUMPIs into single ITE nodes with symbolic expressions; calc makes each opcode an explicit tree node. calc with structural memo is 2.4× faster (22ms vs 52ms) because memo skips 5 of 6 isomorphic member subtrees, something hevm does not do. Verified with hevm v0.54.2 `--show-tree` on MultisigNoCall.sol. See `doc/documentation/calc-vs-hevm.md`.

13. **Fusing pipeline stages doesn't help when the irreducible work dominates.** The inline predicted step proposal (merge tryMatch + mutateState into one pass) was analyzed and rejected. The eliminable overhead — intermediate `consumed` object, `theta.slice()`, `for..in` coercion — totals ~0.3ms for 415 calls. But FactSet binary search, Zobrist updates, FFI calls, and `Store.put` are identical regardless of fusion. The savings are the same class as lesson #11 (micro-allocations). Meanwhile, fusion duplicates ~100-150 LOC across match.js and state-ops.js, violating the clean `strategy → matching → mutation` separation. **Lesson: when the profile is flat, collapsing abstraction boundaries for constant-factor savings trades architectural clarity for unmeasurable gain.**

## What's Next

Per-step and tree-level optimizations are mature. The profile is flat — no single dominant cost. Remaining gains come from reducing per-node overhead across all components, or from scaling triggers for larger programs.

### Closing the gap (5.0ms → 4ms target)

The profile is flat — no single component dominates. The remaining gap is "death by a thousand cuts" that incremental JS-level optimization likely cannot close. The Zig port (estimated 5-8×, dominated by BigInt → u256 elimination) is the realistic path to sub-1ms explore.

#### Disproven (empirically tested or analytically rejected)

| Optimization | Expected | Actual | Why |
|---|---|---|---|
| Pooled match results | ~0.3-0.5ms | 0ms (noise) | ~1245 tiny allocs cost <25µs total; pool cleanup overhead offsets |
| Precomputed consequent tagIds | ~0.1-0.2ms | 0ms (noise) | `Store.tagId()` = `tags[h]` single array lookup, ~5ns; extra branches cost more |
| Inline predicted step | ~0.5-1.0ms | ~0.3ms (est.) | Fuses tryMatch+mutateState; actual savings are intermediate allocs (~consumed object, theta.slice), not the irreducible matching/mutation work. Damages clean tryMatch→mutateState separation of concerns for marginal gain. See analysis below. |

Pooled match results and precomputed tagIds tested on feature branch `opt/pool-and-precompute-tagids` with 3×200 interleaved samples. Baseline trimmed median: 5.02ms. Optimized: 5.14ms (+2.2%, within stdev 0.7-0.9ms). The profile is flat — V8 already optimizes these allocation patterns via nursery GC and inline caches. Per-operation micro-optimizations at this scale cannot produce measurable gains.

### Scaling triggers (larger programs)

| Optimization | Trigger | TODO |
|-------------|---------|------|
| Configurable control predicates | Non-EVM programs with symmetric structure | See note below |
| Constraint propagation (equality + FFI re-check) | Symbolic evar chains (3+ deep) | TODO_0005 |
| Delta-driven activation | 100+ rules | TODO_0035 |
| Compiled matching (Maranget) | 1000+ rules | TODO_0037 |
| Semi-naive for linear logic | 100K+ facts | TODO_0044 |
| Join ordering | 4+ antecedent rules | TODO_0035 |
| DPOR (Partial Order Reduction) | Forward-vs-forward commuting matches | TODO_0054 |
| Path-based nested access | depth 4+ terms | TODO_0022 |
| Memoized mem_read cache (L1) | W > 50 writes per MLOAD | TODO_0052 |
| Per-term read cache (L2) | 50+ branches sharing memory prefixes | TODO_0052 |
| Indexed persistent predicates | 50+ persistent facts per predicate | TODO_0052 |

### ~~Inline predicted step~~ (rejected — marginal gain, damages architecture)

For predicted nodes, we know the rule and the new PC value. The idea was to merge tryMatch + mutateState into a single compiled step, eliminating intermediate allocations.

**What it would save:** The `consumed` object copy (~150ns), `theta.slice()` (~150ns), `for..in + Number()` coercion in consumeLinear (~300ns), Map clear/setup (~40ns). Total: ~0.3ms for 415 predicted calls.

**What it would NOT save:** The irreducible work dominates — FactSet binary search + Zobrist updates in consume/produce, FFI calls for persistent proving, `matchIdx` unification, `Store.put` for compiled substitution. These costs are identical whether tryMatch and mutateState are separate or fused.

**Why rejected:**

1. **Marginal gain.** Estimated ~0.3ms (5.6% of 5.3ms), same class of micro-allocation savings that lesson #11 proved unmeasurable for pooling. Needs empirical validation that may well show noise.

2. **Damages separation of concerns.** The current `strategy → match.js (tryMatch) → state-ops.js (mutateState)` pipeline cleanly separates indexing, matching+proving, and state mutation. Fusing them creates ~100-150 LOC of duplicated logic. Any future change to matching, FactSet operations, preserved optimization, or persistent proving must be mirrored in two places.

3. **Megamorphic constraint.** Per-rule closures are out (RES_0069: 59 closures → 25% regression). The only safe approach is a single defunctionalized function reading `rule` data fields — which ends up doing the same work as the separate functions, just in one pass.

4. **EVM-only.** Prediction requires a fingerprint predicate + bytecode array. Non-EVM programs get zero benefit.

5. **Fails the suckless test.** High complexity, low payoff, poor generality, damages a clean architecture.

### ~~Disc-tree query caching~~ (obsolete)

Originally proposed when findAllMatches was called on every node (69% of explore time). With fingerprint prediction (stage 16), findAllMatches is called on only 53/477 nodes (11%). The disc-tree is no longer the bottleneck. Caching those 53 calls would save <0.3ms — not worth the complexity.

### Configurable control predicates

Stage 14 implements structural memoization for EVM using a hardcoded `controlHash(stateIndex)` that hashes `(pc, sh)`. This works because PC and SH determine the EVM execution point — states with the same PC+SH produce isomorphic subtrees when branching depends only on symbolic values.

The concept generalizes: any program with symmetric structure (checking against a list, dispatch tables, loop unrolling) can benefit. But each domain needs different "control predicates." The fix is to let programs declare them:

```
@control pc sh.
```

The engine reads the annotation and auto-computes the control hash from those predicates. Programs without `@control` get no structural memo (no overhead). Implementation: ~30 LOC in `explore.js` (read annotation, generalize `controlHash` to iterate over declared predicates) + grammar support for `@control` annotation.

**Soundness condition:** the declared control predicates must fully determine the subtree branching structure. Branching on concrete values excluded from the hash would cause unsound memoization. For EVM, this holds because all oplus branching is on symbolic evars/freevars, not on concrete member-specific values like `bitPos`.

### Persistent proving order

Current order: state lookup → FFI → clause resolution. Reversing to FFI → state → clauses yields ~2.5% improvement on the EVM benchmark (n=100, p=0.012) because all 153 persistent goals per tree are FFI-resolvable (inc, plus, neq) — the state lookup always misses.

However, FFI-first is only optimal when all persistent predicates are FFI-backed. Programs with user-defined persistent facts (e.g. lookup tables, memoization) would benefit from state-first order, since state lookup is O(1) via the predicate set guard vs backward proving overhead. The right long-term answer may be per-predicate dispatch: at compile time classify each persistent predicate as FFI-only, state-only, or mixed, and generate the appropriate proving order. For now, keeping state-first as the default is the more general choice.

## Profiling History

### Hand-crafted bytecode (63 nodes, concrete)

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

### Real solc bytecode (MultisigNoCall, 1040 bytes)

| Setup | Nodes | Median | Per-node | Notes |
|-------|-------|--------|----------|-------|
| Concrete (MEMBER1, nonce=0) | 280 | ~4ms | ~14μs | All oplus branches collapse (0 forks) |
| Symbolic sender + nonce, no memo | 2125 | ~49ms | ~23μs | 31 leaves, 10 oplus forks |
| Symbolic sender + nonce, memo | 477 | ~11ms | ~28μs | 9 memo hits, 2 real leaves |
| Symbolic, memo + arrlit + prediction | 477 | ~5.3ms | ~11μs | Stages 15-16 |

Per-node cost is 1.36× higher in symbolic vs concrete due to: more oplus alternatives explored per branch, constraint solver overhead (checkpoint/restore), and persistent goal failures on evars. The arrlit representation change (stage 15) halved absolute cost from ~11ms to ~5.3ms by changing how bytecode is stored. Prediction (stage 16) skips findAllMatches for 87% of nodes but only saves ~3% because the per-call cost is small (~2µs).

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
