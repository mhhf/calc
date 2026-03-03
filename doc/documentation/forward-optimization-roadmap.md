# Forward Chaining Optimization Roadmap

## Architecture

Forward chaining: rules `A * B * !C -o { D * E }` consume linear facts, produce new ones. Persistent facts (`!C`) proved via backward chaining / FFI. Execution proceeds until quiescence.

Key files: `forward.js` (engine), `symexec.js` (tree exploration), `rule-analysis.js` (compile-time analysis), `disc-tree.js` (discrimination tree indexing), `unify.js` (matching), `substitute.js` (substitution), `store.js` (content-addressed terms).

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

## What's Next

Per-step and tree-level optimizations are mature. The profile is flat — no single dominant cost. Remaining gains come from reducing per-node overhead across all components, or from scaling triggers for larger programs.

### Closing the gap (5.0ms → 4ms target)

| Optimization | Saves | Effort | Notes |
|---|---|---|---|
| Inline predicted step (skip tryMatch) | ~0.5-1.0ms | Medium | See below |

#### Disproven (empirically tested, no measurable gain)

| Optimization | Expected | Actual | Why |
|---|---|---|---|
| Pooled match results | ~0.3-0.5ms | 0ms (noise) | ~1245 tiny allocs cost <25µs total; pool cleanup overhead offsets |
| Precomputed consequent tagIds | ~0.1-0.2ms | 0ms (noise) | `Store.tagId()` = `tags[h]` single array lookup, ~5ns; extra branches cost more |

Tested on feature branch `opt/pool-and-precompute-tagids` with 3×200 interleaved samples. Baseline trimmed median: 5.02ms. Optimized: 5.14ms (+2.2%, within stdev 0.7-0.9ms). The profile is flat — V8 already optimizes these allocation patterns via nursery GC and inline caches. Per-operation micro-optimizations at this scale cannot produce measurable gains.

### Scaling triggers (larger programs)

| Optimization | Trigger | TODO |
|-------------|---------|------|
| Configurable control predicates | Non-EVM programs with symmetric structure | See note below |
| Constraint propagation (equality + FFI re-check) | Symbolic evar chains (3+ deep) | [TODO_0005](../todo/0005_symexec-simplification.md) |
| Delta-driven activation | 100+ rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Compiled matching (Maranget) | 1000+ rules | [TODO_0037](../todo/0037_compiled-pattern-matching.md) |
| Semi-naive for linear logic | 100K+ facts | [TODO_0044](../todo/0044_semi-naive-linear-logic.md) |
| Join ordering | 4+ antecedent rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| DPOR (Partial Order Reduction) | Forward-vs-forward commuting matches | [TODO_0054](../todo/0054_commuting-match-reduction.md) |
| Path-based nested access | depth 4+ terms | [TODO_0022](../todo/0022_forward-optimization-research.md) |
| Memoized mem_read cache (L1) | W > 50 writes per MLOAD | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |
| Per-term read cache (L2) | 50+ branches sharing memory prefixes | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |
| Indexed persistent predicates | 50+ persistent facts per predicate | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |

### Inline predicted step (skip tryMatch entirely)

For predicted nodes, we know the rule and the new PC value. The full tryMatch machinery (pool clear → theta fill → matchAllLinear → persistent proving → existential resolution → copy) is overkill. A compiled "step function" per rule could:

1. Look up the 2-3 linear facts by tag (O(1) group access)
2. Extract bindings via delta bypass (direct child extraction, no unification)
3. Prove persistent goals via compiled FFI steps (already exist as `persistentSteps`)
4. Write consumed/produced facts directly into state (no intermediate objects)

This merges tryMatch + mutateState into a single compiled step, eliminating both the match result allocation and the separate mutation pass. For 415 predicted calls at ~6.6µs combined (tryMatch + mutateState), even a 30% reduction saves ~0.8ms.

Risk: high implementation complexity. Each rule has different antecedent/consequent shapes. Would need a per-rule compiled closure or a bytecode interpreter. The V8 megamorphic lesson (RES_0069: 59 closures → 25% regression) applies — must stay within IC threshold or use a single polymorphic dispatch.

### ~~Disc-tree query caching~~ (obsolete)

Originally proposed when findAllMatches was called on every node (69% of explore time). With fingerprint prediction (stage 16), findAllMatches is called on only 53/477 nodes (11%). The disc-tree is no longer the bottleneck. Caching those 53 calls would save <0.3ms — not worth the complexity.

### Configurable control predicates

Stage 14 implements structural memoization for EVM using a hardcoded `computeControlHash(stateIndex)` that hashes `(pc, sh)`. This works because PC and SH determine the EVM execution point — states with the same PC+SH produce isomorphic subtrees when branching depends only on symbolic values.

The concept generalizes: any program with symmetric structure (checking against a list, dispatch tables, loop unrolling) can benefit. But each domain needs different "control predicates." The fix is to let programs declare them:

```
@control pc sh.
```

The engine reads the annotation and auto-computes the control hash from those predicates. Programs without `@control` get no structural memo (no overhead). Implementation: ~30 LOC in `symexec.js` (read annotation, generalize `computeControlHash` to iterate over declared predicates) + grammar support for `@control` annotation.

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
