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

**Current stack:** `fingerprintLayer` (O(1) for ground-discriminated rules) → `discTreeLayer` (O(depth) catch-all) → `predicateLayer` (safety net, never activates).

**Current bottleneck:** evenly distributed — no single dominant cost. 74 tryMatch calls for 63 nodes (strategy stack very effective). matchIndexed + substitute = 10%, state.linear access = ~20%, mutations/undo = ~15%, FFI = ~6%, DFS/alloc = ~10%, other overhead = ~40%.

## Key Learnings

1. **CALC's engine IS TREAT-like.** No beta memories, full re-evaluation from alpha memories (stateIndex). Correct for linear logic — Rete's cached partial matches are pure overhead when facts are consumed. See `doc/research/forward-chaining-networks.md`.

2. **CHR simpagation IS ILL forward rules.** Kept head = `!A`, removed head = linear, guard = FFI/backward proving. 25+ years of CHR compilation research applies. See `doc/research/forward-chaining-networks.md`.

3. **Strategy stack IS a manually compiled decision tree.** The fingerprint layer does what Maranget's algorithm would automate. The disc-tree layer generalizes to arbitrary patterns. Together they handle the full range from 44 to 400+ rules without manual tuning.

4. **Semi-naive for linear logic is fundamentally harder than Datalog.** Fact consumption invalidates matches — needs provenance tracking ≈ Rete beta network. Dirty predicate tracking (Stage 5a) would be the cheap approximation, but the disc-tree already prunes candidates by pattern structure, making 5a redundant for symexec. See `doc/research/incremental-matching.md`.

5. **V8 handles numeric-key objects efficiently.** Plain objects with ~178 numeric keys use V8's sparse array storage, NOT dictionary mode. Microbenchmark: object reads 1.85x faster, writes 5.3x faster, clone 8.6x faster than Map. Map only wins on iteration (5.25x). Don't convert to Map for the state representation.

6. **Disc-tree must filter by relevant predicates.** Naive implementation scans all state facts — 47% regression at 44 rules (178 facts, only 4 unclaimed rules). Fix: at build time collect which predicates appear in indexed rules, only scan those facts. Result: 0% regression. Lesson: catch-all layers must not do O(total_facts) work when they only have a few rules.

7. **Store.arity includes non-term children.** `atom('e')` has `arity=1` (string child) but 0 term children. Flatten functions must use `Store.isTermChild()` to filter, otherwise trie paths are wrong. This applies to any code that recursively walks Store terms.

8. **V8 string interning makes string-based tag comparison nearly as fast as numeric.** `Store.tag()` returns `TAG_NAMES[tags[id]]` — the same interned string object every time. String comparison `===` between interned strings is a pointer comparison. Adding `Store.tagId()` (raw numeric ID) and replacing `isVar()` with `slots[p] !== undefined` gives only ~2% improvement in V8. However, these changes eliminate string allocation in the hot path, which is essential for the Zig port.

9. **At 44 rules, the strategy stack reduces tryMatch calls to 74 for a 63-node tree (1.2×/node).** Only 18 failures out of 74 calls (76% success rate). The remaining failures are inherent: both JUMPI branches must be tried, and calldatasize has overlapping trigger predicates. No further candidate filtering improvement is possible at this scale.

## What's Next

All optimizations that matter at current scale (44 rules, ~20 facts, depth-2 terms) are done. The remaining items are tracked as TODOs, triggered by specific scaling scenarios:

| Optimization | Trigger | TODO |
|-------------|---------|------|
| Delta-driven activation | 100+ rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Compiled matching (Maranget) | 1000+ rules | [TODO_0037](../todo/0037_compiled-pattern-matching.md) |
| Semi-naive for linear logic | 100K+ facts | [TODO_0044](../todo/0044_semi-naive-linear-logic.md) |
| Join ordering | 4+ antecedent rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Path-based nested access | depth 4+ terms | [TODO_0022](../todo/0022_forward-optimization-research.md) |

## Profiling History

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
