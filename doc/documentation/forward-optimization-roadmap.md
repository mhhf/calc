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

8. **V8 string interning makes string-based tag comparison nearly as fast as numeric.** `Store.tag()` returns `TAG_NAMES[tags[id]]` — the same interned string object every time. String comparison `===` between interned strings is a pointer comparison. Adding `Store.tagId()` (raw numeric ID) and replacing `isMetavar()` with `slots[p] !== undefined` gives only ~2% improvement in V8. However, these changes eliminate string allocation in the hot path, which is essential for the Zig port.

9. **At 44 rules, the strategy stack reduces tryMatch calls to 74 for a 63-node tree (1.2×/node).** Only 18 failures out of 74 calls (76% success rate). The remaining failures are inherent: both JUMPI branches must be tried, and calldatasize has overlapping trigger predicates. No further candidate filtering improvement is possible at this scale.

10. **Structural memoization via control hash is cheap and effective for symmetric programs.** The EVM multisig checks 6 members with identical post-check logic. A hash of just `(PC, SH)` — O(1), two lookups — detects isomorphic subtrees and skips 5 of 6 member bodies. Savings: 2125→477 nodes, 49ms→11ms. Exact state memoization can't match because evars have unique hashes from a global counter; predicate histogram hashing can't match because `code` fact counts differ between member bodies (741, 739, ..., 733). The minimal control hash works precisely because it captures execution position without caring about concrete values.

11. **hevm's compactness is representation, not branching.** hevm and calc have identical branching: 30 branch points, 31 leaves, same 5 behavioral outcomes × 6 members. hevm's 61 total nodes vs calc's 477 (memo) / 2125 (no memo) reflects representation granularity: hevm collapses 50+ deterministic opcodes between JUMPIs into single ITE nodes with symbolic expressions; calc makes each opcode an explicit tree node. calc with structural memo is 2.4× faster (22ms vs 52ms) because memo skips 5 of 6 isomorphic member subtrees, something hevm does not do. Verified with hevm v0.54.2 `--show-tree` on MultisigNoCall.sol. See `doc/documentation/calc-vs-hevm.md`.

## What's Next

Per-step optimizations (stages 1-11) are done at current scale. The next wave targets tree-level optimizations (structural memo, constraint solving, branch pruning) and scaling triggers:

| Optimization | Trigger | TODO |
|-------------|---------|------|
| Disc-tree query caching | Any DFS tree with repeated control states | See note below |
| Configurable control predicates | Non-EVM programs with symmetric structure | See note below |
| Constraint propagation (equality + FFI re-check) | Symbolic evar chains (3+ deep) | [TODO_0005](../todo/0005_symexec-simplification.md) |
| Persistent proving order (FFI before state) | Mixed FFI + state predicates | See note below |
| Delta-driven activation | 100+ rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| Compiled matching (Maranget) | 1000+ rules | [TODO_0037](../todo/0037_compiled-pattern-matching.md) |
| Semi-naive for linear logic | 100K+ facts | [TODO_0044](../todo/0044_semi-naive-linear-logic.md) |
| Join ordering | 4+ antecedent rules | [TODO_0035](../todo/0035_forward-chaining-networks.md) |
| DPOR (Partial Order Reduction) | Forward-vs-forward commuting matches | [TODO_0054](../todo/0054_commuting-match-reduction.md) |
| Path-based nested access | depth 4+ terms | [TODO_0022](../todo/0022_forward-optimization-research.md) |
| Memoized mem_read cache (L1) | W > 50 writes per MLOAD | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |
| Per-term read cache (L2) | 50+ branches sharing memory prefixes | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |
| Indexed persistent predicates | 50+ persistent facts per predicate | [TODO_0052](../todo/0052_memory-and-persistent-caching.md) |

### Disc-tree query caching

**Problem**: `findAllMatches()` calls the disc-tree's `getCandidateRules(state)` on every single node in the DFS tree. This is expensive — it flattens every fact into a trie path, queries the discrimination tree, deduplicates results, and verifies trigger predicates. Profiling shows this is 69% of explore time, and 88% of that is overhead (traversal, dedup, filtering), not actual pattern matching.

**Insight**: which rules *can* fire depends on what predicates are present, not on the specific values inside those predicates. Two states at the same program counter with the same stack height have exactly the same set of candidate rules — the disc-tree would return the same list both times.

**Example** — a simple program that checks 3 members:

```
State A: pc=10, sh=3, stack=[alice, bob, carol]
State B: pc=10, sh=3, stack=[dave, eve, frank]
```

Both states have: `pc` fact, `bytecode` fact, `stack` facts at heights 0-2, `sh` fact. The disc-tree query walks all these facts and returns the same candidate rules (say, `evm/add`, `evm/push1`, `evm/jumpi`). Today we do this walk twice. With caching, the second call is a hash-map lookup.

**How it works**:

```
                       explore() DFS tree
                            |
                     node (pc=0, sh=0)
                    /                  \
            node (pc=5, sh=2)    node (pc=5, sh=2)   ← same control state!
               /        \          /        \
          (pc=10,sh=3) (pc=8,sh=1) ...      ...
```

1. Compute a "control hash" from the predicates that determine rule eligibility: `hash(pc_value, sh_value)`.
2. Before calling `getCandidateRules(state)`, check a cache: `controlHash → candidateRules[]`.
3. On cache hit, skip the disc-tree entirely. On miss, run the query and cache the result.

**Why this is sound**: candidate rules depend on *which predicates exist* and *what ground discriminator values they contain* (e.g., opcode at PC). Two states with the same PC have the same opcode (bytecode is immutable), so the fingerprint + disc-tree produce the same candidate list. The actual *matching* (tryMatch) still runs per-node with the real state — only the candidate *filtering* is cached.

**Expected impact**: In the symbolic multisig (477 nodes with memo, 84 without), there are ~15-20 unique (PC, SH) pairs but 84 nodes. Caching eliminates ~75% of disc-tree queries. At 2.93ms for findAllMatches, this could save ~1.5-2ms (targeting ~1ms explore).

**Implementation**: ~20 LOC in `symexec.js`. A `Map<bigint, Rule[]>` cleared per `explore()` call. The control hash already exists (`computeControlHash`). Main risk: if non-control predicates affect candidacy (e.g., a rule triggered by a predicate that appears/disappears mid-execution). Mitigation: only cache when all trigger predicates are "stable" (present throughout execution, like `bytecode`).

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

Per-node cost is 1.36× higher in symbolic vs concrete due to: more oplus alternatives explored per branch, constraint solver overhead (checkpoint/restore), and persistent goal failures on evars. The 2.3× total slowdown (11ms vs 4ms) comes primarily from 1.7× more nodes (477 vs 280), not per-node cost.

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
