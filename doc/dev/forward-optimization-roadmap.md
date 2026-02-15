# Forward Chaining Optimization Roadmap

Optimizing forward chaining execution while keeping everything as plain linear logic. All optimizations are transparent compile-time shortcuts — the logic frontend is unchanged.

## Architecture

Forward chaining: rules of the form `A * B * !C -o { D * E }` consume linear facts and produce new ones. Persistent facts (`!C`) are proved via backward chaining / FFI. Execution proceeds until quiescence.

Key files: `forward.js` (engine), `symexec.js` (tree exploration), `rule-analysis.js` (compile-time analysis), `unify.js` (pattern matching), `substitute.js` (substitution), `store.js` (content-addressed terms).

## EVM Rule Profile (baseline)

44 forward rules in `evm.ill`. Per rule: 2-6 linear antecedents, 0-3 persistent antecedents, 2-6 consequent patterns.

| Category | Facts | % of LHS | Description |
|----------|-------|----------|-------------|
| **Preserved** | 60 | 27% | Same pattern hash both sides — skip consume/produce |
| **Delta** | 108 | 46% | Same predicate, different args — in-place update |
| **Consumed** | 50 | 21% | Left-only, truly removed |
| **Produced** | 27 | — | Right-only, truly new |

Delta by predicate: pc(35), sh(28), gas(24), stack(17), code(1), storage(1), others(2).

## Dependency Graph

```
DONE                           TODO
────                           ────
Stage 1 (flat store)
  │
Stage 2 (preserved/delta detection)
  │
Stage 3 (preserved optimization)
  │
Stage 4 (allocation reduction)
  │
  ├──────────────────── Stage 5 (theta unification)     [standalone, low]
  │
  ├──────────────────── Stage 6 (de Bruijn theta)       [standalone, medium]
  │                       │
  │                     Stage 7 (delta + compiled sub)   [depends on 6, medium]
  │
  ├──────────────────── Stage 8 (path-based access)     [standalone, future]
  │
  └──────────────────── Stage 9 (discrimination trees)  [standalone, future]
```

All future stages are independent of each other except Stage 7 → Stage 6. Each can be implemented and tested in isolation with cross-check tests.

## Implementation Order

1. **Stage 6** — De Bruijn indexed theta. Enables Stage 7. Moderate effort (~150 LOC).
2. **Stage 7** — Delta optimization + compiled substitution. Depends on Stage 6. Moderate effort (~200 LOC).
3. **Stage 5** — Theta format unification. Tech debt cleanup. Low effort (~40 edits).
4. **Stage 9** — Discrimination tree indexing. When rules exceed ~100. High effort (~300 LOC).
5. **Stage 8** — Path-based nested access. When terms become deeply nested. Future.

## Scale Considerations

Current: 44 rules, ~20 linear facts, depth-2 terms, 6-8 metavars per rule.

| Scenario | Rules | Facts | Term depth | Bottleneck | Stage needed |
|----------|-------|-------|------------|------------|-------------|
| Current EVM | 44 | ~20 | 2 | tryMatch | 6, 7 |
| Large EVM | 400 | ~50 | 2 | rule selection | 9 |
| Multi-calculus | 1000 | ~200 | 2-4 | rule selection + match | 9 |
| Symbolic exec | 44 | 100000 | 2 | state indexing | (custom) |
| Nested types | 44 | ~20 | 10+ | match + substitute | 8 |
| Full scale | 1000 | 100000 | 10+ | everything | 6-9 |

---

## Stage 1: Flat Array Store (done)

TypedArray SoA arena in `lib/kernel/store.js`. Terms are sequential uint32 indices. Content-addressing via dedup Map on `put()`.

**Result:** 5.59ms → 3.47ms (38%).

**Zig mapping:** Direct. SoA layout → Zig `MultiArrayList` or manual struct-of-slices. Dedup map → `std.HashMap`. String interning → `std.StringHashMap`. BigInt side table → `ArrayList(u256)` or similar.

---

## Stage 2: Preserved/Delta Detection (done)

`rule-analysis.js` — `analyzeRule()` (preserved) and `analyzeDeltas()` (delta detection). Compile-time analysis stored on `rule.analysis`. 67 tests.

**Safety:** Pure static analysis of pattern hashes. No runtime behavior change. Provably correct: if `hash(ante_pattern) === hash(conseq_pattern)`, content-addressing guarantees structural identity.

---

## Stage 3: Preserved Optimization (done)

`tryMatch`: preserved patterns reserved (not consumed). `applyMatch`/`mutateState`: preserved consequent patterns skipped.

**Result:** ~6-16% improvement. Cross-check tests verify identical results with `optimizePreserved: false`.

**Safety:** Cross-check test runs every symexec with both paths, asserts identical trees. If the optimization produces a different result, the test fails.

---

## Stage 4: Allocation Reduction (done)

Eliminates ~70% of GC-prone allocations on the hot path. Multiple sub-optimizations:

- `linearMeta` as plain object (not Map)
- Reusable `_workPatterns` buffer
- Theta truncate-on-failure (no `[...theta]` copy per match attempt)
- FFI theta push loop (no spread)
- `indexRemove` swap-with-last — O(1)
- Flat interleaved theta `[v,t,v,t,...]` — eliminates ~1500 pair allocs/run
- Flat parallel worklist `_Gp[]`/`_Gt[]` — eliminates ~2000 pair allocs/run
- Arity-specialized `applyFlat` — eliminates `newChildren[]` for arity 0/1/2
- `analyzeBufferLimits` precomputes maxWorklist/maxTheta per rule
- `expandConsequentChoices` moved to `compileRule` (precomputed)

**Result:** P75 −6.6%, P90 −9.3%, tail −20%. Median 0.95ms (100-run, 20 warmup).

**Remaining tech debt:** Two theta formats coexist — flat `[v,t,v,t,...]` for hot path, paired `[[v,t],...]` for cold path. See Stage 5.

**Non-reentrancy invariant:** The flat worklist `_Gp`/`_Gt` is module-level shared state. `match()` must never be called from within another `match()` call. This is safe because: (1) `match()` is iterative, (2) it only calls Store reads and `Store.put`, (3) the backward prover uses `unify()` (separate path), (4) forward chaining is single-threaded. A warning comment in `unify.js` documents this invariant.

See `doc/documentation/buffer-limits.md` for details.

---

## Stage 5: Theta Format Unification (todo — low priority)

**Status:** Tech debt. Not blocking any optimization.

**Problem:** Two theta formats coexist. Hot path uses flat `[v,t,v,t,...]` (`applyFlat` in substitute.js, `match` in unify.js, `tryMatch` in forward.js). Cold path uses paired `[[v,t],...]` (`apply` in substitute.js, `unifyUF` in unify.js, backward prover, sequent prover, FFI functions, tests). Conversion at 2 points in `tryMatch`.

**Risk:** Silent data corruption if wrong format passed to wrong consumer. Mitigated by separate function names (`apply` vs `applyFlat`), but still a footgun.

**Implementation:** ~40 mechanical edits across ~15 files:
- `UnionFind.toTheta()` → produce flat format
- All 14 FFI functions in `lib/engine/ffi/` → return flat format
- `prove.js` backward prover → return flat format
- `context.js`, `sequent.js`, `generic.js` → consume flat format
- ~20 test assertions → update `theta.length` checks (1 binding = 2 entries)

**Safety proof:** Purely mechanical transformation. Each edit changes `theta.push([v, t])` to `theta.push(v, t)` and `theta[i][0]`/`theta[i][1]` to `theta[i]`/`theta[i+1]` with step-by-2 loops. No algorithmic change. Test suite catches any mismatched format.

**Performance:** Near-zero improvement at current scale. Cold paths are called tens of times per run (vs thousands for hot paths). But eliminates conversion overhead at tryMatch boundaries and removes format confusion risk.

**When to do:** Before Zig port, TypeScript migration, or new prover implementation.

**Zig relevance:** In Zig both formats would be `[]const Binding` or `[]const u32` — format unification makes the port simpler.

**At scale (100000 facts):** Still near-zero — cold path frequency doesn't scale with fact count.

---

## Stage 6: De Bruijn Indexed Theta (todo — medium priority)

**Status:** Design complete. Prerequisite for Stage 7.

### Core Idea

Replace the flat interleaved theta scan with O(1) indexed lookup. This is the term-rewriting analogue of **de Bruijn indices**: each metavariable in a rule gets a compile-time slot index, and theta becomes a fixed-size indexed array rather than a scan-searched list.

In lambda calculus, de Bruijn indices replace variable names with positional indices relative to their binder, eliminating alpha-equivalence issues. Here we do the same for pattern matching: each metavar `_X` in a rule gets a fixed slot number, eliminating dependence on match ordering.

### Why Position-Based Indexing Is Unsafe

Theta positions in the current flat format are **not stable**. The deferral mechanism in `tryMatch` changes binding order: if pattern A is deferred because it depends on a persistent output var, pattern B matches first, and `_X` ends up at a different position.

De Bruijn slots avoid this: `_X` always goes to slot `N` regardless of which pattern matches first. The slot assignment is a compile-time invariant, not a runtime artifact.

### Design

```javascript
// Compile time (compileRule):
metavarSlots = { [metavarHash]: slotIndex }  // e.g. {_PC: 0, _OP: 1, _PC': 2}
metavarCount = 3

// Runtime (tryMatch):
theta = new Array(metavarCount)    // fixed-size, filled with undefined
theta[slots[_PC]] = value          // O(1) write
result = theta[slots[_PC']]        // O(1) read
```

### Implementation (~150 LOC added, ~30 removed)

1. **`compileRule()`**: Collect all metavar hashes across antecedent + consequent patterns using existing `collectMetavars()` in rule-analysis.js. Assign sequential slot indices. Store as `compiled.metavarSlots` (plain object) and `compiled.metavarCount` (number).

2. **`tryMatch()`**: Create `theta = new Array(rule.metavarCount)` instead of `theta = []`. Pass `rule.metavarSlots` to `match()` and `applyFlat()`.

3. **`match()`**: Accept optional `slots` parameter. When provided:
   - Binding write: `theta[slots[p]] = t` instead of `theta.push(p, t)`
   - Binding check: `theta[slots[p]] !== undefined` instead of linear scan
   - Consistent binding: `theta[slots[p]] === t` instead of scan + compare

4. **`applyFlat()`**: Accept optional `slots` parameter. When provided:
   - Lookup: `const idx = slots[hash]; if (idx !== undefined) return theta[idx]`
   - Replaces: `for (let i = 0; i < theta.length; i += 2) { if (theta[i] === hash) ... }`

5. **FFI/backward prover boundary**: Convert paired results to indexed:
   `theta[slots[pair[0]]] = pair[1]` instead of `theta.push(pair[0], pair[1])`

### Safety Proof

**Completeness:** Every metavar that appears in any pattern of a rule gets a slot. `collectMetavars` walks all antecedent + consequent patterns. If a metavar appears at runtime that wasn't seen at compile time, `slots[p]` returns `undefined`, and `theta[undefined]` is harmless — same as "not bound". No silent corruption.

**Determinism:** Slot assignments are derived from pattern structure (hash → index), which is immutable per compiled rule. No runtime state affects the mapping.

**Idempotence:** Each metavar has exactly one slot. Multiple bindings of the same metavar write to the same slot — consistent binding check is automatic (`theta[slot] !== undefined && theta[slot] !== t` → fail).

**Cross-check test:** Run symexec with both flat-scan and indexed-slot implementations, assert identical trees.

### Performance

**Current scale (44 rules, 6-8 metavars):** ~3-5% from eliminating linear scans. Each `applyFlat` call scans 6-8 theta entries ~50 times per symexec run. Indexed lookup: O(1) per variable.

**At scale (1000 rules, 20+ metavars):** More significant. Linear scan of 20 entries × thousands of calls per run = measurable overhead. Indexed: still O(1).

**Memory:** `new Array(N)` for N ≤ 20 is negligible. No GC pressure (fixed-size, reusable).

### Complications

1. **match() API change:** Adding `slots` parameter to `match()` changes its signature. Cold-path callers (without slots) must still work. Solution: `slots` is optional, default behavior unchanged.

2. **FFI format bridge:** FFI returns paired `[[v,t],...]`. With indexed theta, conversion is `theta[slots[v]] = t` per pair. Same complexity, different format.

3. **Dynamic rules:** Slot assignments are per-rule, computed in `compileRule()`. New rules at runtime just call `compileRule()` independently. No global state.

### Zig Mapping

Slots map → `[MAX_METAVARS]?u32` (fixed-size array of optional indices). Theta → `[MAX_METAVARS]?u32` (fixed-size array of optional term indices). Both are stack-allocated, zero-allocation. Hash-to-slot at compile time → Zig `comptime` block or lookup table.

### Theoretical Background

De Bruijn indices (N.G. de Bruijn, 1972) replace named variables with positional indices in lambda calculus. The key insight — separating variable identity from binding position — applies equally to pattern matching substitutions. Our indexed slots are a "named de Bruijn" scheme: we keep variable names for debugging/display but use positional indices for all runtime operations.

Related: Explicit substitution calculi (Abadi et al. 1991), which make substitution a first-class operation with indexed variables. Our compiled substitution (Stage 7) is an instance of this.

---

## Stage 7: Delta Optimization + Compiled Substitution (todo — medium priority)

**Status:** Design complete. Depends on Stage 6.

### Core Idea

For delta patterns (same predicate, different args on both sides of `-o`), replace full match + substitute with direct Store operations:

- **Antecedent (delta bypass):** Instead of `match(pattern, fact, theta)`, extract changed args directly: `theta[slots._PC] = Store.child(fact, 0)`. Bind-only, no decomposition.
- **Consequent (compiled substitution):** Instead of `applyFlat(pattern, theta)`, compile to: `Store.put('pc', [theta[slots._PC']])`. Zero traversal, zero scan.

### Why This Works

Content-addressing guarantees: `Store.put('pc', [newVal])` produces the **same hash** as `applyFlat(pc_pattern, theta)`. Both create a node with tag 'pc' and children `[newVal]`. Dedup ensures identity. This is provably correct by the hash-consing invariant.

### Estimated Speedup

~5-8% at 0.95ms median. Saves ~140 match calls (delta patterns) and ~140 applyFlat calls (delta consequents) per symexec run. At 400 rules with proportionally more deltas: ~10-15%.

### Implementation (~200 LOC added, ~50 removed)

**7a. Per-pattern role metadata:**

Extend `analyzeDeltas()` to produce per-pattern roles, keyed by **position index** (not pattern hash, because the same predicate can appear twice — e.g., `stack` in evm/add):

```javascript
// In compileRule(), after analyzeDeltas():
compiled.patternRoles = [];  // indexed by position in antecedent.linear[]
for (let i = 0; i < linearPats.length; i++) {
  const role = classifyPattern(i, analysis);
  compiled.patternRoles[i] = role;
  // role = { type: 'preserved' } | { type: 'delta', conseqIdx, changedPositions } | { type: 'consumed' }
}
```

**7b. Delta bypass in tryMatch:**

```javascript
if (role.type === 'delta') {
  // Bind changed args directly instead of full match
  for (const pos of role.changedPositions) {
    theta[slots[metavarAtPos(pattern, pos)]] = Store.child(fact, pos);
  }
  // Still "consume" the fact (it will be "produced" with new args)
  consumed[fact] = (consumed[fact] || 0) + 1;
  continue;
}
```

**7c. Compiled substitution in applyMatch:**

```javascript
// Precomputed in compileRule():
compiled.compiledConseq = consequent.linear.map(pattern => {
  const tag = Store.tag(pattern);
  const arity = Store.arity(pattern);
  const childSources = [];  // for each child: { type: 'slot', idx } | { type: 'literal', hash }
  for (let i = 0; i < arity; i++) {
    const c = Store.child(pattern, i);
    if (isMetavar(c)) childSources.push({ type: 'slot', idx: slots[c] });
    else childSources.push({ type: 'literal', hash: c });
  }
  return { tag, arity, childSources };
});

// Runtime: instead of applyFlat(pattern, theta):
const { tag, childSources } = compiled.compiledConseq[i];
const children = childSources.map(s => s.type === 'slot' ? theta[s.idx] : s.hash);
return Store.put(tag, children);
```

### Complications and Solutions

1. **Variable flow:** Matching `pc _PC` binds `_PC` into theta. Downstream patterns like `code _PC OP` depend on this binding. Delta bypass must still write bindings. **Solution:** With de Bruijn slots (Stage 6), `theta[slots._PC] = Store.child(fact, 0)` — always writes to the correct slot regardless of processing order.

2. **Multi-match identity:** When `stack` appears twice in antecedent (evm/add), one is delta and one is consumed. **Solution:** Use position indices, not pattern hashes, as role keys. Position is unambiguous.

3. **Ordering guarantees:** Deferral changes match order. **Solution:** De Bruijn slots (Stage 6) make theta writes order-independent. Each metavar has a fixed slot.

4. **Additive choice (`A & B`):** Different consequent alternatives may have different delta structure. **Solution:** Compute delta analysis per `consequentAlt`, not per rule. `consequentAlts` is already precomputed.

5. **Nested delta patterns:** If a delta pattern has arity > 1 with nested metavars (e.g., `f(g(_X, _Y), _Z)`), direct `Store.child` extraction only works for flat patterns. **Solution:** For nested patterns, fall back to full match. Delta bypass is a fast path, not a replacement. The `changedPositions` analysis already identifies which positions change.

### Safety Proof

**Correctness:** For any delta pattern, `Store.put(pred, [Store.child(fact, 0)])` produces the same hash as `applyFlat(pred_pattern, theta)` where theta binds the metavar to `Store.child(fact, 0)`. This follows from hash-consing: same tag + same children → same hash. QED.

**Completeness:** Delta bypass only applies to patterns classified as delta by compile-time analysis. All other patterns use the full match path. The fallback is always available.

**Cross-check test:** Run every symexec with both optimized and unoptimized paths, assert identical trees. Property test: for every delta pattern, `Store.put(pred, [directRead]) === applyFlat(pattern, theta)`.

### Performance at Scale

At 400 EVM rules: proportionally more delta patterns (~400+ delta bypasses per run). Each bypass saves a `match()` call (~5-10 Store reads) and a `applyFlat()` call (~3-5 Store reads + traversal). Estimated: ~10-15% improvement.

At 100000 facts: delta bypass doesn't depend on fact count (it's per-rule, not per-fact). Same improvement ratio.

### Zig Mapping

Compiled consequent → `comptime` array of `ChildSource` unions. Delta bypass → inline `store.child()` + `store.put()`. No closures, no dynamic dispatch. The compiled substitution compiles naturally to Zig's comptime evaluation.

---

## Stage 8: Path-Based Nested Access (future)

**Status:** Design only. Independent of other stages. Not needed at current scale.

### Core Idea

For deeply nested term types, navigate directly to the changed argument via a position path instead of full tree traversal. O(K×D) where K = changed positions, D = depth, vs O(N) for full traversal where N = total term size.

### When This Matters

Current EVM terms are flat (arity 1-2, depth 1-2). If future calculi use compound types like `state(pc(V), stack(S), gas(G), mem(M))`, a single delta update touches one leaf in a depth-4 tree. Full traversal walks all 8+ nodes; path-based access walks 4 (root → state → pc → V).

**At depth 10+ with branching factor 2:** Full traversal = ~1000 nodes. Path-based = 10 nodes. 100x speedup on the substitution step.

### Design Sketch

```javascript
// Compile time: for each delta, compute path from root to changed position
// path = [childIdx, childIdx, ...] from root to leaf
compiled.deltaPaths = deltas.map(d => ({
  path: computePath(d.anteHash, d.changedPositions),
  // For consequent: same path, but leaf is different metavar
}));

// Runtime: navigate path, extract/replace leaf
function navigatePath(hash, path) {
  let h = hash;
  for (const idx of path) h = Store.child(h, idx);
  return h;
}
```

### Safety

Path-based access reads the same content-addressed values as full traversal — it just skips irrelevant subtrees. If the path is wrong (bug), `Store.child` returns a wrong value, and the cross-check test catches it.

**Invariant:** A path is valid iff it was derived from the pattern structure at compile time, and the runtime term has the same structure (guaranteed by pattern matching success).

### Complications

1. **Variable-structure terms:** If the term structure varies (e.g., lists of different lengths), paths are not fixed. **Solution:** Path optimization only applies to fixed-arity constructors. Variable-arity constructs (lists, tensors) use full traversal.

2. **Hash-consing invalidation:** Changing a leaf requires rebuilding all ancestors (new hash at each level). This is O(D) `Store.put` calls regardless. **Solution:** For depth-D terms with 1 changed leaf, we do D `Store.put` calls. This is still better than full traversal + substitution of the whole tree.

### Performance at Scale

At depth 2 (current): No benefit. Path navigation = 2 steps, full traversal = 3-4 nodes. Overhead of path infrastructure may negate gains.

At depth 10: ~10x improvement on substitution step. Substitution is currently ~20% of total time. Net: ~15-18% improvement.

At depth 20: ~20x on substitution. Diminishing returns — other bottlenecks dominate.

### Zig Mapping

Paths → `comptime` array of `u8` indices. Navigation → `inline for` over path. Store.put chain → `comptime`-unrolled loop. Zero allocation, fully static.

---

## Stage 9: Discrimination Tree Indexing (future)

**Status:** Design only. Independent. Relevant when rules exceed ~100.

### Core Idea

Replace predicate-head filtering with a discrimination tree (trie) for rule selection. Currently `findAllMatches` tries each candidate rule via `tryMatch` — the opcode layer gives O(1) for 40/44 EVM rules, but this shortcut is EVM-specific. For a general calculus with 1000 rules, we need O(term-depth) rule selection instead of O(rules).

### Theoretical Background

**Discrimination trees** (Voronkov, 2001; McCune, 1992) are tries where each path corresponds to a depth-first traversal of a term. A query term traverses the trie, and at metavar (wildcard) positions, both the wildcard branch and the concrete branch are followed. All matching rules are collected at leaves.

**Path indexing** (Stickel, 1989) indexes terms by the set of (position, symbol) pairs. Faster for retrieval of instances, but discrimination trees are better for one-sided matching (our use case).

**Substitution trees** (Graf, 1995) combine indexing with substitution sharing. More complex but eliminate redundant variable bindings. Overkill for our current scale.

**Code trees** (Voronkov, 1995) — a variant used in Vampire. Compile indexing operations to bytecode instructions. Maximum flexibility, but complex implementation.

**Rete algorithm** (Forgy, 1982) — the classic forward chaining optimization. Maintains a network of partial matches, incrementally updated as facts change. Key difference from discrimination trees: Rete indexes **across multiple patterns** in a rule (join optimization), while discrimination trees index **single patterns**. Rete is more powerful for multi-pattern rules but has higher memory overhead (stores all partial matches). For linear logic where facts are consumed, Rete's partial match cache invalidation becomes complex — consumed facts must be retracted from all partial matches.

For our use case (content-addressed terms, forward chaining, linear logic), discrimination trees are the best fit: simpler than Rete, handle fact consumption naturally (no cached partial matches to invalidate), and integrate well with hash-consing.

### Design

```javascript
// Build trie at init time (once per rule set)
function buildDiscriminationTree(rules) {
  const root = { children: new Map(), wildcard: null, rules: [] };

  for (const rule of rules) {
    // Index by first linear antecedent (the "trigger" pattern)
    const trigger = rule.antecedent.linear[0];
    insertIntoTrie(root, trigger, rule);
  }
  return root;
}

function insertIntoTrie(node, pattern, rule) {
  // Depth-first traversal of pattern structure
  const tag = Store.tag(pattern);
  if (isMetavar(pattern)) {
    // Wildcard: matches any term
    if (!node.wildcard) node.wildcard = { children: new Map(), wildcard: null, rules: [] };
    node.wildcard.rules.push(rule);
    return;
  }
  // Concrete: branch on tag
  if (!node.children.has(tag)) {
    node.children.set(tag, { children: new Map(), wildcard: null, rules: [] });
  }
  const child = node.children.get(tag);
  // Recurse into children...
  child.rules.push(rule);
}

function queryTrie(node, fact) {
  const results = [];
  // Follow concrete path
  const tag = Store.tag(fact);
  if (node.children.has(tag)) {
    results.push(...node.children.get(tag).rules);
  }
  // Also follow wildcard path (patterns with metavar at this position)
  if (node.wildcard) {
    results.push(...node.wildcard.rules);
  }
  return results;
}
```

### Implementation (~300 LOC)

1. **Trie data structure:** Nodes with `Map<tag, Node>` children and a `wildcard` branch. Leaf nodes store rule references.

2. **Insertion:** Walk the trigger pattern depth-first. At each node, branch on tag. At metavars, branch to wildcard. Terminal nodes store the rule.

3. **Query:** Walk the fact depth-first. At each node, follow both the concrete branch (matching tag) and the wildcard branch. Collect all rules at leaves.

4. **Integration:** Replace the predicate-head filter loop in `findMatch()` with `queryTrie(root, changedFact)`.

5. **Incremental update:** When rules are added dynamically, insert into the trie. When removed, decrement reference count at leaf.

### Safety Proof

**Soundness:** The trie only eliminates rules that CANNOT match. If a fact doesn't match a trigger pattern's structure at any position, the full `tryMatch()` would also fail. The trie is a conservative filter.

**Completeness:** All rules with a matching trigger structure are returned. The wildcard branch ensures that rules with metavars at any position are always included.

**Proof:** Consider a rule R with trigger pattern P and a fact F. If `match(P, F, [])` succeeds, then at every position in P, either P has a metavar (wildcard → included) or P has the same tag as F (concrete branch → included). Therefore R appears in the trie query result. QED.

**Cross-check test:** Run with and without trie, assert same set of matching rules for every step.

### Complications

1. **Multi-trigger rules:** Some rules have multiple linear antecedents. Which to index on? **Solution:** Index on the most discriminating pattern (fewest matching facts). Heuristic: index on the pattern with the most concrete (non-metavar) positions. Falls back to indexing on the first linear pattern.

2. **Wildcard explosion:** If most patterns start with a metavar, the wildcard branch contains most rules, and the trie degenerates to linear scan. **Solution:** Use deeper indexing (look at child[0], child[1], etc.) to discriminate. For EVM rules, the first position is almost always a concrete predicate head — wildcard explosion is unlikely.

3. **Dynamic rules:** Adding a rule = inserting a trie path (O(pattern-depth)). Removing = decrementing a leaf counter. No full rebuild needed.

4. **Content-addressed optimization:** Since our terms are content-addressed, two facts with the same hash are identical. The trie can use **hash-based shortcuts**: if a trie node has seen a particular hash before, cache the result. This makes repeated queries O(1) via memoization.

### Performance at Scale

At 44 rules (current): ~2-3% improvement over opcode layer. Not worth the complexity.

At 100 rules: ~10-15% improvement. Opcode layer covers ~40 rules; remaining 60 need predicate-head scan.

At 400 rules: ~25-35% improvement. Trie reduces candidate set from ~400 to ~5-10 per query.

At 1000 rules: ~40-60% improvement. Linear scan of 1000 rules per step is prohibitive. Trie: O(term-depth) = O(2-4) per query.

**Memory:** O(rules × pattern-depth) nodes. At 1000 rules with depth-4 patterns: ~4000 nodes × ~50 bytes = ~200KB. Negligible.

### Zig Mapping

Trie nodes → Zig struct with `AutoHashMap(u32, *Node)` children. Wildcard → optional pointer. Rules at leaf → `ArrayList(*Rule)`. For maximum performance: flatten the trie into an array with offset-based children (cache-friendly).

Alternative: Zig `comptime` trie generation — if rules are known at compile time, the entire trie can be a comptime-generated array of structs.

### Relationship to Rete

The Rete algorithm builds a network that indexes **across multiple patterns**, maintaining partial match results (alpha memories for individual patterns, beta memories for joins). This is powerful for multi-pattern rules but comes with costs:

- **Memory:** Rete stores all partial matches. For 100000 facts and 1000 rules, partial match memory can explode.
- **Fact retraction:** In linear logic, facts are consumed. Rete must retract partial matches involving consumed facts — this is complex and error-prone.
- **Complexity:** Full Rete implementation is 1000+ LOC with subtle invalidation logic.

Our discrimination tree approach is simpler: it only indexes single patterns (the trigger), and `tryMatch()` handles the multi-pattern join. This is less optimal for rules with many antecedents but much simpler and naturally handles linear fact consumption.

**Future consideration:** If profiling shows that multi-pattern join is the bottleneck (not single-pattern lookup), a limited Rete-like approach — caching the first two patterns' join results and invalidating on consumption — could be worthwhile. But this is a Stage 10+ optimization.

---

## Profiling History

| Milestone | Median | P90 | Notes |
|-----------|--------|-----|-------|
| Original | 5.59ms | — | Baseline |
| Stage 1 (flat store) | 3.47ms | — | −38% |
| Stage 3 (preserved) | ~2.8ms | — | −6-16% |
| Strategy stack | 14ms→2.3ms | — | 12.7x (was 181ms original) |
| Incremental context | 2.3ms→1.4ms | — | 1.7x |
| Mutation+undo | 1.4ms→0.8ms | — | 1.8x |
| Index+set undo | 0.8ms→0.6ms | — | 1.25x |
| Direct FFI bypass | — | — | 1.2x |
| Stage 4 (alloc reduction) | 0.95ms | 1.2ms | P90 −9.3% |

Current bottleneck: `findAllMatches` → `tryMatch` → `match` + `applyFlat`. GC pressure reduced ~70%.

## References

- Baader & Nipkow (1998) — *Term Rewriting and All That*. Positions and paths in term rewriting.
- Conchon & Filliatre (2006) — *Type-safe modular hash-consing*. Content-addressed term stores.
- de Bruijn (1972) — *Lambda calculus notation with nameless dummies*. Positional variable indices.
- Abadi, Cardelli, Curien & Levy (1991) — *Explicit substitutions*. First-class substitution with indexed variables.
- Forgy (1982) — *Rete: A fast algorithm for the many pattern/many object match problem*. Forward chaining network optimization.
- Graf (1995) — *Substitution tree indexing*. Combined indexing and substitution sharing.
- Le Fessant & Maranget (2001) — *Optimizing pattern matching*. Decision tree compilation for pattern matching.
- Maranget (2008) — *Compiling pattern matching to good decision trees*. Optimal column selection.
- McCune (1992) — *Experiments with discrimination-tree indexing and path indexing for term retrieval*. Empirical comparison of indexing techniques.
- Sampson (2019) — *Flattening ASTs (arena allocation)*. SoA layout for compilers.
- Stickel (1989) — *The path-indexing method for indexing terms*. Alternative to discrimination trees.
- Voronkov (1995) — *The anatomy of Vampire*. Code trees for term indexing.
- Voronkov (2001) — *Term indexing*. In *Handbook of Automated Reasoning*. Comprehensive survey.
