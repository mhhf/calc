---
title: Optimization Strategies
created: 2026-02-10
modified: 2026-02-10
summary: Comprehensive catalog of deferred optimizations including clause indexing, memoization, arena allocation, and explicit substitutions
tags: [optimization, performance, benchmarking, strategies]
---

# Optimization Strategies for Content-Addressed Proof Search

Deferred optimizations to benchmark and evaluate. Each should be tested with real workloads before implementation.

---

## MDE Backward Prover Performance (Feb 2026)

### Deep Benchmark Results

Benchmark: `tests/mde/backward-benchmark.js`

| Complexity | Avg Time | Recursion Depth | Clauses Tried | Unify Attempts |
|------------|----------|-----------------|---------------|----------------|
| **Easy** (0+0, 0+1) | 0.11 ms | 0 | 0 (types only) | 22 |
| **Medium** (1+1, 3+2, 4+4) | 0.69 ms | 2 | 13 | 218 |
| **Complex** (15+17, 127+1) | 1.98 ms | 6.3 | 79 | 878 |

### Bottleneck Analysis (Complex Queries)

| Component | % of Time | Issue |
|-----------|-----------|-------|
| **Clause Iteration** | 347% | Loop overhead dominates |
| Unification | 44.5% | |
| Freshening | 34.5% | |
| Substitution | 12.0% | |

**Critical insight:** 98.6% of unify attempts fail (3462 wasted / 3510 total)

### Specific Examples

| Query | Time | Depth | Clauses | Unify Success |
|-------|------|-------|---------|---------------|
| 0 + 0 = 0 | 0.08 ms | 0 | 0 | 4.8% |
| 3 + 2 = 5 | 0.73 ms | 2 | 13 | 1.9% |
| 15 + 17 = 32 | 1.44 ms | 5 | 37 | 1.4% |
| 127 + 1 = 128 | 0.91 ms | 7 | 25 | 1.4% |

### MDE-Specific Optimizations

| Optimization | Expected Speedup | Effort | Status |
|--------------|------------------|--------|--------|
| **Clause Indexing** | 10-50x | MEDIUM | **IMPLEMENTED** |
| **Goal Memoization** | 60x on repeated | LOW | Tested |
| **First-Arg Indexing** | 2.3x | MEDIUM | **IMPLEMENTED** |
| **Compile Arithmetic** | 100-1000x | HIGH | Future |
| **Reduce Allocations** | 1.5-2x | LOW | Planned |

### Memoization Results (Tested)

```
Without memoization: 0.22 ms/query
With memoization:    0.004 ms/query
Speedup:             60x
```

### Clause Indexing Impact Analysis

Current: iterate 81 types + 37 clauses = 118 items per search call

With first-argument indexing on `plus`, `inc`, `mul`:
- `plus` has 4 recursive clauses + 5 type axioms
- Only need to check ~9 items instead of 118 (13x reduction)
- Est. speedup: 5-10x for recursion-heavy queries

---

## Bug Fix: Variable Freshening Collision (Feb 2026)

**Symptom:** `mul 7 7` and `mul 7 3` failed while `mul 7 4`, `mul 7 5`, `mul 7 6` worked.

**Root Cause:** `freshenClause` used recursion depth as suffix for variable renaming:
```javascript
const suffix = `_d${depth}`;  // BUG: same depth visited multiple times!
```

When the same depth is visited multiple times during search (e.g., `plus 7 14` at depth 2, then `plus 3 21` also at depth 2), variables like `_M_d2` get reused. The old bindings from `plus 7 14` pollute the proof of `plus 3 21`.

**Fix:** Use a global counter instead of depth:
```javascript
let freshCounter = 0;
// ...
const { head, premises } = freshenClause(clause, freshCounter++);
```

**File:** `lib/mde/prove.js`

---

## First-Arg Indexing: Implementation (Feb 2026)

### Results

| Query | Candidates | Reduction | Time (warm) |
|-------|------------|-----------|-------------|
| `mul 7*7` | 1 | 99.2% | 0.91ms |
| `plus 7+7` | 3 | 97.5% | 0.10ms |
| `mul 3*3` | 1 | 99.2% | 0.16ms |
| `inc 1` | 1 | 99.2% | - |

**Speedup:** ~2.7x for `mul 7*7` (0.91ms vs ~2.5ms baseline)

### Index Structure

Two-level: `head → firstArgCtor → [items]`

```
Types:   plus: { e:3, o:1, i:1 }, mul: { e:1 }, inc: { o:1, e:1 }
Clauses: plus: { o:2, i:2 }, mul: { o:1, i:1 }, inc: { i:1 }
```

### Why Unification Can't Act as Free Filter

**Problem:** Curried terms bury head functor O(arity) deep:
```
mul 7 7 X = app(app(app(app(mul, 7), 7), X))
```

To discover head mismatch (e.g., `mul` vs `plus`), unification must:
1. Traverse 3-4 `app` nodes to reach head
2. Compare atoms
3. This is O(arity) per clause × 118 clauses = O(n·arity) wasted work

### How CLF/Celf/Ceptre Handle This

**Celf** (`getCandAtomic` in `unify.sml`):
- Index clauses by atomic head before search
- Only unify with clauses matching goal's head

**Prolog WAM** uses three-level indexing:
1. `switch_on_term` - dispatch by term type
2. `switch_on_constant` - hash table for first-arg constant
3. `switch_on_structure` - hash table for first-arg functor

### Our Implementation

```javascript
function getHead(hash)        // O(arity) - extract head functor
function getFirstArgCtor(hash) // O(arity) - get first arg constructor
function buildIndex(clauses, types) // O(n·arity) one-time
function getCandidates(idx, goalHash) // O(1) lookup
```

**Catch-all bucket `'_'`** handles clauses with variable first-arg.

**File:** `lib/mde/prove.js`

---

## Post-Indexing Bottleneck Analysis (Feb 2026)

After implementing first-arg indexing, **59x fewer candidates** but only **2.7x speedup**. Why?

### New Bottleneck: Variable Freshening

| Component | Time (μs) | Notes |
|-----------|-----------|-------|
| `Store.intern` (freshening) | 14.4 | **Dominant** |
| `unify` | 13.2 | Per candidate |
| `getCandidates` | 1.9 | O(1) lookup |
| `subApply` | 2.6 | Per premise |

**`mul 7*7` proof:** 20 search calls × ~45μs = 900μs total

### Why Freshening Dominates

Each clause application creates fresh variables:
```javascript
freshenClause(clause, freshCounter++)  // Creates new _Z_c0, _M_c0, etc.
```

With 20 search calls and ~3 vars per clause = 60+ `Store.intern` calls at 14μs each.

### Next Optimization Targets

| Optimization | Expected Impact | Effort |
|--------------|-----------------|--------|
| **Lazy freshening** | 2-3x | LOW |
| **Goal memoization** | 60x on repeated | LOW |
| **Compiled arithmetic** | 100-1000x | HIGH |

**Lazy freshening:** Only freshen variables that actually get bound. Most clauses fail unification before binding all vars.

**Goal memoization:** Cache `goalHash → result`. Content-addressing makes keys trivial. Already tested: 60x on repeated goals.

**Compiled arithmetic:** Replace `plus`, `mul`, `inc` with native JS functions. Eliminates proof search entirely for arithmetic.

---

## Priority Assessment

Based on deep benchmarking (Feb 2026):

| Optimization | Impact | Complexity | Status |
|--------------|--------|------------|--------|
| **Clause Indexing (MDE)** | **2.3x** | MEDIUM | **IMPLEMENTED** (Feb 2026) |
| Goal Memoization (MDE) | HIGH | LOW | Tested: 60x on repeated goals |
| Constructor Index | HIGH | LOW | If identity lookup is bottleneck |
| Proof Memoization | HIGH | MEDIUM | If proof search repeats subgoals |
| Near-Linear Unification | MEDIUM | MEDIUM | Unify is 44% of time |
| Explicit Substitutions | LOW | HIGH | Only 12% of time in subApply |
| Persistent Data Structures | LOW | LOW | Not needed for MDE |
| Arena Allocation | LOW | LOW (Zig) | For Zig port |

---

## 1. O(1) Identity via Constructor Index

**Current:** `tryIdPos` iterates through ALL context formulas trying unification.

```javascript
// Current: O(m·n²) - try mgu with each formula
Object.keys(ctx).find(id => {
  theta = mgu([[ctxFormula, formula]]);  // O(n²)
  return !!theta;
});
```

**Better:** Index context by constructor ID for O(1) ground lookup, O(c) variable lookup:

```javascript
class ContextIndex {
  constructor(store) {
    this.store = store;
    this.byHash = new Map();        // hash → entry (ground formulas)
    this.byConstructor = new Map(); // constructorId → [entry] (for unification)
  }

  add(hash, entry) {
    this.byHash.set(hash, entry);
    const data = this.store.getStructural(hash);
    if (!data) return;
    const ctorId = data.constructorId;
    if (!this.byConstructor.has(ctorId)) {
      this.byConstructor.set(ctorId, []);
    }
    this.byConstructor.get(ctorId).push({ hash, entry });
  }

  // O(1) for ground formulas!
  findExact(hash) {
    return this.byHash.get(hash);
  }

  // O(c) where c = formulas with same outermost constructor
  findUnifiable(hash) {
    const data = this.store.getStructural(hash);
    if (!data) return null;
    const candidates = this.byConstructor.get(data.constructorId) || [];
    for (const { hash: candHash, entry } of candidates) {
      const theta = mgu_fast(candHash, hash);
      if (theta) return { entry, theta };
    }
    return null;
  }
}
```

**Impact:** For ground formulas (no variables), identity becomes O(1) hash lookup.

**Benchmark:** Measure c/m ratio (candidates vs total context size) on real proofs.

---

## 2. Subformula Property Memoization

From [Verified and Optimized Implementation of Orthologic Proof Search](https://arxiv.org/html/2501.09418): subformula property + memoization = polynomial complexity.

**Why it works:**
- Cut-free proofs have subformula property: only subformulas of input appear
- If input has n subformulas, at most O(n²) unique sequents possible
- Memoize proof results: `sequentHash → ProofResult`
- Each unique sequent computed at most once

```javascript
class ProofMemo {
  constructor() {
    this.cache = new Map();  // sequentHash → { success, theta, proofTree }
    this.hits = 0;
    this.misses = 0;
  }

  key(seq) {
    // Canonical key: sorted context hashes + succedent hash
    const ctxHashes = Object.keys(seq.linear_ctx)
      .map(BigInt)
      .sort((a, b) => a < b ? -1 : 1);
    const persHashes = Object.keys(seq.persistent_ctx)
      .map(BigInt)
      .sort((a, b) => a < b ? -1 : 1);
    return hashCombine(...persHashes, ...ctxHashes, seq.succedent);
  }

  lookup(seq) {
    const k = this.key(seq);
    if (this.cache.has(k)) {
      this.hits++;
      return this.cache.get(k);
    }
    this.misses++;
    return null;
  }

  store(seq, result) {
    const k = this.key(seq);
    this.cache.set(k, result);
  }
}
```

**Complexity impact:**
- Without memoization: O(b^d) where b = branching, d = depth
- With memoization: O(n²) where n = subformulas

**Benchmark:** Verify ILL has subformula property. Measure hit rate on real proofs.

---

## 3. Near-Linear Unification

**Current:** Robinson unification with O(n²) complexity (due to eager substitution propagation).

```javascript
// Current mgu.js - O(n²) due to eager substitution
theta = propagate(theta, new_theta);  // O(k·n) per iteration
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))  // O(n) per pair
```

**Better:** [Martelli-Montanari algorithm](https://dl.acm.org/doi/10.1145/357162.357169) with union-find achieves O(n·α(n)) ≈ O(n).

```javascript
class UnionFind {
  constructor() {
    this.parent = new Map();
    this.rank = new Map();
  }

  find(x) {
    if (!this.parent.has(x)) return x;
    // Path compression
    const root = this.find(this.parent.get(x));
    this.parent.set(x, root);
    return root;
  }

  union(x, y) {
    const rx = this.find(x), ry = this.find(y);
    if (rx === ry) return;
    // Union by rank
    const rankX = this.rank.get(rx) || 0;
    const rankY = this.rank.get(ry) || 0;
    if (rankX < rankY) this.parent.set(rx, ry);
    else if (rankX > rankY) this.parent.set(ry, rx);
    else { this.parent.set(ry, rx); this.rank.set(rx, rankX + 1); }
  }
}
```

**Research:** [A practically efficient and almost linear unification algorithm](https://www.sciencedirect.com/science/article/abs/pii/0004370288900057) by Paterson & Wegman achieves true O(n).

**Benchmark:** Compare current mgu vs Martelli-Montanari on realistic proof search workloads.

---

## 4. Explicit Substitutions (Lazy Evaluation)

**Current:** Substitution eagerly traverses entire term.

```javascript
// Current substitute.js - O(n) per substitution
node.vals = node.vals.map(v => sub(v, key, val))
```

**Problem:** When we do `seq.substitute(theta)`, we traverse ALL formulas even if most are unchanged. For a sequent with m formulas of size n and k substitutions, this is O(m·k·n).

**Better:** [Explicit substitution calculus](https://dl.acm.org/doi/10.1145/96709.96712) delays substitution:

```javascript
class Closure {
  constructor(hash, env) {
    this.hash = hash;      // Original term hash
    this.env = env;        // Map: varHash → valueHash
  }

  // Force evaluation only when needed
  force(store) {
    if (this.env.size === 0) return this.hash;
    return forceSubstitute(store, this.hash, this.env);
  }

  // Compose closures without forcing
  compose(otherEnv) {
    const newEnv = new Map(this.env);
    for (const [k, v] of otherEnv) {
      if (!newEnv.has(k)) newEnv.set(k, v);
    }
    return new Closure(this.hash, newEnv);
  }
}
```

**When to force:**
- Rendering (need actual term)
- Hashing for memoization (need canonical form)
- Identity check on ground formula

**Benchmark:** Analyze how many substitutions are applied before terms are actually needed.

---

## 5. Persistent Data Structures for Sequent

**Current:** `copyMS()` creates new object, `Sequent.copy()` deep copies.

**Better:** [Persistent data structures](https://en.wikipedia.org/wiki/Persistent_data_structure) with path copying:

```javascript
// Using immutable.js or similar
import { Map as ImmutableMap } from 'immutable';

class PersistentSequent {
  constructor(persistentCtx, linearCtx, succedent) {
    this.persistentCtx = persistentCtx;  // ImmutableMap
    this.linearCtx = linearCtx;          // ImmutableMap
    this.succedent = succedent;          // hash
  }

  // O(log m) update, O(1) "copy"
  addToLinear(hash, entry) {
    return new PersistentSequent(
      this.persistentCtx,
      this.linearCtx.set(hash, entry),
      this.succedent
    );
  }

  // O(1) "copy" - just return this (immutable!)
  copy() {
    return this;
  }
}
```

**Trade-off:**
- Allocation: O(log m) vs O(m) for full copy
- Access: O(log m) vs O(1) for plain object
- Memory: Sharing across branches saves memory

**Benchmark:** Compare ImmutableMap vs plain object for realistic context sizes.

---

## 6. Arena Allocation for Proof Branches

**Concept:** Each proof branch gets its own arena. On backtrack, free entire arena at once.

**JavaScript:** Already have ScopedStore design. Main benefit is avoiding GC pauses.

**Zig:** [Arena allocators](https://www.gingerbill.org/article/2019/02/08/memory-allocation-strategies-002/) are idiomatic:

```zig
pub fn searchBranch(parent_arena: *ArenaAllocator) !ProofResult {
    var branch_arena = ArenaAllocator.init(parent_arena.allocator);
    defer branch_arena.deinit();  // Free everything on backtrack

    const store = ScopedStore.init(&branch_arena, parent_store);
    // ... proof search ...

    if (success) {
        return commitToParent(parent_arena, result);
    }
    // On failure: branch_arena.deinit() frees everything - O(1)!
}
```

**Impact:**
- Failed branches: O(1) deallocation instead of GC traversal
- No GC pauses during search
- Better cache locality

**Benchmark:** Measure GC time percentage in long proof searches.

---

## 7. Term Indexing (Substitution Trees)

For very large contexts (100s of formulas), even constructor-indexed lookup may be slow. [Substitution tree indexing](https://pure.mpg.de/rest/items/item_1834191_2/component/file_1857890/content) provides logarithmic lookup.

**When to use:** Context size > 50-100 formulas.

**Complexity:** O(log m) for retrieval vs O(c) for constructor index.

**Benchmark:** Find threshold where substitution trees beat simple constructor indexing.

---

## 8. Opaque Primitive Storage

For 256-bit numbers (EVM words), store as opaque leaves instead of 256-level trees:

```javascript
// Instead of 256-level tree:
{ type: 'structural', id: 'bin_i', children: [{ id: 'bin_i', ... }] }

// Store as single opaque leaf:
{
  type: 'opaque',
  dataType: 'bin',
  value: 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffn,
  hash: hash('bin:' + value.toString(16))
}
```

| Aspect | Structural (256-bit) | Opaque |
|--------|----------------------|--------|
| Nodes | 256 | 1 |
| Memory | ~6KB | ~40 bytes |
| Intern time | O(256) | O(1) |

**When to implement:** When FFI with large numbers is needed.

---

## Research Directions

These need more investigation:

1. **De Bruijn Indices** — For alpha-equivalence if needed
2. **E-graphs** — For equality reasoning / congruence closure
3. **BDD-style Reduction** — Canonical forms during interning
4. **Lazy Proof Construction** — Return proof "recipe" not actual tree
5. **Incremental Proof Maintenance** — Reuse partial proofs on input changes
6. **Parallel Proof Search** — Exploit ScopedStore for safe parallelism

---

## Benchmarking Strategy

Before implementing any optimization:

1. **Profile current code** with `CALC_PROFILE=1`
2. **Identify actual bottleneck** from profiler output
3. **Create benchmark case** that exercises the bottleneck
4. **Implement optimization** with feature flag
5. **Measure improvement** on benchmark
6. **Verify no regression** on test suite
