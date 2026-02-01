# Optimization Strategies for Content-Addressed Proof Search

Deferred optimizations to benchmark and evaluate. Each should be tested with real workloads before implementation.

---

## Priority Assessment

| Optimization | Impact | Complexity | When to Implement |
|--------------|--------|------------|-------------------|
| Constructor Index | HIGH | LOW | If identity lookup is bottleneck |
| Proof Memoization | HIGH | MEDIUM | If proof search repeats subgoals |
| Near-Linear Unification | MEDIUM | MEDIUM | If unification is bottleneck |
| Explicit Substitutions | MEDIUM | HIGH | If many unused substitutions |
| Persistent Data Structures | LOW | LOW | If sequent copying is bottleneck |
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
