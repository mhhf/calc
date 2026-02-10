---
title: "Backward Prover Optimization: Deep Analysis"
created: 2026-02-10
modified: 2026-02-10
summary: Analysis of proof search bottlenecks revealing 90% overhead in substitution operations with optimization strategies for 10-30x speedup through simultaneous substitution and union-find unification.
tags: [optimization, proof-search, substitution, unification, performance]
---

# Backward Prover Optimization: Deep Analysis

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Current Bottleneck Analysis](#current-bottleneck-analysis)
3. [Optimization Strategies Ranked by Impact](#optimization-strategies-ranked-by-impact)
4. [Recommended Implementation Plan](#recommended-implementation-plan)
5. [Benchmark Summary](#benchmark-summary)
6. [References](#references)

---

## Executive Summary

Analysis of backward chaining in `lib/mde/prove.js` reveals **90%+ overhead** in substitution operations (`subApply` 56.4%, `unify` 33.9%). Benchmarking shows:

| Strategy | Gets Reduction | Speed Improvement |
|----------|----------------|-------------------|
| Simultaneous substitution | **63x** (large theta) | **21x faster** |
| Union-Find unification | **4x** | **2x faster** |
| Combined (estimated) | - | **10-30x faster** |

## Current Bottleneck Analysis

### Problem 1: Sequential Substitution O(N × M)

```javascript
// substitute.js:70 - CURRENT (SLOW)
const apply = (h, theta) => theta.reduce((acc, [v, val]) => sub(acc, v, val), h);
```

For N bindings and M-node term:
- Each `sub()` traverses entire term: O(M)
- Applied N times sequentially: O(N × M) total

**Benchmark** (12 bindings, 3-var term):
- Original: **251 Store.get** calls
- Simultaneous: **4 Store.get** calls (63x reduction)

### Problem 2: Quadratic Theta Maintenance O(K²)

```javascript
// unify.js:72-74 - CURRENT (SLOW)
theta = [...theta.map(([v, x]) => [v, sub(x, t0, t1)]), [t0, t1]];
G.forEach((g, i) => { G[i] = [sub(g[0], t0, t1), sub(g[1], t0, t1)]; });
```

Every new binding (K total):
1. Apply new sub to all K-1 existing bindings
2. Apply new sub to all remaining goals
**Total: O(K² × M) substitution applications**

### Problem 3: No Backtracking - All Overhead is Success Path

Trace of `plus 20 118 X` shows **zero failed branches**:
- 10 successful unifies, 10 failed (quick mismatch)
- All expensive work builds the successful solution

## Optimization Strategies Ranked by Impact

### 1. Simultaneous Substitution ⭐⭐⭐⭐⭐ (HIGHEST IMPACT)

**Implementation**:
```javascript
const applySimultaneous = (h, theta) => {
  if (theta.length === 0) return h;
  const varMap = new Map(theta);  // O(N) build, O(1) lookup

  function go(hash) {
    if (varMap.has(hash)) return varMap.get(hash);
    const node = Store.get(hash);
    if (!node || node.tag === 'atom' || node.tag === 'freevar') return hash;

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });
    return changed ? Store.intern(node.tag, newChildren) : hash;
  }
  return go(h);
};
```

**Complexity**: O(M) instead of O(N × M)

**Benchmark Results**:
| Theta Size | Original gets | Simultaneous gets | Speedup |
|------------|---------------|-------------------|---------|
| 3 bindings | 17 | 3 | 5.7x |
| 12 bindings | 251 | 4 | **63x** |

**Why it's safe**: Current `unify()` produces idempotent MGU - variables never reference other bound variables.

**Effort**: 1-2 hours | **Expected speedup**: 5-20x on apply

---

### 2. Union-Find Unification ⭐⭐⭐⭐

> **See also:** [[near-linear-unification]] for detailed algorithm analysis.

Based on [Martelli-Montanari algorithm](https://dl.acm.org/doi/10.1145/357162.357169) with union-find:

**Key insight**: Instead of maintaining idempotent substitution, use union-find with path compression:
- Adding binding: O(α(n)) ≈ O(1) amortized
- Finding canonical: O(α(n)) with path compression

**Benchmark Results**:
| Algorithm | Gets/op | Time/op |
|-----------|---------|---------|
| Original unify | 84 | 0.0184ms |
| Triangular | 32 | 0.0178ms |
| Union-Find | **21** | **0.0091ms** |

**Implementation complexity**: Medium - need careful occurs check handling

**Effort**: 3-4 hours | **Expected speedup**: 2-4x on unify

---

### 3. Triangular Substitution ⭐⭐⭐

From [miniKanren research](https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf):

**Concept**: Don't maintain idempotent form. Just append bindings, resolve on demand via "walk".

```javascript
// Just append, O(1)
theta.push([t0, t1]);

// Walk on lookup
const walk = (h, theta) => {
  for (const [v, val] of theta) {
    if (v === h) return walk(val, theta);
  }
  return h;
};
```

**Trade-off**:
- Binding: O(1) instead of O(K × M)
- Lookup: O(K) walk (can optimize with [skew binary lists](https://github.com/michaelballantyne/faster-minikanren))

**Effort**: 2-3 hours | **Expected speedup**: 2-3x on unify

---

### 4. Tabling/Memoization ⭐⭐⭐

> **See also:** [[polynomial-memoization]] for proof search memoization.

[SLG resolution](https://www.swi-prolog.org/pldoc/man?section=tabling) memoizes subgoals:

**For our case**: Cache `prove(goal)` results within a proof.

```javascript
const proveCache = new Map();

function cachedProve(goal, ...) {
  const key = goal;  // Hash IS the key (content-addressed)
  if (proveCache.has(key)) return proveCache.get(key);
  const result = actualProve(goal, ...);
  proveCache.set(key, result);
  return result;
}
```

**Benefit**: If same subgoal appears multiple times, compute once.

**Limitation**: For `plus` proof, each goal is unique (no repetition). More useful for:
- Recursive predicates with overlapping subproblems
- Forward chaining (where same backward goals may recur)

**Effort**: 1-2 hours | **Expected speedup**: Variable (0-5x depending on goal structure)

---

### 5. Hash-Consing Optimizations ⭐⭐

We already use [hash-consing](https://en.wikipedia.org/wiki/Hash_consing) (Store). Potential improvements:

**A. Intern during substitution traversal**:
- Current: Check if changed, then intern
- Better: Memoize `go(hash)` within single `apply()` call

```javascript
function applyWithMemo(h, theta) {
  const memo = new Map();
  const varMap = new Map(theta);

  function go(hash) {
    if (memo.has(hash)) return memo.get(hash);
    // ... traversal ...
    memo.set(hash, result);
    return result;
  }
  return go(h);
}
```

**B. Weak map for garbage collection**: Current Store never garbage collects. For long-running proofs, could use WeakMap.

**Effort**: 1 hour | **Expected speedup**: 1.2-1.5x

---

### 6. Explicit Substitutions (λσ-calculus) ⭐⭐

> **See also:** [[explicit-substitutions]] for detailed treatment.

From [Abadi et al.](https://dl.acm.org/doi/10.1145/96709.96712):

**Concept**: Delay substitution, represent as closures:
```javascript
// Instead of eagerly applying:
const result = apply(term, theta);

// Represent suspended:
const closure = { term, env: theta };

// Force only when comparing
const force = (c) => applySimultaneous(c.term, c.env);
```

**Benefit**: Compose substitutions without traversing: `{term, env1 ∘ env2}`

**Trade-off**: Complex implementation, benefits mainly in lazy evaluation contexts.

**Effort**: 4-6 hours | **Expected speedup**: Variable

---

### 7. E-graphs / Congruence Closure ⭐

[E-graphs](https://en.wikipedia.org/wiki/E-graph) represent equivalence classes:

**Potential use**: Instead of applying substitutions, maintain equivalence classes. Two terms equal if same e-class.

**Reality check**: E-graphs excel at equality saturation and optimization problems. For our backward chaining prover, the overhead of maintaining e-graph may exceed benefit.

**Effort**: 8+ hours | **Expected speedup**: Unclear for this use case

---

### 8. De Bruijn Indices ⭐

**Analysis showed**: Freshening is only 7.5% of overhead.

**Would help if**:
- Many more clause applications
- Combined with explicit substitutions

**Doesn't help because**:
- Still need O(M) "shift" operation
- Complicates equality checks

**Effort**: 6+ hours | **Expected speedup**: ~1.1x (eliminates 7.5%)

---

## Recommended Implementation Plan

### Phase 1: Quick Wins (Est. 2-3 hours, Expected 10-20x speedup)

1. **Replace `apply()` with simultaneous version** in `substitute.js`
   - Single traversal instead of sequential
   - Verified safe for idempotent MGU

2. **Add memoization within apply**
   - Cache intermediate results during single call

### Phase 2: Unification Optimization (Est. 3-4 hours, Additional 2-3x)

1. **Implement triangular unification**
   - Remove quadratic theta maintenance
   - Add efficient walk with path compression

2. **Or: Implement union-find unification**
   - Better theoretical complexity
   - More implementation work

### Phase 3: Advanced (Optional, Variable benefit)

1. **Tabling for repeated subgoals**
2. **Attributed variables for constraints**
3. **Lazy/explicit substitutions**

## Benchmark Summary

```
Test 1: Unification
Original unify:     84 gets/op
Union-Find unify:   21 gets/op  (4x fewer)

Test 2: Substitution (small, 3 bindings)
Original apply:     17 gets/op
Simultaneous apply: 3 gets/op   (5.7x fewer)

Test 3: Substitution (large, 12 bindings)
Original apply:     251 gets/op
Simultaneous apply: 4 gets/op   (63x fewer!)
```

## References

- [Martelli-Montanari: An Efficient Unification Algorithm](https://dl.acm.org/doi/10.1145/357162.357169)
- [Comparing Unification Algorithms in First-Order Theorem Proving](http://www.cs.man.ac.uk/~hoderk/ubench/unification_full.pdf)
- [Efficient representations for triangular substitutions (miniKanren)](https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf)
- [Hash consing - Wikipedia](https://en.wikipedia.org/wiki/Hash_consing)
- [SWI-Prolog Tabling (SLG resolution)](https://www.swi-prolog.org/pldoc/man?section=tabling)
- [Explicit substitutions - Wikipedia](https://en.wikipedia.org/wiki/Explicit_substitution)
- [E-graph - Wikipedia](https://en.wikipedia.org/wiki/E-graph)
- [faster-miniKanren (GitHub)](https://github.com/michaelballantyne/faster-minikanren)
- [Union-Find pack for SWI-Prolog](https://www.swi-prolog.org/pack/list?p=union_find)
