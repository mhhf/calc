---
title: Prover Optimization Research
created: 2026-02-10
modified: 2026-02-11
summary: Comprehensive research on proof search optimization including benchmarks, implemented optimizations, and deferred strategies
tags: [optimization, performance, benchmarking, prover, research]
---

# Prover Optimization Research

Comprehensive research on proof search optimization strategies.

## Table of Contents

1. [Current Bottleneck Analysis](#1-current-bottleneck-analysis)
2. [Implemented Optimizations](#2-implemented-optimizations)
3. [Deferred Optimizations Catalog](#3-deferred-optimizations-catalog)
4. [Memory Management](#4-memory-management)
5. [Research Directions](#5-research-directions)

---

## 1. Current Bottleneck Analysis

### Dual Representation Problem (v2 Focused Prover)

We maintain TWO representations of linear resources:

| Representation | Format | Purpose |
|----------------|--------|---------|
| `seq.contexts.linear` | Array of hashes | "What formulas are available" |
| `delta` | Multiset `{hash: count}` | "What resources remain" |

**They contain the same information!** Constant conversion is ~25% of runtime.

**Solution:** Use multiset as single source of truth.

### MDE Backward Prover Benchmarks

| Complexity | Avg Time | Recursion Depth | Unify Attempts |
|------------|----------|-----------------|----------------|
| Easy (0+0, 0+1) | 0.11 ms | 0 | 22 |
| Medium (1+1, 3+2) | 0.69 ms | 2 | 218 |
| Complex (15+17, 127+1) | 1.98 ms | 6.3 | 878 |

**Critical insight:** 98.6% of unify attempts fail (3462 wasted / 3510 total).

---

## 2. Implemented Optimizations

### First-Argument Indexing (Feb 2026)

Two-level index: `head → firstArgCtor → [items]`

| Query | Candidates | Reduction | Time |
|-------|------------|-----------|------|
| `mul 7*7` | 1 | 99.2% | 0.91ms |
| `plus 7+7` | 3 | 97.5% | 0.10ms |

**Speedup:** ~2.7x for complex queries.

**File:** `lib/mde/prove.js`

### Goal Memoization (Tested)

```
Without memoization: 0.22 ms/query
With memoization:    0.004 ms/query
Speedup:             60x on repeated goals
```

### Bug Fix: Variable Freshening Collision

**Root cause:** Used recursion depth as suffix for variable renaming. Same depth visited multiple times caused collision.

**Fix:** Use global counter instead of depth.

---

## 3. Deferred Optimizations Catalog

### High Priority

| Optimization | Expected Impact | Effort |
|--------------|-----------------|--------|
| Eliminate dual representation | ~25% | MEDIUM |
| Proof memoization | Polynomial complexity | MEDIUM |
| Constructor index | O(1) identity lookup | LOW |

### Medium Priority

| Optimization | Impact | Notes |
|--------------|--------|-------|
| Near-linear unification | Unify is 44% of time | Martelli-Montanari + Union-Find |
| Lazy freshening | 2-3x | Only freshen bound variables |
| Persistent data structures | O(1) copy | HAMT for sequents |

### Low Priority / Future

| Optimization | When to use |
|--------------|-------------|
| Explicit substitutions | If substitution dominates |
| Term indexing (substitution trees) | Context > 100 formulas |
| Arena allocation | For Zig port |
| Compiled arithmetic | Replace proof search with native ops |

---

## 4. Memory Management

### The Problem

Proof search creates many short-lived objects. Failed branches allocate thousands of objects that become garbage.

**Effects:**
- GC pauses during search
- Memory fragmentation
- Poor cache locality

### Arena Allocation Strategy

**Concept:** Each proof branch gets its own arena. On backtrack, free entire arena at once (O(1)).

**JavaScript approach:** ScopedStore pattern:
```javascript
class ScopedStore {
  constructor(parent) {
    this.parent = parent;
    this.local = new Map();
  }
  fork() { return new ScopedStore(this); }
  discard() { this.local.clear(); }  // Free branch
}
```

**Zig approach:** Native arena allocators with bulk deallocation.

### When to Implement

Priority: LOW (for JavaScript). MEDIUM (for Zig port).

Profile first with `CALC_PROFILE=1` to verify GC is actually a bottleneck.

---

## 5. Research Directions

These need more investigation:

| Direction | Purpose |
|-----------|---------|
| De Bruijn indices | Alpha-equivalence if needed |
| E-graphs | Equality reasoning / congruence closure |
| Parallel proof search | Exploit ScopedStore for parallelism |
| Incremental proof maintenance | Reuse partial proofs on input changes |

---

## Benchmarking Strategy

Before implementing any optimization:

1. Profile with `CALC_PROFILE=1`
2. Identify actual bottleneck
3. Create benchmark exercising the bottleneck
4. Implement with feature flag
5. Measure improvement
6. Verify no regression

---

## Related Documents

- Dev: [[primitives-implementation]] — Lazy primitive storage (binlit)
- Research: [[content-addressed-formulas]] — Foundation for all optimizations
- Research: [[benchmarking]] — Hotspot analysis
