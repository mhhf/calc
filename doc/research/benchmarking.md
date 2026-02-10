---
title: "CALC Operations Analysis and Benchmarking Strategy"
created: 2026-02-10
modified: 2026-02-10
summary: Catalog of CALC's primitive operations showing proof search dominated by O(n²) unification and O(n×m) substitution with benchmarking framework for performance measurement.
tags: [benchmarking, complexity-analysis, performance, profiling, optimization]
---

# CALC Operations Analysis and Benchmarking Strategy

Research document analyzing primitive operations, their complexity, usage frequency, and benchmarking strategy.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Part 1: Primitive Operations Catalog](#part-1-primitive-operations-catalog)
3. [Part 2: Call Graph Analysis](#part-2-call-graph-analysis)
4. [Part 3: Complexity Summary](#part-3-complexity-summary)
5. [Implementation](#implementation)
6. [References](#references)

---

## Executive Summary

This document catalogs all primitive operations in CALC, analyzes their computational complexity, traces their usage during proof search, and proposes a benchmarking framework to measure real-world performance.

**Key Finding:** The proof search hot path is dominated by:
1. **Unification (mgu)** — O(n²) due to repeated toString() comparisons
2. **Substitution** — O(n) per call, called O(m) times per unification
3. **Context operations** — O(n) per hash computation
4. **Deep copying** — O(n) everywhere, no structural sharing

---

## Part 1: Primitive Operations Catalog

### 1.1 Node Operations (lib/node.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **Create** | `new Node(id, vals)` | O(1) | Allocate node with rule ID and children |
| **Copy** | `node.copy()` | O(n) | Deep recursive copy of entire subtree |
| **Equality** | (implicit via toString) | O(n) | No direct equality — uses string comparison |
| **toString** | `node.toString(style)` | O(n) | Serialize to ASCII/LaTeX/Isabelle format |
| **isVar** | `node.isVar()` | O(1) | Check if node is a variable |
| **isTermType** | `node.isTermType()` | O(1) | Check if Structure_Term_Formula |

**Code location:** `lib/node.js:1-150`

**Key issue:** No identity/hash — equality requires full tree traversal via toString().

### 1.2 Sequent Operations (lib/sequent.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **fromTree** | `Sequent.fromTree(ast)` | O(n) | Parse AST into sequent structure |
| **copy** | `Sequent.copy(seq)` | O(n) | Deep copy entire sequent |
| **toString** | `seq.toString(style)` | O(n) | Serialize sequent |
| **add_to_linear_ctx** | (internal) | O(n) | Add formula to context, hash via sha3(toString) |
| **add_to_antecedent_bulk** | `Sequent.add_to_antecedent_bulk()` | O(m·n) | Add multiple formulas |
| **remove_from_antecedent** | `Sequent.remove_from_antecedent()` | O(m) | Remove formulas from context |
| **remove_structural_variables** | `Sequent.remove_structural_variables()` | O(m) | Clean up structural vars |
| **substitute** | `seq.substitute(theta)` | O(n·k) | Apply substitution list |
| **getFreeVariables** | `Sequent.getFreeVariables()` | O(n) | Collect all free variables |
| **getAtoms** | `Sequent.getAtoms()` | O(n) | Collect atomic propositions |
| **renameUnique** | `Sequent.renameUnique()` | O(n) | Alpha-rename to fresh variables |
| **renameUniqueArray** | `Sequent.renameUniqueArray()` | O(m·n) | Rename array of sequents |
| **constructCompareOptions** | `Sequent.constructCompareOptions()` | O(m!) | Generate permutations for multiset matching |

**Code locations:**
- `lib/sequent.js:255` — sha3(ast.toString()) for context keys
- `lib/sequent.js:420` — fromTree with linear_ctx construction
- `lib/sequent.js:180` — copy operation

**Critical hotspot:** `sha3(ast.toString())` — called on every context insertion.

### 1.3 Unification Operations (lib/mgu.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **mgu** | `mgu(pairs)` | O(n²) | Most General Unifier computation |
| **propagate** | (internal) | O(n·k) | Propagate substitution through pairs |
| **occurs** | (internal) | O(n) | Occurs check |

**Code location:** `lib/mgu.js:1-120`

```javascript
// Line 23: O(n) equality check
let isEq = t0.toString() === t1.toString();

// Line 45-46: O(n) substitutions applied to all remaining pairs
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))
```

**Complexity breakdown:**
- Per iteration: O(n) equality + O(m·n) substitutions
- Total iterations: O(k) where k = number of variables
- Overall: O(k²·n) in worst case

### 1.4 Substitution Operations (lib/substitute.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **substitute** | `substitute(node, var, term)` | O(n) | Replace variable with term |
| **subs** | `subs(node, var, term)` | O(n) | Alias for substitute |

**Code location:** `lib/substitute.js:1-60`

```javascript
// Line 23: Recursive traversal with copy
return new Node(val.id, val.vals.map(v => {
  return typeof(v) === "object" ? substitute(v, x_, w) : v;
}))
```

**Key issue:** Creates new nodes on every call — no structural sharing.

### 1.5 Comparison Operations (lib/compare.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **compare** | `compare(a, b, theta)` | O(n) | Structural comparison with unification |

**Code location:** `lib/compare.js:1-80`

Returns substitution (theta) for matching, or false if no match.

### 1.6 Proof Tree Operations (lib/pt.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **Create** | `new PT({conclusion, premisses})` | O(1) | Create proof tree node |
| **toTree** | `pt.toTree()` | O(m) | Convert to display tree |
| **toString** | `pt.toString(style)` | O(m·n) | Render proof tree |

**Code location:** `lib/pt.js:1-160`

### 1.7 Proof Search Operations (lib/proofstate.js, lib/prover.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **auto** | `Proofstate.auto(pt, opts)` | Exponential | Full proof search |
| **getInvertibleRule** | (prover) | O(m) | Find invertible rule |
| **chooseFocus** | (prover) | O(m) | Choose formula to focus on |
| **applyRule** | (prover) | O(n) | Apply inference rule |
| **tryIdentityPositive** | (prover) | O(m·n) | Try Id+ rule |
| **tryIdentityNegative** | (prover) | O(n) | Try Id- rule |
| **continueProof** | (prover) | Recursive | Continue on premises |

**Code locations:**
- `lib/proofstate.js:1-400` — Main proof search loop
- `lib/prover.js:1-530` — Focused prover implementation

---

## Part 2: Call Graph Analysis

### 2.1 Proof Search Call Tree

```
Proofstate.auto(pt)
├── Sequent.getFreeVariables(seq)          [O(n)]
├── prover.getInvertibleRule(pt)           [O(m)]
│   ├── getPolarity(formula)               [O(1)]
│   └── isAtomic(formula)                  [O(1)]
├── prover.chooseFocus(pt)                 [O(m)]
├── prover.applyRule(pt, ruleName, ...)    [O(n)]
│   ├── mgu([[conclusionConnective, ...]])  [O(n²)]
│   │   ├── toString() comparisons          [O(n) × k]
│   │   └── substitute() calls              [O(n) × k]
│   ├── Sequent.substitute(theta)           [O(n·k)]
│   └── new PT({conclusion: seq})           [O(1)]
├── prover.tryIdentityPositive(pt)         [O(m·n)]
│   ├── mgu([[ctxFormula, formula]])        [O(n²)]
│   ├── substitute(succedent, k, v)         [O(n) × k]
│   └── Sequent.remove_from_antecedent()   [O(m)]
├── prover.continueProof(pt, ...)          [Recursive]
│   ├── seq.substitute(theta)               [O(n·k)]
│   ├── Sequent.add_to_antecedent_bulk()   [O(m·n)]
│   │   └── sha3(ast.toString())           [O(n) × m]
│   ├── Sequent.remove_structural_variables() [O(m)]
│   └── Proofstate.auto(premise)           [Recursive]
└── Rule application overhead
    ├── Ruleset.getRule(name)               [O(n) — renameUnique]
    └── seq.copy() for each premise         [O(n)]
```

### 2.2 Hotspot Identification

Based on call graph analysis, the **critical path** operations are:

| Rank | Operation | Frequency | Per-call Cost | Cumulative Impact |
|------|-----------|-----------|---------------|-------------------|
| 1 | `mgu()` | Every rule application | O(n²) | **CRITICAL** |
| 2 | `toString()` | Every mgu, every context op | O(n) | **CRITICAL** |
| 3 | `substitute()` | k times per mgu | O(n) | **HIGH** |
| 4 | `sha3(toString())` | Every context add | O(n) | **HIGH** |
| 5 | `copy()` | Every rule, every premise | O(n) | **MEDIUM** |
| 6 | `renameUnique()` | Every rule fetch | O(n) | **MEDIUM** |

---

## Part 3: Complexity Summary

> **See also:** [[content-addressed-formulas]] for Merkle-DAG optimization, [[backward-prover-optimization]] for optimization strategies.

### 3.1 Current vs Target Complexity

| Operation | Current | With Interning | Improvement |
|-----------|---------|----------------|-------------|
| Node equality | O(n) | O(1) | n× faster |
| Node copy | O(n) | O(1)* | n× faster |
| Context lookup | O(n) | O(1) | n× faster |
| Substitution | O(n) | O(n)** | Same (but shared) |
| MGU | O(n²) | O(n) | n× faster |
| Proof search | O(b^d · n²) | O(b^d · n) | n× faster |

\* With structural sharing, "copy" becomes reference copy
\** Substitution creates new interned nodes but shares subtrees

### 3.2 Estimated Frequency (per proof search)

For a proof of depth d with branching factor b:
- Rule applications: O(b^d)
- MGU calls: O(b^d)
- Substitutions: O(k · b^d) where k = avg variables per rule
- Context operations: O(m · b^d) where m = avg context size
- Copy operations: O(b · b^d) = O(b^(d+1))

**Example: Proving `(A * B) -o C |- A -o (B -o C)` (currying)**
- Depth: ~6 (Loli_R, Loli_R, Tensor_L, Loli_L, Id, Id)
- Branching: ~1.5 (some rules have choices)
- Estimated operations: ~20 rule applications, ~40 MGU calls, ~100 substitutions

---

## Implementation

For benchmark implementation, benchmark runner, and npm scripts, see `dev/optimization_strategies.md`.

---

## References

- [Benchmark.js](https://benchmarkjs.com/) — Statistical benchmarking library
- [Node.js perf_hooks](https://nodejs.org/api/perf_hooks.html) — Native performance APIs
- [V8 Performance Characteristics](https://github.com/davidmarkclements/v8-perf) — V8 optimization guide
- [The State of Benchmarking in Node.js](https://webpro.nl/articles/the-state-of-benchmarking-in-nodejs)
- [How JS Benchmarks Lie](https://medium.com/cacher-app/how-js-benchmarks-lie-fa35fa989ee0) — Pitfalls to avoid
- [micro-bmark](https://github.com/paulmillr/micro-bmark) — Nanosecond resolution benchmarking
- [V8 Orinoco GC](https://v8.dev/blog/trash-talk) — V8's garbage collector architecture
- [V8 Parallel Scavenger](https://v8.dev/blog/orinoco-parallel-scavenger) — Young generation GC
- [Object Pooling in Games](https://gameprogrammingpatterns.com/object-pool.html) — Game programming pattern
- [Static Memory JS](https://web.dev/articles/speed-static-mem-pools) — GC-free patterns
- [Zig Allocators](https://zig.guide/standard-library/allocators/) — Arena allocator guide
- [Hash consing - Wikipedia](https://en.wikipedia.org/wiki/Hash_consing) — Technique overview
- [Merkle DAG - IPFS](https://docs.ipfs.tech/concepts/merkle-dag/) — Content-addressed DAGs
- [ACL2 HONS-AND-MEMOIZATION](https://www.cs.utexas.edu/~moore/acl2/v6-3/HONS-AND-MEMOIZATION.html) — Theorem prover hash consing
- [Hash-Consing GC (Appel)](https://www.cs.princeton.edu/research/techreps/TR-412-93) — Generational integration
- [rapidhash](https://github.com/Nicoshev/rapidhash) — Fastest non-cryptographic hash
- [rapidhash-js](https://github.com/komiya-atsushi/rapidhash-js) — JavaScript implementation
- [SAT Solver Memory](https://link.springer.com/chapter/10.1007/978-3-540-30494-4_20) — Memory-efficient solving
- [SMHasher](https://github.com/rurban/smhasher) — Hash function quality tests
