---
title: "Near-Linear Unification: Martelli-Montanari with Union-Find"
created: 2026-02-10
modified: 2026-02-10
summary: Optimization from O(n²) Robinson unification to O(n·α(n)) using Martelli-Montanari algorithm with union-find for near-linear performance.
tags: [unification, optimization, union-find, algorithms, Martelli-Montanari]
---

# Near-Linear Unification: Martelli-Montanari with Union-Find

Deep dive into upgrading from O(n²) Robinson unification to O(n·α(n)) Martelli-Montanari.

> **See also:** [[content-addressed-formulas]] for Merkle-DAG hash consing enabling O(1) equality, [[backward-prover-optimization]] for overall optimization strategy, [[benchmarking]] for performance analysis.

---

## Table of Contents

1. [Current Implementation Analysis](#1-current-implementation-analysis)
2. [The Martelli-Montanari Algorithm](#2-the-martelli-montanari-algorithm)
3. [Union-Find Data Structure](#3-union-find-data-structure)
4. [Near-Linear Unification with Union-Find](#4-near-linear-unification-with-union-find)
5. [Detailed Implementation for CALC](#5-detailed-implementation-for-calc)
6. [Comparison: Before and After](#6-comparison-before-and-after)
7. [Integration with Merkle-DAG](#7-integration-with-merkle-dag)
8. [Edge Cases and Considerations](#8-edge-cases-and-considerations)
9. [Recommendation](#9-recommendation)
10. [References](#10-references)

---

## 1. Current Implementation Analysis

### Current `mgu.js` Implementation

```javascript
const mgu = function (G) {
  let rules = Calc.db.rules;
  var theta = [];

  while (G.length > 0) {
    let job = G.pop();
    let t0 = job[0];
    let t1 = job[1];

    let isEq = t0.toString() === t1.toString();  // O(n) per check!
    // ...

    if(isEq) {
      // delete - do nothing
    } else if(isVarL && isVarR) {
      G = [[t0, t1]].concat(G);  // Handle double-variable case
    } else if(isVarL) {
      // ELIMINATE: propagate substitution through theta AND G
      theta = propagate(theta, [[t0, t1]])  // O(k·n)
      G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))  // O(|G|·n)
    } else if(isVarR) {
      G.push([t1, t0]);  // SWAP
    } else if(isEqType && !isString) {
      // DECOMPOSE
      t0.vals.forEach((v, i) => {
        G.push([v, t1.vals[i]]);
      })
    } else {
      return false;  // CONFLICT
    }
  }
  return theta;
}
```

### Why It's O(n²)

1. **Equality check is O(n):** `t0.toString() === t1.toString()` converts entire AST to string

2. **Substitution propagation is O(|G|·n):** Every time we eliminate a variable, we substitute through ALL remaining equations

3. **Cascading effect:** For k variables, we do k eliminate steps, each touching up to n terms

**Worst case:** O(k · n · k) = O(k² · n) where k = variables, n = term size

For typical cases where k ∝ n: **O(n³)**

### Concrete Example

Unify: `f(?X, ?Y, ?Z) = f(a, ?X, ?Y)`

```
Step 1: Decompose
  G = [(?X, a), (?Y, ?X), (?Z, ?Y)]

Step 2: Eliminate ?X=a
  theta = [(?X, a)]
  Propagate: ?Y=?X becomes ?Y=a, ?Z=?Y stays
  G = [(?Y, a), (?Z, ?Y)]

Step 3: Eliminate ?Y=a
  theta = [(?X, a), (?Y, a)]
  Propagate: ?Z=?Y becomes ?Z=a
  G = [(?Z, a)]

Step 4: Eliminate ?Z=a
  theta = [(?X, a), (?Y, a), (?Z, a)]
  G = []
```

Each elimination propagates through remaining equations. With k variables, this is O(k²) propagations.

---

## 2. The Martelli-Montanari Algorithm

### Transformation Rules

The algorithm transforms a set of equations E using these rules until no rule applies:

| Rule | Pattern | Transformation | When |
|------|---------|----------------|------|
| **Delete** | `t = t` | Remove equation | Both sides identical |
| **Decompose** | `f(s₁,...,sₙ) = f(t₁,...,tₙ)` | `{s₁=t₁, ..., sₙ=tₙ}` | Same functor |
| **Conflict** | `f(...) = g(...)` | FAIL | Different functors |
| **Swap** | `t = X` | `X = t` | t is non-variable |
| **Eliminate** | `X = t` where X ∈ E | `E[X/t]` | X appears elsewhere |
| **Check** | `X = t` where X ∈ vars(t) | FAIL | Occurs check |

### Why It's Still Not Linear

The **Eliminate** rule still requires propagating substitutions, which is expensive.

**Key insight:** We can delay substitution by using **Union-Find** to track which terms are equivalent, rather than eagerly substituting.

---

## 3. Union-Find Data Structure

### Core Idea

Instead of substituting `X = t` everywhere, we record that X and t are in the same "equivalence class."

```
X ≡ t means: "X and t represent the same value"
```

Later, when we need the actual substitution, we can reconstruct it from the equivalence classes.

### Union-Find Operations

```javascript
class UnionFind {
  constructor() {
    this.parent = new Map();  // node → parent
    this.rank = new Map();    // node → rank (for balancing)
  }

  // Find the representative of x's equivalence class
  find(x) {
    if (!this.parent.has(x)) {
      return x;  // x is its own representative
    }
    // Path compression: make x point directly to root
    const root = this.find(this.parent.get(x));
    this.parent.set(x, root);
    return root;
  }

  // Unite the equivalence classes of x and y
  union(x, y) {
    const rootX = this.find(x);
    const rootY = this.find(y);

    if (rootX === rootY) return;  // Already in same class

    // Union by rank: attach smaller tree under larger
    const rankX = this.rank.get(rootX) || 0;
    const rankY = this.rank.get(rootY) || 0;

    if (rankX < rankY) {
      this.parent.set(rootX, rootY);
    } else if (rankX > rankY) {
      this.parent.set(rootY, rootX);
    } else {
      this.parent.set(rootY, rootX);
      this.rank.set(rootX, rankX + 1);
    }
  }
}
```

### Complexity

With **path compression** and **union by rank**:
- `find(x)`: Amortized O(α(n))
- `union(x, y)`: Amortized O(α(n))

Where α(n) is the **inverse Ackermann function**, which is ≤ 4 for any realistic n (up to 10^80).

**Effectively constant time!**

---

## 4. Near-Linear Unification with Union-Find

### Algorithm Sketch

```javascript
function mguLinear(s, t) {
  const uf = new UnionFind();
  const worklist = [[s, t]];

  while (worklist.length > 0) {
    let [a, b] = worklist.pop();

    // Find representatives
    a = uf.find(a);
    b = uf.find(b);

    if (a === b) continue;  // Already unified

    if (isVariable(a)) {
      if (occursIn(a, b)) return null;  // Occurs check
      uf.union(a, b);  // a now points to b
    } else if (isVariable(b)) {
      if (occursIn(b, a)) return null;
      uf.union(b, a);  // b now points to a
    } else if (functor(a) === functor(b)) {
      uf.union(a, b);
      // Add children to worklist
      for (let i = 0; i < arity(a); i++) {
        worklist.push([child(a, i), child(b, i)]);
      }
    } else {
      return null;  // Conflict
    }
  }

  return extractSubstitution(uf);
}
```

### Why This Is Near-Linear

1. **No eager substitution:** We union equivalence classes instead of substituting
2. **Each term visited once:** Each subterm enters worklist at most once
3. **Union-Find is O(α(n)):** Finding/unioning is effectively constant

**Total: O(n · α(n)) ≈ O(n)** where n = total term size

---

## 5. Detailed Implementation for CALC

### Data Structures

```javascript
// Represent terms by their hash (from Merkle-DAG)
// Union-Find operates on hashes

class TermUnionFind {
  constructor(store) {
    this.store = store;
    this.parent = new Map();  // hash → parentHash
    this.rank = new Map();    // hash → rank
    this.binding = new Map(); // varHash → termHash (for extracting substitution)
  }

  // Find representative, with path compression
  find(hash) {
    if (!this.parent.has(hash)) {
      return hash;
    }
    const root = this.find(this.parent.get(hash));
    if (this.parent.get(hash) !== root) {
      this.parent.set(hash, root);  // Path compression
    }
    return root;
  }

  // Union two terms
  // Returns false if conflict detected
  union(hash1, hash2) {
    const root1 = this.find(hash1);
    const root2 = this.find(hash2);

    if (root1 === root2) return true;  // Already same

    const isVar1 = this.store.isVariable(root1);
    const isVar2 = this.store.isVariable(root2);

    // Prefer non-variables as representatives
    if (isVar1 && !isVar2) {
      this.parent.set(root1, root2);
      this.binding.set(root1, root2);  // Record: var1 → term2
    } else if (isVar2 && !isVar1) {
      this.parent.set(root2, root1);
      this.binding.set(root2, root1);  // Record: var2 → term1
    } else if (isVar1 && isVar2) {
      // Both variables - union by rank
      const rank1 = this.rank.get(root1) || 0;
      const rank2 = this.rank.get(root2) || 0;
      if (rank1 < rank2) {
        this.parent.set(root1, root2);
        this.binding.set(root1, root2);
      } else if (rank1 > rank2) {
        this.parent.set(root2, root1);
        this.binding.set(root2, root1);
      } else {
        this.parent.set(root2, root1);
        this.binding.set(root2, root1);
        this.rank.set(root1, rank1 + 1);
      }
    } else {
      // Both non-variables - they must have same constructor
      const data1 = this.store.getStructural(root1);
      const data2 = this.store.getStructural(root2);

      if (data1.constructorId !== data2.constructorId) {
        return false;  // Conflict!
      }

      // Union and return children for further processing
      this.parent.set(root2, root1);
      return { children: zip(data1.children, data2.children) };
    }

    return true;
  }

  // Extract theta from bindings
  extractTheta(originalVars) {
    const theta = [];
    for (const varHash of originalVars) {
      const binding = this.binding.get(varHash);
      if (binding && binding !== varHash) {
        // Need to convert hash back to Node for compatibility
        // Or return hash-based theta for new system
        theta.push([varHash, this.find(binding)]);
      }
    }
    return theta;
  }
}
```

### Main Unification Function

```javascript
function mguFast(term1Hash, term2Hash, store) {
  const uf = new TermUnionFind(store);
  const worklist = [[term1Hash, term2Hash]];

  // Track variables for theta extraction
  const variables = new Set();
  collectVariables(term1Hash, store, variables);
  collectVariables(term2Hash, store, variables);

  while (worklist.length > 0) {
    const [h1, h2] = worklist.pop();

    // Find representatives
    const r1 = uf.find(h1);
    const r2 = uf.find(h2);

    if (r1 === r2) continue;  // Already unified

    // Occurs check for variables
    const isVar1 = store.isVariable(r1);
    const isVar2 = store.isVariable(r2);

    if (isVar1 && !isVar2 && occursIn(r1, r2, uf, store)) {
      return null;  // Occurs check failed
    }
    if (isVar2 && !isVar1 && occursIn(r2, r1, uf, store)) {
      return null;
    }

    // Union
    const result = uf.union(r1, r2);

    if (result === false) {
      return null;  // Conflict
    }

    if (result && result.children) {
      // Add children to worklist
      for (const [c1, c2] of result.children) {
        worklist.push([c1, c2]);
      }
    }
  }

  return uf.extractTheta(variables);
}

// Occurs check: does varHash appear in termHash?
function occursIn(varHash, termHash, uf, store) {
  const visited = new Set();
  const stack = [termHash];

  while (stack.length > 0) {
    const h = uf.find(stack.pop());

    if (h === varHash) return true;
    if (visited.has(h)) continue;
    visited.add(h);

    if (store.isStructural(h)) {
      const data = store.getStructural(h);
      for (const childHash of data.children) {
        stack.push(childHash);
      }
    }
  }

  return false;
}
```

---

## 6. Comparison: Before and After

### Before (Current mgu.js)

```
Unify: f(g(?X, ?Y), ?Z) = f(g(a, b), c)

Steps:
1. Decompose f: [g(?X,?Y)=g(a,b), ?Z=c]
2. Decompose g: [?X=a, ?Y=b, ?Z=c]
3. Eliminate ?X=a:
   - theta = [?X→a]
   - Propagate through G (no more ?X)
4. Eliminate ?Y=b:
   - theta = [?X→a, ?Y→b]
   - Propagate through G
5. Eliminate ?Z=c:
   - theta = [?X→a, ?Y→b, ?Z→c]
   - Propagate through G
6. Return theta

Operations: 3 decompositions + 3 eliminations × propagation work
Complexity: O(k²·n) where k=3 variables, n≈6 nodes
```

### After (Near-Linear)

```
Unify: f(g(?X, ?Y), ?Z) = f(g(a, b), c)

Steps:
1. Worklist: [(f(...), f(...))]
2. Pop, same constructor, union, add children
   Worklist: [(g(?X,?Y), g(a,b)), (?Z, c)]
3. Pop (g,g), same constructor, union, add children
   Worklist: [(?X,a), (?Y,b), (?Z,c)]
4. Pop (?X,a), variable, union ?X→a in O(1)
   Worklist: [(?Y,b), (?Z,c)]
5. Pop (?Y,b), variable, union ?Y→b in O(1)
   Worklist: [(?Z,c)]
6. Pop (?Z,c), variable, union ?Z→c in O(1)
   Worklist: []
7. Extract theta from bindings

Operations: 6 union/find operations, each O(α(n))
Complexity: O(n·α(n)) ≈ O(n)
```

### Speedup Analysis

| Scenario | Before | After | Speedup |
|----------|--------|-------|---------|
| 3 vars, size 10 | O(90) | O(10) | ~9× |
| 5 vars, size 20 | O(500) | O(20) | ~25× |
| 10 vars, size 50 | O(5000) | O(50) | ~100× |

The speedup increases with more variables and larger terms!

---

## 7. Integration with Merkle-DAG

### Hash-Based Unification

With content-addressed terms, we unify **hashes** directly:

```javascript
// In store, add helper method
class Store {
  // Check if hash represents a variable
  isVariable(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.STRUCT) return false;
    const data = this.getStructural(hash);
    const ruleId = data.constructorId;
    return Calc.db.rules[ruleId]?.ruleName.endsWith('_Freevar');
  }
}
```

### O(1) Equality Check

**Before:**
```javascript
let isEq = t0.toString() === t1.toString();  // O(n)
```

**After:**
```javascript
let isEq = h0 === h1;  // O(1) - just compare BigInt hashes!
```

This alone gives n× speedup on the equality check in the main loop!

---

## 8. Edge Cases and Considerations

### Occurs Check Cost

The occurs check (`occursIn`) is O(n) in the worst case because it must traverse the term.

**Optimization:** With Merkle-DAG, we can cache "contains variable" information:

```javascript
// During term interning, compute and cache
class Store {
  internStructural(constructorId, childHashes) {
    const hash = this.hashStructural(constructorId, childHashes);
    // ...
    // Also compute: does this term contain any variables?
    const containsVars = childHashes.some(ch => this.containsVars(ch));
    this._containsVars.set(hash, containsVars);
    return hash;
  }

  containsVars(hash) {
    if (this.isVariable(hash)) return true;
    return this._containsVars.get(hash) || false;
  }
}
```

Then occurs check becomes:
```javascript
function occursIn(varHash, termHash, uf, store) {
  if (!store.containsVars(termHash)) return false;  // O(1) shortcut!
  // ... full check only if term contains variables
}
```

### Variable Renaming

Current code does `renameUnique` before unification. With hash-based unification:

- Variables with same name but different scopes get different hashes
- No explicit renaming needed if we track scope during interning

### Compatibility with Existing Code

For backwards compatibility, provide wrapper:

```javascript
// Wrapper that converts Node-based API to hash-based
function mguCompat(pairs) {
  const store = getGlobalStore();
  const hashPairs = pairs.map(([t0, t1]) => [
    t0.hash || intern(t0, store),
    t1.hash || intern(t1, store)
  ]);

  const thetaHashes = mguFast(hashPairs[0][0], hashPairs[0][1], store);
  if (!thetaHashes) return false;

  // Convert back to Node-based theta
  return thetaHashes.map(([varHash, termHash]) => [
    extern(varHash, store),
    extern(termHash, store)
  ]);
}
```

---

## 9. Recommendation

### Verdict: **IMPLEMENT** (with caveats)

**Priority:** MEDIUM-HIGH

**Effort:** MEDIUM

### Rationale

**Pros:**
1. O(n²) → O(n) is significant for large terms
2. Integrates well with Merkle-DAG (hash-based equality)
3. Standard algorithm, well-understood
4. Enables other optimizations (e.g., O(1) equality check)

**Cons:**
1. More complex implementation than current
2. Need to handle theta extraction carefully
3. Backwards compatibility requires wrapper
4. For small terms (n < 20), overhead might exceed benefit

### When to Use

- **Small terms (n < 20):** Current algorithm is fine, simpler
- **Medium terms (20 < n < 100):** Near-linear gives 10-50× speedup
- **Large terms (n > 100):** Near-linear is essential

### Implementation Strategy

**Phase 1:** Keep current mgu, add O(1) hash equality (biggest quick win)
```javascript
// Just change this line in current mgu:
let isEq = t0.hash === t1.hash;  // Instead of toString comparison
```
This alone gives ~n× speedup.

**Phase 2:** Full near-linear implementation when benchmarks show need

---

## 10. References

- [Martelli & Montanari - An Efficient Unification Algorithm (1982)](https://dl.acm.org/doi/10.1145/357162.357169)
- [Disjoint-set data structure - Wikipedia](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
- [Union-Find complexity proof](https://codeforces.com/blog/entry/98275)
- [A unification algorithm - CMI lecture notes](https://www.cmi.ac.in/~madhavan/courses/pl2009/lecturenotes/lecture-notes/node113.html)
- [Unification (computer science) - Wikipedia](https://en.wikipedia.org/wiki/Unification_(computer_science))
