# Backward Prover Optimization Analysis

## Problem Statement

The backward chaining prover in `lib/mde/prove.js` uses significant computation on substitution operations. Analysis of `plus 20 118 X` shows:

| Operation | % of Store.get | Calls | Gets/call |
|-----------|----------------|-------|-----------|
| subApply  | 56.4%          | 19    | 118       |
| unify     | 33.9%          | 20    | 67        |
| freshen   | 7.5%           | 20    | 15        |

**Root cause**: Sequential substitution and quadratic theta maintenance.

## Detailed Analysis

### 1. Sequential Substitution Problem

In `lib/v2/kernel/substitute.js:70`:
```javascript
const apply = (h, theta) => theta.reduce((acc, [v, val]) => sub(acc, v, val), h);
```

For a term with M nodes and theta with N bindings:
- Each `sub()` traverses the entire term: O(M) Store.get calls
- Sequential application: N traversals total
- **Complexity: O(N × M)**

Example: `apply(bigTerm, theta)` where |theta| = 12, |term| = 10 nodes → 120+ gets.

### 2. Quadratic Theta Maintenance in Unify

In `lib/v2/kernel/unify.js:72-74`:
```javascript
// When binding new variable t0 → t1:
theta = [...theta.map(([v, x]) => [v, sub(x, t0, t1)]), [t0, t1]];
G.forEach((g, i) => { G[i] = [sub(g[0], t0, t1), sub(g[1], t0, t1)]; });
```

Every new binding triggers:
1. Apply new substitution to ALL existing bindings
2. Apply new substitution to ALL remaining goals

With K bindings total, this is O(K²) substitution applications.

### 3. Depth-Dependent Growth

Analysis of `plus 5 3 X`:

| Depth | Avg theta size | Apply gets/call | Unify gets/call |
|-------|----------------|-----------------|-----------------|
| 0     | 0              | 0               | 70              |
| 1     | 5.5            | 55              | 57              |
| 2     | 8              | 62              | 44              |
| 3     | 12             | 60              | 17              |

Theta grows with depth → apply cost grows linearly.

## Optimization Strategies

### Strategy 1: Simultaneous Substitution (Easy, High Impact)

**Current**: Apply each binding sequentially, traversing term N times.
**Better**: Single traversal applying all bindings at once.

```javascript
const applySimultaneous = (h, theta) => {
  if (theta.length === 0) return h;
  const varMap = new Map(theta);  // O(N) build, O(1) lookup

  function go(hash) {
    if (varMap.has(hash)) return varMap.get(hash);
    const node = Store.get(hash);
    if (!node) return hash;

    let changed = false;
    const newChildren = node.children.map(c => {
      if (Store.isTermChild(c)) {
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
**Expected speedup**: 5-10x for apply operations

**Caveat**: This is correct only if variables in theta don't reference each other. Need to verify usage.

### Strategy 2: Triangular Substitution (Medium, High Impact)

**Current**: Maintain idempotent MGU (variables fully resolved in theta).
**Better**: Triangular form - only store raw bindings, resolve on demand.

```javascript
// Walk a variable through the substitution chain
const walk = (h, theta) => {
  const binding = theta.find(([v]) => v === h);
  if (binding) return walk(binding[1], theta);
  return h;
};

// Full walk - resolve all variables in term
const walkFully = (h, theta) => {
  const walked = walk(h, theta);
  const node = Store.get(walked);
  if (!node) return walked;

  let changed = false;
  const newChildren = node.children.map(c => {
    if (Store.isTermChild(c)) {
      const nc = walkFully(c, theta);
      if (nc !== c) changed = true;
      return nc;
    }
    return c;
  });
  return changed ? Store.intern(node.tag, newChildren) : walked;
};
```

In unify, just push new bindings:
```javascript
if (isMetavar(t0)) {
  if (occurs(t0, t1, theta)) return null;
  theta.push([t0, t1]);  // Don't apply to existing theta!
  continue;
}
```

**Benefit**: Adding binding is O(1), not O(K × M).
**Cost**: Walk chains on lookup. Use path compression to amortize.

### Strategy 3: Union-Find with Path Compression (Hard, Highest Impact)

Standard technique in efficient Prolog implementations.

```javascript
class UnionFind {
  constructor() {
    this.parent = new Map();  // var → var or term
    this.rank = new Map();
  }

  find(v) {
    if (!this.parent.has(v)) return v;
    const p = this.parent.get(v);
    if (!isMetavar(p)) return p;  // Bound to term
    const root = this.find(p);
    if (root !== p) this.parent.set(v, root);  // Path compression
    return root;
  }

  union(v, term) {
    const rv = this.find(v);
    if (rv === term) return true;
    if (isMetavar(rv)) {
      this.parent.set(rv, term);
      return true;
    }
    return false;  // Already bound to something else
  }
}
```

**Complexity**: O(α(N)) amortized per operation (nearly constant).

### Strategy 4: Memoization Within Proof (Easy, Medium Impact)

Cache expensive operations within a single proof search:

```javascript
const proveWithMemo = (goal, ...) => {
  const applyCache = new Map();  // (h, thetaId) → result
  let thetaVersion = 0;

  function memoApply(h, theta) {
    const key = h + ':' + thetaVersion;
    if (applyCache.has(key)) return applyCache.get(key);
    const result = applySimultaneous(h, theta);
    applyCache.set(key, result);
    return result;
  }

  // Increment thetaVersion when theta changes
  // ...
};
```

### Strategy 5: Lazy/Explicit Substitution (Hard, Variable Impact)

Represent suspended substitutions as closures:
```javascript
// Instead of eagerly applying:
const goalInst = apply(goal, theta);

// Represent as closure:
const goalInst = { term: goal, env: theta };

// Only force when needed for comparison
const force = (closure) => walkFully(closure.term, closure.env);
```

This is the foundation for explicit substitution calculi. Complex but powerful.

## Recommended Implementation Order

1. **Simultaneous substitution** - Easy win, just change `apply()`. Test that variable-to-variable bindings work correctly.

2. **Triangular unification** - Remove the quadratic theta update in unify. Requires changing how we use theta downstream.

3. **Memoization** - Add caching for repeated apply calls on same terms.

4. **Union-find** - If above isn't enough, implement full UF with path compression.

## Expected Results

| Strategy | Implementation | Expected Speedup |
|----------|---------------|------------------|
| Simultaneous sub | 1 hour | 2-5x on apply |
| Triangular unify | 2 hours | 2-3x on unify |
| Memoization | 1 hour | 1.5x overall |
| Union-find | 4 hours | 3-5x overall |

Combined: **5-15x speedup** on backward chaining operations.
