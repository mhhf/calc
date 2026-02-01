# Explicit Substitutions: Lazy Evaluation for Proof Search

Deep dive into deferring substitution operations until actually needed.

---

## 1. The Problem: Eager Substitution is Expensive

### Current Substitution Pattern

In proof search, we frequently apply substitutions:

```javascript
// proofstate.js:267
theta.length > 0 && ptp.conclusion.substitute(theta);

// proofstate.js:279-285
theta = theta.map(([k, v]) => {
  let new_value = v;
  result.theta.forEach(([k_, v_]) => {
    new_value = substitute(new_value, k_, v_);
  });
  return [k, new_value];
});
```

### The Cost

Each `substitute(term, var, value)` call:
1. Traverses the entire term: O(n)
2. Creates new nodes for modified paths: O(n) allocations
3. Recomputes hashes (with Merkle-DAG): O(n)

For a sequent with m formulas, each of size n, applying k substitutions costs: **O(m · k · n)**

### The Waste

Many substituted terms are **never actually inspected**:
- Failed proof branches discard all their work
- Intermediate sequents during inversion phase often just pass through
- Identity rule only looks at the goal and one context formula

**Observation:** We might substitute through 100 formulas just to ultimately read 2 of them.

---

## 2. Explicit Substitutions: Core Concept

### Traditional Substitution (Eager)

```
substitute(f(X, g(X)), X, a) = f(a, g(a))
```

The substitution is **immediately applied**, creating a new term.

### Explicit Substitution (Lazy)

```
f(X, g(X))[X := a]
```

The substitution is **recorded but not applied**. The term `f(X, g(X))[X := a]` is itself a valid term that **represents** `f(a, g(a))` but doesn't materialize it yet.

### When to Force

The substitution is only applied ("forced") when we need to:
1. **Pattern match** on the term structure
2. **Hash** the term (for memoization)
3. **Display** the term to the user
4. **Compare** with another term (though hash comparison doesn't require forcing)

---

## 3. Implementation: Closures

### The Closure Data Structure

A **closure** is a pair: (term, environment)

```javascript
class Closure {
  constructor(termHash, env) {
    this.termHash = termHash;  // Original term (hash in Merkle-DAG)
    this.env = env;            // Map: varHash → valueHash
    this._forcedHash = null;   // Cached forced result
  }

  // Check if there are pending substitutions
  hasPendingSubstitutions() {
    return this.env.size > 0;
  }

  // Compose with another substitution
  // [X := a][Y := b] → closure with {X: a, Y: b}
  compose(otherEnv) {
    if (otherEnv.size === 0) return this;
    if (this.env.size === 0) {
      return new Closure(this.termHash, otherEnv);
    }

    // Merge environments, applying new substitution to existing values
    const newEnv = new Map();
    for (const [k, v] of this.env) {
      // Apply otherEnv to v
      const vClosure = new Closure(v, otherEnv);
      newEnv.set(k, vClosure.force(store));  // Need to force here
    }
    for (const [k, v] of otherEnv) {
      if (!newEnv.has(k)) {
        newEnv.set(k, v);
      }
    }

    return new Closure(this.termHash, newEnv);
  }

  // Force: actually apply the substitution
  force(store) {
    if (this._forcedHash !== null) {
      return this._forcedHash;
    }

    if (this.env.size === 0) {
      this._forcedHash = this.termHash;
      return this._forcedHash;
    }

    // Apply substitution
    this._forcedHash = forceSubstitute(store, this.termHash, this.env);
    return this._forcedHash;
  }
}

// Actually perform substitution (recursive)
function forceSubstitute(store, termHash, env) {
  // Check if this term is a variable being substituted
  if (env.has(termHash)) {
    return env.get(termHash);
  }

  // If not structural, return as-is
  if (!store.isStructural(termHash)) {
    return termHash;
  }

  const data = store.getStructural(termHash);

  // Check if any children need substitution
  let anyChanged = false;
  const newChildren = data.children.map(childHash => {
    const newChild = forceSubstitute(store, childHash, env);
    if (newChild !== childHash) anyChanged = true;
    return newChild;
  });

  if (!anyChanged) {
    return termHash;  // Return original (structural sharing!)
  }

  // Create new term with substituted children
  return store.internStructural(data.constructorId, newChildren);
}
```

---

## 4. Sequent with Closures

### Modified Sequent Structure

```javascript
class LazySequent {
  constructor(params) {
    this.persistent_ctx = params.persistent_ctx || new Map();  // hash → Closure
    this.linear_ctx = params.linear_ctx || new Map();          // hash → {num, closure}
    this.succedent = params.succedent;  // Closure
    this.store = params.store;
  }

  // Apply substitution lazily - O(1)!
  substitute(theta) {
    const env = new Map(theta.map(([k, v]) => [k.hash || k, v.hash || v]));

    return new LazySequent({
      persistent_ctx: mapValues(this.persistent_ctx, c => c.compose(env)),
      linear_ctx: mapValues(this.linear_ctx, ({num, closure}) =>
        ({num, closure: closure.compose(env)})),
      succedent: this.succedent.compose(env),
      store: this.store
    });
  }

  // Force all closures (for display or final result)
  force() {
    return new Sequent({
      persistent_ctx: mapValues(this.persistent_ctx, c => c.force(this.store)),
      linear_ctx: mapValues(this.linear_ctx, ({num, closure}) =>
        ({num, val: extern(closure.force(this.store), this.store)})),
      succedent: extern(this.succedent.force(this.store), this.store),
    });
  }

  // Get succedent formula (forces only succedent)
  getSuccedent() {
    return this.succedent.force(this.store);
  }

  // Get a context formula (forces only that formula)
  getContextFormula(id) {
    return this.linear_ctx.get(id)?.closure.force(this.store);
  }
}
```

### Key Insight

**Substitution becomes O(1)** — just compose environments!

The actual O(n) work is deferred until `force()` is called.

---

## 5. When to Force: Strategic Forcing

### Operations That DON'T Need Forcing

| Operation | Why No Forcing Needed |
|-----------|----------------------|
| Copy sequent | Just copy closures |
| Apply substitution | Compose environments |
| Add to context | Add closure as-is |
| Remove from context | Remove closure as-is |
| Check if empty | Check closure count |

### Operations That DO Need Forcing

| Operation | Why Forcing Needed |
|-----------|-------------------|
| Unification | Need actual structure to unify |
| Pattern match (rule application) | Need to see connective |
| Identity check | Need formula hash |
| Display to user | Need readable form |
| Memoization key | Need canonical hash |

### Strategic Design

```javascript
// In proof search
function tryIdentity(seq) {
  // Force only the succedent (need to check its structure)
  const goalHash = seq.getSuccedent();

  // Try exact match first (O(1) if ground)
  const exactMatch = seq.linear_ctx.findByHash(goalHash);
  if (exactMatch) {
    return success(exactMatch);
  }

  // Only now force candidates for unification
  const candidates = seq.linear_ctx.getCandidatesByConstructor(goalHash);
  for (const candidate of candidates) {
    const candidateHash = candidate.closure.force(seq.store);  // Force here
    const theta = mgu(candidateHash, goalHash);
    if (theta) return success(candidate, theta);
  }

  return failure();
}
```

---

## 6. Concrete Example

### Scenario

```
Proof search: (A ⊗ B) ⊗ C, D -o E |- F

Step 1: Inversion on succedent (assume F is negative)
  - Substitute: ?X → G
  - Context formulas: unchanged (still closures)

Step 2: Apply Loli_R
  - Add D to context
  - Substitute: ?Y → H
  - Context: still closures with composed environments

Step 3: Focus on left
  - Only NOW force the focused formula

Step 4: Decompose (A ⊗ B) ⊗ C
  - Force this formula, get A, B, C

Step 5: Fail branch
  - Discard everything
  - NONE of D -o E was ever forced!
```

### Cost Comparison

**Without lazy substitution:**
```
Step 1: substitute through 2 formulas: O(2n)
Step 2: substitute through 3 formulas: O(3n)
Total before fail: O(5n)
```

**With lazy substitution:**
```
Step 1: compose env: O(1)
Step 2: compose env: O(1)
Step 3: force 1 formula: O(n)
Total before fail: O(n)
```

**Savings: 5× fewer term traversals!**

For deeper proofs with more substitutions, savings compound.

---

## 7. Integration with Merkle-DAG

### Hash of Closure

The hash of a closure should be the hash of its **forced form**, but we want to delay computing it.

**Option 1: Force on hash request**
```javascript
class Closure {
  get hash() {
    return this.force(this.store);  // Returns hash of forced term
  }
}
```

**Option 2: Separate "weak hash" for memoization**
```javascript
class Closure {
  // Hash that includes environment (for identity, not content)
  get weakHash() {
    return hashCombine(this.termHash, hashEnv(this.env));
  }

  // True content hash (requires forcing)
  get contentHash() {
    return this.force(this.store);
  }
}
```

### Structural Sharing with Closures

When forcing, we can share structure with the original term:

```javascript
function forceSubstitute(store, termHash, env) {
  // ... as above ...

  if (!anyChanged) {
    return termHash;  // SAME hash - structural sharing!
  }

  // Only changed subtrees are new
  return store.internStructural(data.constructorId, newChildren);
}
```

---

## 8. Complexity Analysis

### Per-Operation Costs

| Operation | Eager | Lazy |
|-----------|-------|------|
| Substitute | O(n) | O(1) |
| Compose substitutions | O(n) | O(k) where k = env size |
| Force | N/A | O(n) |
| Copy sequent | O(m·n) | O(m) |

### Full Proof Search

Let:
- d = proof depth
- b = branching factor
- m = avg context size
- n = avg formula size
- s = substitutions per step

**Eager:**
```
Total substitution work = d × b × m × s × n = O(d·b·m·s·n)
```

**Lazy:**
```
Substitution work = d × b × s × O(1) = O(d·b·s)  // Just composing
Forcing work = d × (# forced formulas) × n
            = d × O(1) × n = O(d·n)  // Only force what we need!
Total = O(d·b·s + d·n)
```

**Speedup:**
```
Eager / Lazy = (d·b·m·s·n) / (d·b·s + d·n)
             ≈ m·n for large proofs
             ≈ 20 × 10 = 200× for typical values!
```

---

## 9. Edge Cases and Challenges

### Challenge 1: Environment Growth

If we keep composing without forcing, environments can grow large.

**Solution: Periodic forcing threshold**
```javascript
class Closure {
  compose(newEnv) {
    const combined = this._compose(newEnv);
    if (combined.env.size > MAX_ENV_SIZE) {
      // Force and reset to avoid unbounded growth
      return new Closure(combined.force(store), new Map());
    }
    return combined;
  }
}
```

### Challenge 2: Sharing Detection

With closures, `closure1.termHash === closure2.termHash` doesn't mean they're equal if environments differ.

**Solution: Compare contentHash when equality matters**
```javascript
function closuresEqual(c1, c2, store) {
  // Quick check: same term and same env
  if (c1.termHash === c2.termHash && envEqual(c1.env, c2.env)) {
    return true;
  }
  // Slow check: force and compare
  return c1.force(store) === c2.force(store);
}
```

### Challenge 3: Variable Capture

Substituting might capture free variables if not careful.

**Solution: Use de Bruijn indices or careful scoping**
- Our system uses unique variable names (V_0, V_1, ...)
- `renameUnique` ensures no capture
- With Merkle-DAG hashes, variables are globally unique

### Challenge 4: Debugging

Closures make debugging harder since you don't see the "real" term.

**Solution: Debug helper**
```javascript
class Closure {
  inspect() {
    return {
      term: extern(this.termHash, store).toString(),
      env: [...this.env].map(([k, v]) =>
        `${extern(k, store)} → ${extern(v, store)}`),
      forced: this._forcedHash ? extern(this._forcedHash, store).toString() : null
    };
  }
}
```

---

## 10. Recommendation

### Verdict: **DEFER** (implement if benchmarks show need)

**Priority:** LOW-MEDIUM

**Effort:** HIGH

### Rationale

**Pros:**
1. Significant theoretical speedup (up to 200× fewer traversals)
2. Natural fit with lazy evaluation mindset
3. Reduces allocation pressure

**Cons:**
1. Adds complexity throughout codebase
2. Every operation must handle closures
3. Debugging becomes harder
4. Need careful handling of forcing points
5. May not help if most formulas ARE inspected

### When It's Worth It

- Proofs with **high backtracking** (many failed branches)
- Proofs with **many substitutions** that don't get inspected
- Proofs with **large context** but focused inspection

### When It's NOT Worth It

- Small proofs where everything gets inspected anyway
- Interactive proving where user sees every step
- When other optimizations (hash equality, memoization) already dominate

### Recommended Approach

1. **First:** Implement other optimizations (hash equality, memoization, constructor index)
2. **Then:** Benchmark real workloads
3. **Measure:** What % of substituted terms are never forced?
4. **If > 50%:** Implement lazy substitution
5. **If < 50%:** Skip (overhead not worth it)

### Partial Implementation

If benchmarks show benefit, start with **lazy sequent copy** only:

```javascript
// Instead of deep copying everything:
Sequent.lazyCopy = function(seq) {
  return {
    linear_ctx: seq.linear_ctx,     // Share reference
    persistent_ctx: seq.persistent_ctx,
    succedent: seq.succedent,
    _pendingTheta: [],              // Record substitutions
    _original: seq,
  };
}

// Only materialize when modifying
Sequent.materializeOnWrite = function(lazySeq, modifyFn) {
  const materialized = Sequent.copy(lazySeq._original);
  lazySeq._pendingTheta.forEach(theta => materialized.substitute(theta));
  return modifyFn(materialized);
}
```

This gives 80% of the benefit with 20% of the complexity.

---

## 11. References

- [Explicit substitutions - nLab](https://ncatlab.org/nlab/show/explicit+substitution)
- [Explaining the lazy Krivine machine using explicit substitution](https://link.springer.com/article/10.1007/s10990-007-9013-1)
- [Closures - Wikipedia](https://en.wikipedia.org/wiki/Closure_(computer_programming))
- [Environment Model of Operational Semantics](https://bguppl.github.io/interpreters/class_material/2.7EnvironmentModel.html)
- [Abadi, Cardelli, Curien & Lévy - Explicit Substitutions (1991)](https://dl.acm.org/doi/10.1145/96709.96712)
