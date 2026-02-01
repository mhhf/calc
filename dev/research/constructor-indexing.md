# O(1) Identity via Constructor Indexing

Deep dive into accelerating the identity rule from O(m·n²) to O(1) for ground formulas.

---

## 1. The Problem: Identity Rule is the Hot Path

### Current Identity Rule Implementation

From `prover.js:202-229` (tryIdentityPositive):

```javascript
tryIdentityPositive(pt, state) {
    const formula = pt.conclusion.succedent.vals[1];  // Goal: find this in context
    const ctx = pt.conclusion.linear_ctx;

    let theta;
    // TRY EVERY FORMULA IN CONTEXT until one matches!
    const matchId = Object.keys(ctx).find(id => {
        const ctxFormula = ctx[id].val.vals[1];
        theta = mgu([[ctxFormula, formula]]);  // O(n²) per attempt!
        return !!theta;
    });

    if (!matchId) return false;
    // ... consume formula ...
}
```

### Why This Is Slow

1. **Linear scan:** `Object.keys(ctx).find(...)` iterates through ALL context formulas
2. **Expensive comparison:** Each `mgu()` call is O(n²) due to:
   - `t0.toString() === t1.toString()` on line 23 of mgu.js (O(n))
   - Substitution propagation in `propagate()` (O(k·n))
   - Recursive decomposition

### Complexity Analysis

| Variable | Meaning | Typical Value |
|----------|---------|---------------|
| m | Context size (number of formulas) | 5-20 |
| n | Formula size (AST nodes) | 10-50 |
| k | Variables in unification | 2-10 |

**Current complexity per identity attempt:**
- Loop: O(m) iterations
- Per iteration: O(n²) for mgu
- **Total: O(m · n²)**

For m=10, n=20: **O(4000)** operations per identity check!

---

## 2. The Key Insight: Unification Prerequisites

### When Can Two Formulas Unify?

For `formula1` and `formula2` to unify:
1. **Same outermost constructor** (or one is a variable)
2. Corresponding subterms must unify recursively

### Example: What CAN Unify

```
A ⊗ B     can unify with    ?X ⊗ C      (same constructor ⊗)
A ⊗ B     can unify with    ?X          (variable matches anything)
A         can unify with    A           (same atom)
A         can unify with    ?X          (variable matches anything)
```

### Example: What CANNOT Unify

```
A ⊗ B     CANNOT unify with    A -o B    (different constructors: ⊗ vs -o)
A ⊗ B     CANNOT unify with    A & B     (different constructors: ⊗ vs &)
A ⊗ B     CANNOT unify with    A         (compound vs atom)
```

### The Optimization Principle

> **If the outermost constructors differ, don't even try to unify!**

By indexing formulas by their outermost constructor, we can **filter out impossible candidates** before attempting expensive unification.

---

## 3. Constructor Index Design

### Data Structure

```javascript
class ContextIndex {
    constructor(store) {
        this.store = store;

        // Primary index: hash → entry (for exact ground match)
        this.byHash = new Map();

        // Secondary index: constructorId → [entries] (for unification filtering)
        this.byConstructor = new Map();

        // Tertiary index: variable entries (match anything)
        this.variables = [];
    }
}
```

### Index Entry Structure

```javascript
// An entry in the index
{
    hash: BigInt,        // Content hash of the formula
    constructorId: number,  // Outermost constructor (e.g., 5 for ⊗)
    ctxId: string,       // Key in linear_ctx
    entry: {             // Original context entry
        num: number,
        val: Node
    }
}
```

### Building the Index

```javascript
class ContextIndex {
    // Add a formula to the index
    add(ctxId, entry, store) {
        const formula = entry.val.vals[1];  // Extract formula from structure
        const hash = formula.hash || computeHash(formula, store);
        const type = Calc.db.rules[formula.id];
        const constructorId = formula.id;
        const isVariable = type.ruleName.endsWith('_Freevar');

        const indexEntry = { hash, constructorId, ctxId, entry };

        // Add to primary index (by hash)
        this.byHash.set(hash, indexEntry);

        // Add to secondary index (by constructor) or variables
        if (isVariable) {
            this.variables.push(indexEntry);
        } else {
            if (!this.byConstructor.has(constructorId)) {
                this.byConstructor.set(constructorId, []);
            }
            this.byConstructor.get(constructorId).push(indexEntry);
        }
    }

    // Remove a formula from the index
    remove(ctxId) {
        // ... implementation ...
    }
}
```

---

## 4. Fast Identity Lookup

### Case 1: Ground Formula (No Variables) — O(1)

If the goal formula has no variables, we can use **direct hash lookup**:

```javascript
findExactMatch(goalHash) {
    // O(1) hash lookup!
    return this.byHash.get(goalHash) || null;
}
```

**Example:**
```
Goal: A ⊗ B
Context: [A ⊗ B, C -o D, E]

Hash(A ⊗ B) = 0x12AB...
byHash.get(0x12AB...) → {ctxId: "abc", entry: ...}

Found in O(1)!
```

### Case 2: Goal Has Variables — O(c + v)

If the goal has variables, we need to try unification, but only with:
1. Formulas with the **same outermost constructor** (c candidates)
2. **Variable formulas** in context (v candidates, usually 0)

```javascript
findUnifiable(goalFormula, store) {
    const goalType = Calc.db.rules[goalFormula.id];
    const goalConstructorId = goalFormula.id;
    const goalIsVariable = goalType.ruleName.endsWith('_Freevar');

    // If goal is a variable, it unifies with anything
    if (goalIsVariable) {
        // Return first context formula (or use some heuristic)
        return this.getFirst();
    }

    // Get candidates with same constructor
    const candidates = this.byConstructor.get(goalConstructorId) || [];

    // Also include variable formulas in context (they match anything)
    const allCandidates = [...candidates, ...this.variables];

    // Now try unification only with candidates
    for (const candidate of allCandidates) {
        const theta = mgu([[candidate.entry.val.vals[1], goalFormula]]);
        if (theta) {
            return { ...candidate, theta };
        }
    }

    return null;
}
```

### Complexity Comparison

| Scenario | Current | With Index | Speedup |
|----------|---------|------------|---------|
| Ground formula in context | O(m · n²) | **O(1)** | **m · n² ×** |
| Ground formula NOT in context | O(m · n²) | **O(1)** | **m · n² ×** |
| Goal with variables, c candidates | O(m · n²) | O(c · n²) | **m/c ×** |
| Goal is variable | O(m · n²) | O(1) | **m · n² ×** |

Where:
- m = total context formulas
- c = formulas with same constructor (typically c << m)
- n = formula size

---

## 5. Concrete Example

### Context

```
Linear context:
  1. A ⊗ B        (constructor: Tensor)
  2. C -o D       (constructor: Loli)
  3. E & F        (constructor: With)
  4. G ⊗ H        (constructor: Tensor)
  5. I            (constructor: Atprop)
```

### Index After Building

```javascript
byHash = {
    hash(A⊗B): { ctxId: "1", constructorId: TENSOR, ... },
    hash(C-oD): { ctxId: "2", constructorId: LOLI, ... },
    hash(E&F): { ctxId: "3", constructorId: WITH, ... },
    hash(G⊗H): { ctxId: "4", constructorId: TENSOR, ... },
    hash(I): { ctxId: "5", constructorId: ATPROP, ... },
}

byConstructor = {
    TENSOR: [entry1, entry4],   // A⊗B, G⊗H
    LOLI: [entry2],             // C-oD
    WITH: [entry3],             // E&F
    ATPROP: [entry5],           // I
}

variables = []  // No variables in context
```

### Query: Find `A ⊗ B`

```
Goal: A ⊗ B (ground, constructor = TENSOR)

Step 1: Compute hash
  hash(A⊗B) = 0x12AB...

Step 2: Direct lookup
  byHash.get(0x12AB...) → entry1

Step 3: Return
  Found! ctxId = "1"

Operations: 1 hash computation + 1 Map lookup = O(1)
```

### Query: Find `?X ⊗ B`

```
Goal: ?X ⊗ B (has variable, constructor = TENSOR)

Step 1: Get candidates by constructor
  byConstructor.get(TENSOR) → [entry1, entry4]  // A⊗B, G⊗H

Step 2: Try unification with each candidate
  mgu(?X ⊗ B, A ⊗ B) → {?X: A}  ✓ Success!

Step 3: Return
  Found! ctxId = "1", theta = {?X: A}

Operations: 1 lookup + 1 mgu attempt = O(n²)
vs. Current: 5 mgu attempts = O(5·n²)
```

### Query: Find `A -o Z` (not in context)

```
Goal: A -o Z (constructor = LOLI)

Current approach (without index):
  - Try mgu(A⊗B, A-oZ) → decompose... wait, different constructor → fail
  - Try mgu(C-oD, A-oZ) → decompose(C-oD, A-oZ) → fail (C≠A, D≠Z)
  - Try mgu(E&F, A-oZ) → different constructor → fail
  - Try mgu(G⊗H, A-oZ) → different constructor → fail
  - Try mgu(I, A-oZ) → different constructor → fail
  Total: 5 mgu calls, mostly wasted

With index:
  - byConstructor.get(LOLI) → [entry2]  // Only C-oD
  - Try mgu(C-oD, A-oZ) → fail (C≠A, D≠Z)
  - No more candidates
  Total: 1 mgu call

Speedup: 5× fewer mgu calls!
```

---

## 6. Integration with Merkle-DAG

### Hash as Primary Key

With content-addressed formulas, each formula has a unique hash. This is perfect for indexing:

```javascript
class ContextIndex {
    add(ctxId, entry, store) {
        // With Merkle-DAG, hash is already computed!
        const hash = entry.hash;  // O(1) - already stored
        // ... rest of indexing ...
    }
}
```

### Rebuilding Index After Substitution

**Problem:** After applying substitutions, formulas change, so hashes change.

**Solution 1: Lazy Rebuilding**
```javascript
class ContextIndex {
    constructor() {
        this.dirty = false;
    }

    markDirty() {
        this.dirty = true;
    }

    ensureValid(ctx, store) {
        if (this.dirty) {
            this.rebuild(ctx, store);
            this.dirty = false;
        }
    }
}
```

**Solution 2: Incremental Update**
```javascript
// When applying substitution theta to context:
function applySubstitution(ctx, index, theta, store) {
    for (const ctxId of Object.keys(ctx)) {
        const oldHash = ctx[ctxId].hash;
        const newVal = substitute(ctx[ctxId].val, theta);
        const newHash = intern(newVal, store);

        if (oldHash !== newHash) {
            index.remove(ctxId);
            ctx[ctxId] = { ...ctx[ctxId], val: newVal, hash: newHash };
            index.add(ctxId, ctx[ctxId], store);
        }
    }
}
```

---

## 7. Complete Implementation

### ContextIndex Class

```javascript
const Calc = require('./calc.js');

class ContextIndex {
    constructor() {
        this.byHash = new Map();        // hash → entry
        this.byConstructor = new Map(); // constructorId → [entries]
        this.variables = [];            // entries that are variables
        this.size = 0;
    }

    /**
     * Add a context entry to the index
     */
    add(ctxId, entry, store) {
        // Get the formula (inside the structure)
        const struct = entry.val;
        const formula = struct.vals[1];

        // Get hash (from store if available)
        const hash = formula.hash !== undefined
            ? formula.hash
            : this._computeHash(formula, store);

        // Get constructor info
        const type = Calc.db.rules[formula.id];
        const constructorId = formula.id;
        const isVariable = type && type.ruleName.endsWith('_Freevar');

        const indexEntry = {
            hash,
            constructorId,
            ctxId,
            entry,
            isVariable
        };

        // Add to primary index
        this.byHash.set(hash, indexEntry);

        // Add to secondary index
        if (isVariable) {
            this.variables.push(indexEntry);
        } else {
            if (!this.byConstructor.has(constructorId)) {
                this.byConstructor.set(constructorId, []);
            }
            this.byConstructor.get(constructorId).push(indexEntry);
        }

        this.size++;
        return indexEntry;
    }

    /**
     * Remove an entry by ctxId
     */
    remove(ctxId) {
        // Find and remove from byHash
        for (const [hash, entry] of this.byHash) {
            if (entry.ctxId === ctxId) {
                this.byHash.delete(hash);

                // Remove from byConstructor
                const bucket = this.byConstructor.get(entry.constructorId);
                if (bucket) {
                    const idx = bucket.findIndex(e => e.ctxId === ctxId);
                    if (idx >= 0) bucket.splice(idx, 1);
                }

                // Remove from variables
                const varIdx = this.variables.findIndex(e => e.ctxId === ctxId);
                if (varIdx >= 0) this.variables.splice(varIdx, 1);

                this.size--;
                return true;
            }
        }
        return false;
    }

    /**
     * O(1) exact lookup for ground formulas
     */
    findExact(hash) {
        return this.byHash.get(hash) || null;
    }

    /**
     * Find formulas that might unify with goal
     * Returns candidates filtered by constructor
     */
    getCandidates(goalFormula) {
        const type = Calc.db.rules[goalFormula.id];

        // If goal is a variable, all non-variables are candidates
        if (type && type.ruleName.endsWith('_Freevar')) {
            const allNonVars = [];
            for (const bucket of this.byConstructor.values()) {
                allNonVars.push(...bucket);
            }
            return allNonVars;
        }

        // Get formulas with same constructor
        const sameConstructor = this.byConstructor.get(goalFormula.id) || [];

        // Also include variables (they can match anything)
        return [...sameConstructor, ...this.variables];
    }

    /**
     * Find a formula that unifies with goal
     * Returns { entry, theta } or null
     */
    findUnifiable(goalFormula, mguFn) {
        // First try exact match (O(1))
        const goalHash = goalFormula.hash;
        if (goalHash !== undefined) {
            const exact = this.findExact(goalHash);
            if (exact) {
                return { entry: exact, theta: [] };
            }
        }

        // Get filtered candidates
        const candidates = this.getCandidates(goalFormula);

        // Try unification with each candidate
        for (const candidate of candidates) {
            const ctxFormula = candidate.entry.val.vals[1];
            const theta = mguFn([[ctxFormula, goalFormula]]);
            if (theta) {
                return { entry: candidate, theta };
            }
        }

        return null;
    }

    /**
     * Build index from context
     */
    static fromContext(ctx, store) {
        const index = new ContextIndex();
        for (const ctxId of Object.keys(ctx)) {
            index.add(ctxId, ctx[ctxId], store);
        }
        return index;
    }

    /**
     * Debug: show index structure
     */
    debug() {
        console.log(`ContextIndex (${this.size} entries):`);
        console.log(`  byHash: ${this.byHash.size} entries`);
        console.log(`  byConstructor:`);
        for (const [ctor, entries] of this.byConstructor) {
            const name = Calc.db.rules[ctor]?.ruleName || ctor;
            console.log(`    ${name}: ${entries.length} entries`);
        }
        console.log(`  variables: ${this.variables.length} entries`);
    }
}

module.exports = ContextIndex;
```

### Updated Identity Rule

```javascript
// In FocusedProver
tryIdentityPositive(pt, state) {
    const goal = pt.conclusion.succedent.vals[1];
    const ctx = pt.conclusion.linear_ctx;

    // Build or get cached index
    if (!pt._ctxIndex) {
        pt._ctxIndex = ContextIndex.fromContext(ctx, this.store);
    }

    // Use indexed lookup instead of linear scan
    const result = pt._ctxIndex.findUnifiable(goal, mgu);

    if (!result) return false;

    const { entry, theta } = result;

    // Apply substitution
    theta.forEach(([k, v]) => {
        pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v);
    });

    // Consume the matching formula
    const linear_ctx_ = { [entry.ctxId]: { num: 1, val: entry.entry.val } };
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_);

    const delta_out = pt.conclusion.linear_ctx;
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_+";

    return { theta, delta_out };
}
```

---

## 8. Performance Analysis

### Benchmarking Candidates vs. Total

Let's measure how much filtering helps:

```javascript
// Add to ContextIndex
findUnifiableWithStats(goalFormula, mguFn) {
    const totalEntries = this.size;
    const candidates = this.getCandidates(goalFormula);
    const candidateCount = candidates.length;

    console.log(`Candidates: ${candidateCount}/${totalEntries} (${(candidateCount/totalEntries*100).toFixed(1)}% of context)`);

    // ... rest of implementation ...
}
```

### Expected Filtering Ratios

For a context with m formulas and c distinct constructors:

| Distribution | Candidates per Lookup | Filtering Ratio |
|--------------|----------------------|-----------------|
| Uniform (m/c each) | m/c | c× speedup |
| One dominant constructor | ~m | ~1× (no benefit) |
| Many distinct constructors | ~1-2 | m× speedup |

**Typical ILL proofs:**
- Constructors: ⊗, -o, &, !, atoms (5-6 types)
- For m=10 formulas: expect ~2 candidates per lookup
- **Speedup: ~5×** just from filtering

### Combined Speedup

| Optimization | Factor |
|--------------|--------|
| Constructor filtering | ~m/c = ~5× |
| Hash equality (Merkle-DAG) | ~n× = ~20× |
| **Combined** | **~100×** |

---

## 9. Edge Cases and Considerations

### When Index Doesn't Help

1. **All same constructor:** If context is `A⊗B, C⊗D, E⊗F, ...` (all tensors), no filtering benefit.

2. **Goal is variable:** `?X` matches everything, so all context formulas are candidates.

3. **Very small context:** For m < 5, overhead might exceed benefit.

### Index Maintenance Cost

Building index: O(m) — done once per sequent.

For focused proofs, we might do multiple lookups on the same context, so the O(m) build cost is amortized.

### Memory Overhead

Per context formula:
- Hash map entry: ~40 bytes
- Constructor bucket entry: ~32 bytes
- **Total: ~72 bytes per formula**

For m=20 formulas: ~1.4 KB overhead. Negligible.

---

## 10. Recommendation

### Verdict: **IMPLEMENT**

**Priority:** HIGH (highest impact single optimization)

**Effort:** LOW-MEDIUM

**Rationale:**
1. Identity rule is the hottest path in proof search
2. O(m·n²) → O(1) for ground formulas is massive
3. Even for variable formulas, filtering gives ~5× speedup
4. Low implementation complexity
5. Integrates naturally with Merkle-DAG store
6. No downside — at worst, small constant overhead

### Implementation Order

1. Implement ContextIndex class
2. Add to tryIdentityPositive/tryIdentityNegative
3. Cache index on proof tree node
4. Benchmark and measure filtering ratio
5. Optimize if filtering ratio is low (e.g., secondary index on argument types)

---

## 11. References

- [Term indexing - Wikipedia](https://en.wikipedia.org/wiki/Term_indexing)
- [Lecture 22: Indexing - CMU ATP Course](https://www.cs.cmu.edu/~fp/courses/atp/lectures/22-indexing.html)
- [Term Indexing Techniques](https://www.researchgate.net/publication/234826819_Term_Indexing)
- [First-argument indexing - Prolog](https://www.swi-prolog.org/pldoc/man?section=indexing)
