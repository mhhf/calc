---
title: "Polynomial Memoization via Subformula Property"
created: 2026-02-10
modified: 2026-02-10
summary: Leveraging subformula property to bound proof search space enabling polynomial-time memoization using Merkle-DAG hashing for sequent deduplication.
tags: [memoization, subformula-property, optimization, polynomial-time, proof-search]
---

# Polynomial Memoization via Subformula Property

Deep dive into how the subformula property enables polynomial-time proof search through memoization.

> **See also:** [[content-addressed-formulas]] for Merkle-DAG sequent hashing, [[backward-prover-optimization]] for overall optimization strategy, [[proof-calculi-foundations]] for subformula property.

---

## Table of Contents

1. [The Problem: Exponential Proof Search](#1-the-problem-exponential-proof-search)
2. [The Subformula Property](#2-the-subformula-property-bounding-the-search-space)
3. [From Subformula Property to Polynomial Bound](#3-from-subformula-property-to-polynomial-bound)
4. [Memoization: Computing Each Sequent Once](#4-memoization-computing-each-sequent-once)
5. [Implementing Memoization with Merkle-DAG](#5-implementing-memoization-with-merkle-dag)
6. [Concrete Example](#6-concrete-example-before-and-after-memoization)
7. [When Does Memoization Help Most?](#7-when-does-memoization-help-most)
8. [Complexity Analysis](#8-complexity-analysis)
9. [Implementation Details for CALC](#9-implementation-details-for-calc)
10. [Recommendation](#10-recommendation-should-we-implement-this)
11. [References](#11-references)

---

## 1. The Problem: Exponential Proof Search

### Current Complexity Analysis

Consider proof search for a sequent like:

```
A ⊗ B, C ⊗ D, E -o F |- G
```

**Without optimizations, proof search is exponential:**

```
         [Root Sequent]
            /      \
       [Choice 1]  [Choice 2]  ...
          /    \
    [Premise 1] [Premise 2]
        |           |
       ...         ...
```

At each step, the prover makes nondeterministic choices:
- Which formula to focus on (m choices for m context formulas)
- Which rule to apply (sometimes multiple options)
- How to split context for multiplicative rules (exponential splits)

**Complexity:** O(b^d) where b = branching factor, d = depth.

For a formula of size n with depth d ≈ n, this is O(b^n) — exponential.

### Example: Why Current Prover Revisits Same Subproblems

Consider proving: `A ⊗ A ⊗ A |- A ⊗ A ⊗ A`

The prover might:
1. Focus on first A on right
2. Try to match with first A on left → **subproblem: `A ⊗ A |- A ⊗ A`**
3. If that fails, try second A on left → same subproblem!
4. If that fails, try third A → same subproblem!

**The same subproblem `A ⊗ A |- A ⊗ A` is solved 3 times!**

And within that subproblem, `A |- A` might be solved multiple times.

This redundancy compounds exponentially.

---

## 2. The Subformula Property: Bounding the Search Space

### Definition

**Subformula Property:** In a cut-free proof, every formula that appears is a subformula of some formula in the final sequent (the goal).

**Subformula Definition:** A subformula of φ is:
- φ itself
- Any immediate constituent of φ
- Any subformula of an immediate constituent

### Example: Subformulas

For the formula `(A ⊗ B) -o (C & D)`:

```
Subformulas:
├── (A ⊗ B) -o (C & D)   [the formula itself]
├── A ⊗ B                 [left of -o]
│   ├── A                 [left of ⊗]
│   └── B                 [right of ⊗]
├── C & D                 [right of -o]
│   ├── C                 [left of &]
│   └── D                 [right of &]
```

**Count:** 7 subformulas for this formula.

### Counting Subformulas

For a formula of size n (measured by number of connective symbols):
- **Upper bound:** At most n distinct subformulas
- Each connective contributes one subformula
- Atoms are also subformulas

**Key insight:** The number of subformulas is **linear** in formula size.

### Why Cut Violates Subformula Property

The Cut rule introduces a "lemma" formula:

```
  Γ |- A      A, Δ |- C
  ----------------------- Cut
       Γ, Δ |- C
```

The formula A (the "cut formula") can be **anything** — it doesn't have to appear in the conclusion `Γ, Δ |- C`.

This allows unbounded formulas to appear in proofs, breaking the subformula bound.

**Cut-free proofs** don't have this problem: every formula is derived from decomposing formulas already in the sequent.

---

## 3. From Subformula Property to Polynomial Bound

### The Key Insight

If only subformulas can appear, and there are at most n subformulas, then:

**The number of distinct sequents is bounded by a polynomial in n.**

### Counting Distinct Sequents

For intuitionistic linear logic with multiset contexts:

**Sequent structure:** `Γ ; Δ |- C`
- Γ = persistent context (set of formulas)
- Δ = linear context (multiset of formulas)
- C = succedent (single formula)

**Possible sequents from n subformulas:**

1. **Succedent:** n choices (any subformula)

2. **Linear context:** Each subformula can appear 0, 1, 2, ... times
   - But wait — can multiplicities be unbounded?
   - **No!** In a proof, you can't create formulas from nothing
   - Multiplicity of any formula ≤ multiplicity in original goal
   - If original goal has each formula at most k times, max multiplicity = k

3. **Practical bound:** For typical proofs where each formula appears ≤ 1 time:
   - Linear context: 2^n possibilities (each subformula present or absent)
   - This is still exponential!

### The Tighter Bound (for specific logics)

For **propositional linear logic without contraction**:
- Each formula appears at most once
- Total formulas in any sequent ≤ n (original formulas, minus consumed, plus decomposed)
- Number of sequents = O(n × 2^n)

This is still exponential in general, BUT:

**For focused proof search with the specific structure of ILL:**
- Inversion phase: deterministic (no branching)
- Focus phase: bounded choices based on context
- The actual reachable sequents are much fewer

### The Orthologic Result (Special Case)

The [orthologic paper](https://arxiv.org/html/2501.09418) achieves O(n²) because:
- Sequents have **at most 2 formulas** (special restriction)
- With n subformulas and max 2 per sequent: O(n²) possibilities

**For general ILL, the bound is worse but still polynomial under certain conditions.**

---

## 4. Memoization: Computing Each Sequent Once

### The Memoization Principle

```
Memoization Table: sequent_hash → ProofResult

function prove(sequent):
    hash = computeHash(sequent)
    if memoTable.has(hash):
        return memoTable.get(hash)  // O(1) lookup!

    result = actualProofSearch(sequent)
    memoTable.set(hash, result)
    return result
```

### Why This Helps

**Without memoization:**
- Same sequent may be reached via different paths
- Each occurrence is solved independently
- Exponential redundancy

**With memoization:**
- First time: full proof search, store result
- Subsequent times: O(1) lookup
- Each unique sequent solved exactly once

### Complexity With Memoization

If there are P distinct sequents reachable:
- Each sequent's proof search body runs at most once
- Total time = O(P × T) where T = time per sequent
- If P is polynomial and T is polynomial, total is polynomial!

---

## 5. Implementing Memoization with Merkle-DAG

### The Challenge: Efficient Sequent Hashing

To memoize, we need fast, canonical hashing of sequents.

**Current approach (bad):**
```javascript
// O(n) - converts entire sequent to string, then hashes
const key = sha3(sequent.toString());
```

**With Merkle-DAG (good):**
```javascript
// O(1) - sequent already has content hash
const key = sequent.hash;  // BigInt, computed incrementally
```

### Sequent Hash Structure

A sequent `Γ ; Δ |- C` becomes a hash combining:
1. Persistent context hash (order-independent)
2. Linear context hash (order-independent, but multiplicity-sensitive)
3. Succedent hash

```javascript
function hashSequent(seq, store) {
    // Get sorted hashes for order independence
    const persHashes = Object.keys(seq.persistent_ctx)
        .map(id => seq.persistent_ctx[id].hash)
        .sort((a, b) => a < b ? -1 : 1);

    const linHashes = [];
    for (const [id, entry] of Object.entries(seq.linear_ctx)) {
        // Include multiplicity in hash
        for (let i = 0; i < entry.num; i++) {
            linHashes.push(entry.hash);
        }
    }
    linHashes.sort((a, b) => a < b ? -1 : 1);

    const succHash = seq.succedent;

    // Combine all hashes
    // Constructor ID 0 reserved for "sequent" type
    return store.hashStructural(0, [
        store.hashArray(persHashes),
        store.hashArray(linHashes),
        succHash
    ]);
}
```

### The Memo Table

```javascript
class ProofMemo {
    constructor() {
        // Map: sequentHash (BigInt) → ProofResult
        this.table = new Map();
        this.stats = { hits: 0, misses: 0 };
    }

    lookup(seqHash) {
        if (this.table.has(seqHash)) {
            this.stats.hits++;
            return this.table.get(seqHash);
        }
        this.stats.misses++;
        return null;
    }

    store(seqHash, result) {
        this.table.set(seqHash, result);
    }

    // For debugging: hit rate
    hitRate() {
        const total = this.stats.hits + this.stats.misses;
        return total > 0 ? this.stats.hits / total : 0;
    }
}
```

### Integration with Proof Search

```javascript
// In FocusedProver.auto()
auto(pt, options = {}) {
    const seqHash = hashSequent(pt.conclusion, this.store);

    // Check memo first
    const cached = this.memo.lookup(seqHash);
    if (cached !== null) {
        // Replay cached result
        pt.proven = cached.success;
        pt.type = cached.type;
        return cached;
    }

    // ... actual proof search ...

    // Store result
    const result = { success, delta_out, theta, type: pt.type };
    this.memo.store(seqHash, result);
    return result;
}
```

---

## 6. Concrete Example: Before and After Memoization

### Goal: Prove `(A ⊗ A) ⊗ A |- A ⊗ (A ⊗ A)`

**Subformulas:** {A, A⊗A, (A⊗A)⊗A, A⊗(A⊗A)} = 4 unique (A appears multiple times but is one subformula)

### Without Memoization

```
prove((A⊗A)⊗A |- A⊗(A⊗A))
├── decompose right: A⊗(A⊗A)
│   ├── branch: ∅ |- A  AND  (A⊗A)⊗A |- A⊗A
│   │   ├── prove(∅ |- A) → FAIL (no A in context)
│   │   └── [backtrack]
│   ├── branch: A |- A  AND  (A⊗A) |- A⊗A
│   │   ├── prove(A |- A) → SUCCESS
│   │   └── prove((A⊗A) |- A⊗A)  ← SUBPROBLEM 1
│   │       ├── decompose right
│   │       │   ├── branch: ∅ |- A AND A⊗A |- A
│   │       │   │   └── FAIL
│   │       │   ├── branch: A |- A AND A |- A  ← SUBPROBLEM 2 (twice!)
│   │       │   │   ├── prove(A |- A) → SUCCESS
│   │       │   │   └── prove(A |- A) → SUCCESS (REPEATED!)
│   │       │   └── SUCCESS
│   │       └── SUCCESS
│   └── SUCCESS
├── ... many other branches tried ...
└── SUCCESS
```

**Problem:** `prove(A |- A)` is called multiple times!

### With Memoization

```
prove((A⊗A)⊗A |- A⊗(A⊗A))
├── hash = 0xABC... (not in memo, compute)
├── decompose right: A⊗(A⊗A)
│   ├── branch: A |- A  AND  (A⊗A) |- A⊗A
│   │   ├── prove(A |- A)
│   │   │   ├── hash = 0x123... (not in memo, compute)
│   │   │   ├── identity succeeds
│   │   │   └── STORE memo[0x123...] = SUCCESS
│   │   └── prove((A⊗A) |- A⊗A)
│   │       ├── hash = 0x456... (not in memo, compute)
│   │       ├── decompose right
│   │       │   ├── branch: A |- A AND A |- A
│   │       │   │   ├── prove(A |- A)
│   │       │   │   │   └── MEMO HIT! 0x123... → SUCCESS (O(1)!)
│   │       │   │   └── prove(A |- A)
│   │       │   │       └── MEMO HIT! 0x123... → SUCCESS (O(1)!)
│   │       │   └── SUCCESS
│   │       └── STORE memo[0x456...] = SUCCESS
│   └── SUCCESS
└── STORE memo[0xABC...] = SUCCESS

Memo Stats:
- Unique sequents: 3
- Total calls: 5
- Memo hits: 2
- Hit rate: 40%
```

**Savings:** 2 redundant proof searches avoided.

For larger proofs, savings compound exponentially!

---

## 7. When Does Memoization Help Most?

### High-Value Scenarios

1. **Repeated subformulas** (like `A ⊗ A ⊗ A`)
   - Same substructures reached via different decomposition paths

2. **Symmetric connectives** (`&`, `⊗`)
   - Left and right subformulas may create similar subproblems

3. **Deep nesting**
   - More opportunities for subtree reuse

4. **Contraction** (with `!`)
   - Duplicated formulas create identical subproblems

### Low-Value Scenarios

1. **All distinct atoms** (`A, B, C, D, ...`)
   - Few repeated subformulas, less memoization opportunity

2. **Shallow proofs**
   - Not enough recursion to build up memo table

3. **Highly asymmetric formulas**
   - Different branches encounter different sequents

### Measuring Value: Hit Rate

```javascript
// After proof search
console.log(`Memo hit rate: ${(memo.hitRate() * 100).toFixed(1)}%`);
console.log(`Unique sequents: ${memo.table.size}`);
console.log(`Total calls: ${memo.stats.hits + memo.stats.misses}`);

// If hit rate > 30%, memoization is helping significantly
// If hit rate > 50%, we're seeing exponential → polynomial improvement
```

---

## 8. Complexity Analysis

### Variables

- n = number of subformulas in goal
- k = maximum multiplicity of any formula
- m = number of formulas in largest context

### Without Memoization

**Branching factor b:** At each step, we might try:
- m focus choices (each context formula)
- Split choices for multiplicatives: O(2^m) in worst case

**Depth d:** Proof depth ≈ n (one step per subformula decomposition)

**Total:** O(b^d) = O((m × 2^m)^n) — doubly exponential!

### With Memoization

**Unique sequents P:**
- Each sequent is determined by: which subformulas, with what multiplicities, in which position
- Upper bound: P ≤ n × (k+1)^n ≤ n × 2^(n log k)
- For k=1 (no contraction): P ≤ n × 2^n

**Work per sequent:**
- Constant branching within that sequent: O(b)
- But we only enter each sequent once!

**Total with memoization:** O(P × b) = O(n × 2^n × b)

**For specific logics (like orthologic with size-2 sequents):** O(n²)

### The Win

| Scenario | Without Memo | With Memo | Speedup |
|----------|--------------|-----------|---------|
| Orthologic | O((2^n)!) | O(n²) | Exponential → Polynomial |
| ILL (worst) | O((2^m)^n) | O(n × 2^n) | Super-exp → Singly-exp |
| ILL (practical) | O(b^n) | O(P × b) where P << b^n | Often polynomial |

The practical speedup depends on how many sequents are actually reachable.

---

## 9. Implementation Details for CALC

### Step 1: Add Hash to Sequent

```javascript
// In sequent.js
class Sequent {
    constructor(params) {
        this.persistent_ctx = params.persistent_ctx || {};
        this.linear_ctx = params.linear_ctx || {};
        this.succedent = params.succedent;
        this.store = params.store;  // NEW: reference to Store
        this._hash = null;          // NEW: cached hash (lazy)
    }

    // Compute hash on demand, cache it
    get hash() {
        if (this._hash === null) {
            this._hash = this._computeHash();
        }
        return this._hash;
    }

    _computeHash() {
        // ... implementation from section 5 ...
    }

    // Invalidate cache when modified
    invalidateHash() {
        this._hash = null;
    }
}
```

### Step 2: Add Memo Table to Prover

```javascript
// In prover.js
class FocusedProver {
    constructor(calculus) {
        // ... existing init ...
        this.memo = new ProofMemo();
    }

    auto(pt, options = {}) {
        const seqHash = pt.conclusion.hash;

        // Memo lookup
        const cached = this.memo.lookup(seqHash);
        if (cached) {
            return this._applyCachedResult(pt, cached);
        }

        // ... existing proof search ...

        // Store in memo before returning
        this.memo.store(seqHash, { success, theta, type: pt.type });
        return result;
    }

    _applyCachedResult(pt, cached) {
        pt.proven = cached.success;
        pt.type = cached.type + " (memo)";
        return {
            success: cached.success,
            delta_out: {},  // Need to handle this carefully
            theta: cached.theta,
            debug: { head: { technique: "MEMO HIT" }, children: [] }
        };
    }
}
```

### Step 3: Handle Substitutions Correctly

**Problem:** Memoization doesn't automatically handle variable bindings.

A sequent `?X |- ?X` always proves (identity), regardless of what ?X is. But `A |- B` doesn't prove.

**Solution:** Only memoize **ground** results, or normalize variables first.

```javascript
function canMemoize(sequent) {
    // Only memoize if fully ground (no variables)
    return Sequent.getFreeVariables(sequent).length === 0;
}

// In auto():
const isGround = canMemoize(pt.conclusion);
if (isGround) {
    const cached = this.memo.lookup(seqHash);
    if (cached) return cached;
}

// ... proof search ...

if (isGround) {
    this.memo.store(seqHash, result);
}
```

**Alternative:** Memoize with variable-aware hashing (more complex, bigger payoff).

---

## 10. Recommendation: Should We Implement This?

### Effort Estimate

| Task | Effort | Dependencies |
|------|--------|--------------|
| Add hash to Sequent | LOW | Store + hash.js |
| ProofMemo class | LOW | None |
| Integrate with prover | MEDIUM | Sequent hash |
| Handle variables correctly | MEDIUM | Variable analysis |
| **Total** | **MEDIUM** | Requires Store first |

### Expected Benefit

For **typical proofs** in CALC:
- Formulas like `owns(Alice, 100$) ⊗ owns(Bob, 50$) -o owns(Alice, 50$) ⊗ owns(Bob, 100$)`
- Moderate repetition of subformulas
- Expected hit rate: 20-50%
- Expected speedup: 2-10×

For **complex proofs** with high symmetry:
- Hit rate: 50-80%
- Expected speedup: 10-100×

For **very large proofs** with deep nesting:
- Hit rate: 80%+
- Expected speedup: 100-1000× (exponential → polynomial)

### Verdict: **IMPLEMENT**

**Priority:** HIGH

**Rationale:**
1. Medium implementation effort
2. High expected benefit for complex proofs
3. Foundation (Store + hash) needed anyway
4. Easy to measure effectiveness via hit rate
5. No downside — worst case is no speedup, not slowdown

### Implementation Order

1. First: Implement Store + hash.js (required anyway)
2. Then: Add sequent hashing
3. Then: Add ProofMemo
4. Then: Integrate with prover
5. Finally: Measure and optimize

---

## 11. References

- [Verified and Optimized Implementation of Orthologic Proof Search](https://arxiv.org/html/2501.09418) — O(n²) via memoization
- [Cut-elimination theorem - Wikipedia](https://en.wikipedia.org/wiki/Cut-elimination_theorem) — Subformula property origin
- [Subformula Property - nLab](https://ncatlab.org/nlab/show/subformula+property) — Formal definition
- [Propositional logics complexity and the sub-formula property](https://arxiv.org/pdf/1401.8209) — PSPACE completeness
- [On sharing, memoization, and polynomial time](https://www.sciencedirect.com/science/article/pii/S0890540118300750) — Theoretical foundations
