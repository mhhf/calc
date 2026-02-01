# Algebraic Accounting: Mathematical Foundations

This document explores the mathematical structures underlying accounting, with focus on connections to linear logic and CALC's research goals.

---

## Overview

Accounting is one of the oldest "applied mathematics" — double-entry bookkeeping predates calculus by 300 years (Pacioli 1494 vs Newton/Leibniz 1680s). Yet its mathematical foundations were only formalized in the 1980s.

Key insight: **Accounting = Applied Linear Algebra + Group Theory + Graph Theory**

---

## The Pacioli Group (Ellerman)

### Definition

The **Pacioli Group** P is the group of differences constructed from non-negative numbers:

```
P = { [x // y] : x, y ≥ 0 }
```

Where `[x // y]` is a T-account with debits x and credits y.

### Operations

**Addition:**
```
[a // b] + [c // d] = [a+c // b+d]
```

**Identity:**
```
0 = [0 // 0]
```

**Inverse:**
```
-[a // b] = [b // a]
```

**Equality (via cross-sums):**
```
[a // b] = [c // d]  ⟺  a + d = b + c
```

### Isomorphism to Integers

Two canonical isomorphisms:

```
Debit iso:  φ_D([x // y]) = x - y
Credit iso: φ_C([x // y]) = y - x
```

Both are group isomorphisms P → ℤ (or ℝ for real amounts).

### Why Pairs Instead of Signed Numbers?

1. **Historical**: Bookkeepers used unsigned ledgers
2. **Provenance**: Separate audit trails for debits and credits
3. **Error detection**: Cross-sum equality is a checksum
4. **Semantic clarity**: Debits and credits have different meanings

---

## Multidimensional Generalization (Pⁿ)

### Definition

The **multidimensional Pacioli Group** Pⁿ handles n commodities:

```
Pⁿ = { [x⃗ // y⃗] : x⃗, y⃗ ∈ ℝ≥0ⁿ }
```

Each vector component is a different commodity (BTC, ETH, USD, etc.).

### Preserved Properties

All double-entry features generalize:
- Balance sheet equation ✓
- Equity accounts ✓
- Temporary accounts ✓
- Trial balance ✓

### Encoding Rules

For a vector equation `A = B + C`:
- Left-hand side: debit isomorphism → debit-balance accounts
- Right-hand side: credit isomorphism → credit-balance accounts

---

## The Grothendieck Group

The Pacioli group is a special case of the **Grothendieck group** construction.

### General Construction

Given a commutative monoid (M, +, 0), the Grothendieck group K(M) is:

```
K(M) = (M × M) / ~

where (a, b) ~ (c, d) ⟺ ∃k. a + d + k = b + c + k
```

### Example: ℕ → ℤ

```
K(ℕ, +) = ℤ

(3, 1) ~ (5, 3) because 3 + 3 = 1 + 5 = 6
Both represent the integer 2
```

### Connection to K-Theory

The Grothendieck group is fundamental in algebraic K-theory:
- K₀(X) of a manifold X = Grothendieck group of vector bundles
- K₀(R) of a ring R = Grothendieck group of finitely generated projective modules

This suggests deep connections between accounting and algebraic topology!

---

## Graph-Theoretic View

### Accounts as Nodes, Transactions as Edges

Martin Kleppmann's insight:

```
Accounts = Nodes
Transactions = Directed edges (with amounts)
```

A transaction moving $100 from A to B:
```
A --[$100]--> B
```

### Balance Calculation

For each node (account):
```
balance = Σ(incoming edges) - Σ(outgoing edges)
```

### The Zero-Sum Property

**Theorem**: The sum of all account balances is always zero.

**Proof**: Every transaction creates +amount at destination and -amount at source. Net effect: zero.

### Partition Property

For any partition of accounts into sets S₁ and S₂:
```
Σ(balances in S₁) = -Σ(balances in S₂)
```

This is why Assets = Liabilities + Equity works!

---

## Linear Algebra Formulation

### Incidence Matrix

Represent accounts as rows, transactions as columns:

```
         T₁  T₂  T₃  ...
A₁    [  +1  -1   0  ... ]
A₂    [  -1  +1  +1  ... ]
A₃    [   0   0  -1  ... ]
...
```

Where +1 = debit, -1 = credit.

### Conservation as Null Space

The vector of all 1s is in the **left null space** of the incidence matrix:

```
[1 1 1 ...] · M = [0 0 0 ...]
```

This means: for every transaction (column), debits equal credits.

### Balance Vector

```
balance = M · amounts
```

Where `amounts` is the vector of transaction amounts.

---

## Category-Theoretic View

### Recent Work (2025)

Paper: "Macroeconomic Foundation of Monetary Accounting by Diagrams of Categorical Universals" (arXiv:2508.14132)

Uses category theory to:
- Compose microeconomic double-entry systems → macroeconomic systems
- **Limits** verify constraints (balance equations)
- **Colimits** aggregate (sum accounts)
- **Endofunctors** model temporal evolution

### Potential Categorical Structure

```
Objects: Account states (inventories)
Morphisms: Transactions (balanced transfers)
Composition: Sequential execution
Identity: No-op transaction
```

This forms a category! The zero-sum constraint means every morphism is "measure-preserving."

---

## Connection to Linear Logic

### The Fundamental Parallel

| Accounting | Linear Logic |
|------------|--------------|
| Transaction balances to zero | Sequent is balanced |
| Debits = Credits | Resources in = Resources out |
| No creating value | No weakening |
| No destroying value | No contraction (if tracking) |
| T-account [x // y] | A ⊗ A⊥ or A ⅋ A⊥ ? |
| Transfer A→B | Linear implication A ⊸ B |
| Liability | Linear negation (A⊥) |

### The Pacioli Group as Linear Logic?

**Hypothesis**: The T-account structure [x // y] might correspond to:

1. **Tensor with negation**: x ⊗ y⊥
   - "I have x debits AND owe y credits"

2. **Par with negation**: x ⅋ y⊥
   - "Either x debits OR y credits (entangled)"

3. **Additive structure**: x ⊕ y⊥
   - "Choice between x and y"

**Open question**: Which is the correct correspondence?

### Conservation as Cut-Free Proofs

The zero-sum property corresponds to:
```
Γ ⊢ Δ  where |Γ| = |Δ| (in some measure)
```

This is exactly the resource-counting property of linear logic!

---

## Connection to CALC Goals

### Coin Ownership (from sketch.md)

Our formula `[Alice] coin(BTC, 0.322)` maps to accounting:

```
Account: Alice:BTC
Balance: 0.322 (debit balance = asset)
```

### Transfers

Our transfer rule:
```
(Alice says transfer(Bob,BTC,q)) ⊗ [Alice] coin(BTC,q) ⊸ [Bob] coin(BTC,q)
```

Maps to accounting transaction:
```
Debit:  Bob:BTC     +q
Credit: Alice:BTC   -q
```

### Liabilities as Negation

Our hypothesis: `coin(BTC, q)⊥` = debt

In accounting:
```
Liability account = credit balance = "negative asset"
```

**The parallel is exact!**

### Atomic Swaps

Our atomic swap:
```
[A] coin(C₁,q₁) ⊗ [B] coin(C₂,q₂) ⊸ [B] coin(C₁,q₁) ⊗ [A] coin(C₂,q₂)
```

In accounting, this is a **compound transaction** with 4 entries:
```
Debit:  B:C₁   +q₁
Credit: A:C₁   -q₁
Debit:  A:C₂   +q₂
Credit: B:C₂   -q₂
```

All four entries must be atomic — exactly what accounting requires!

---

## Research Update: Pacioli/Grothendieck and Linear Logic

### Q1: Is Pacioli Group Related to Linear Logic Additives?

**Answer: NO — Pacioli group relates to MULTIPLICATIVES, not additives.**

**Analysis of Linear Logic Additives:**
- **⊕ (oplus)**: External/additive disjunction — "one OR the other, environment chooses"
- **& (with)**: Internal/additive conjunction — "one OR the other, I choose"

These are fundamentally about **CHOICE** between alternatives.

**Analysis of Pacioli Group:**
- [x // y] tracks BOTH debit (x) AND credit (y) simultaneously
- Addition: [a // b] + [c // d] = [a+c // b+d] — componentwise, PARALLEL
- Not about choosing between x and y

**Correct correspondence: Pacioli group relates to MULTIPLICATIVES:**
```
[x // y]  ≈  x ⊗ y⊥
```
- x = asset/debit (positive resource)
- y⊥ = liability/credit (obligation)
- ⊗ = "have both simultaneously"

**The inverse operation:**
```
-[x // y] = [y // x]  ≈  y ⊗ x⊥
```
Flipping debit/credit swaps which side is the obligation.

**Why not additives:**
- [x // y] + [a // b] = [x+a // y+b] — both sides accumulate
- A ⊕ B would mean "choose x OR y" — but T-accounts track both
- A & B would mean "offer choice" — but T-accounts are determined

### Q2: Is Grothendieck Group = Linear Negation?

**Answer: CONCEPTUALLY SIMILAR but structurally different.**

| Grothendieck Group | Linear Negation |
|-------------------|-----------------|
| Element-level: monoid M → group K(M) | Formula-level: A → A⊥ |
| Creates additive inverses | Creates logical duals |
| Universal construction (left adjoint) | Built-in involution |
| Equivalence classes of pairs | Already exists as operation |

**The parallel:**
- Grothendieck: "unsigned → signed" (adds inverses to elements)
- Linear negation: "resource → obligation" (flips proponent/opponent)

**Key difference:**
- Grothendieck group is a **categorical construction** (left adjoint to forgetful functor)
- Linear negation is a **logical operation** (de Morgan duality in star-autonomous categories)

**The deep insight**: Grothendieck group operates on the **GRADE/QUANTITY level**, not formula level!

### Q1+Q2 Synthesis: Pacioli Group as Grading Semiring

**Key insight: The Pacioli group should be a GRADING STRUCTURE, not formula structure!**

In graded linear logic (Granule-style):
```
□_r A   =  "r copies of A"
```
where r comes from a semiring (or ring).

**Proposal: Use Pacioli group P as the grading ring:**
```
□_{[x//y]} A  =  "have x of A, owe y of A"
```

Then:
- Grade addition: [a//b] + [c//d] = [a+c // b+d] ✓
- Grade multiplication: [a//b] · [c//d] = ??? (needs definition)
- Settlement: □_{[x//y]} A ⊗ □_{[y//x]} A⊥ ⊢ □_{[0//0]} 1

**This connects:**
- Ellerman's algebraic accounting
- Graded linear logic (Granule, QTT)
- CALC's ownership modalities

### Updated Open Questions

### 3. K-Theory Connection (Unchanged)

If accounting relates to K₀, what does this mean for:
- Multi-commodity tracking (vector bundles?)
- Hierarchical accounts (sheaves?)
- Time-varying balances (spectral sequences?)

### 4. Categorical Semantics (Unchanged)

Can we give accounting a proper categorical semantics where:
- Objects = account states
- Morphisms = transactions
- The zero-sum constraint is built into the category structure?

### 5. Pacioli Ring as Grading Structure (NEW)

Can the Pacioli group be used as a grading RING for graded linear logic?
- What is the multiplication operation?
- How do grade polymorphism and T-accounts interact?
- Does □_{[x//y]} A give clean accounting semantics?

### 6. Star-Autonomous Accounting (NEW)

Star-autonomous categories are the categorical semantics of classical linear logic.
- Can accounting be given star-autonomous semantics?
- What is the dualizing object?
- Does the Pacioli group relate to the self-duality A ≅ (A⊥)⊥?

---

## Summary

Algebraic accounting reveals that double-entry bookkeeping has deep mathematical structure:

1. **Pacioli Group**: T-accounts form a group via "group of differences"
2. **Graph Theory**: Accounts as nodes, transactions as edges, zero-sum property
3. **Linear Algebra**: Incidence matrices, null space = conservation
4. **Category Theory**: Limits verify constraints, colimits aggregate

**The parallel to linear logic is striking:**
- Conservation = resource-sensitivity
- T-accounts = formulas with negation
- Transactions = linear implications
- Liabilities = linear negation

This validates our approach in sketch.md and suggests that **linear logic IS the logic of accounting**.

---

## References

### Ellerman's Work
- [Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment" (arXiv:1407.1898)](https://arxiv.org/abs/1407.1898)
- [Ellerman, "The Math of Double-Entry Bookkeeping Part I"](https://www.ellerman.org/the-math-of-double-entry-bookkeeping-part-i-scalars/)
- [Ellerman, "The Math of Double-Entry Bookkeeping Part II (vectors)"](https://www.ellerman.org/the-math-of-double-entry-bookkeeping-part-ii-vectors/)

### Graph/Linear Algebra
- [Kleppmann, "Accounting for Computer Scientists"](https://martin.kleppmann.com/2011/03/07/accounting-for-computer-scientists.html)
- [MDPI, "Accounting Games: Using Matrix Algebra"](https://www.mdpi.com/2227-7390/6/9/152)

### Category Theory
- [arXiv:2508.14132 — Macroeconomic Accounting via Category Theory](https://arxiv.org/abs/2508.14132)
- [Sulganik, "Towards a Theory of Mathematical Accounting"](https://gilkalai.wordpress.com/2012/06/19/eyal-sulganik-towards-a-theory-of-mathematical-accounting/)

### Grothendieck Group
- [Wikipedia: Grothendieck Group](https://en.wikipedia.org/wiki/Grothendieck_group)

---

*Last updated: 2026-01-29*
