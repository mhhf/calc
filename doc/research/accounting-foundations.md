# Accounting Foundations: Mathematical Structures and Linear Logic

Comprehensive research on the mathematical foundations of accounting, plain text accounting systems, and their deep connection to linear logic and CALC.

---

## Table of Contents

1. [Overview](#overview)
2. [The Pacioli Group](#the-pacioli-group)
3. [The Grothendieck Group](#the-grothendieck-group)
4. [Graph-Theoretic View](#graph-theoretic-view)
5. [Linear Algebra Formulation](#linear-algebra-formulation)
6. [Plain Text Accounting Systems](#plain-text-accounting-systems)
7. [Connection to Linear Logic](#connection-to-linear-logic)
8. [Category-Theoretic View](#category-theoretic-view)
9. [Connection to CALC](#connection-to-calc)
10. [Open Questions](#open-questions)
11. [References](#references)

---

## Overview

Accounting is one of the oldest "applied mathematics" — double-entry bookkeeping predates calculus by 300 years (Pacioli 1494 vs Newton/Leibniz 1680s). Yet its mathematical foundations were only formalized in the 1980s.

**Key insight**: Accounting = Applied Linear Algebra + Group Theory + Graph Theory

**The fundamental invariant**:
> **The sum of all postings in a transaction must equal zero.**

This is the **conservation law** of accounting — value cannot be created or destroyed, only transferred.

---

## The Pacioli Group

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

### Multidimensional Generalization (Pⁿ)

The **multidimensional Pacioli Group** Pⁿ handles n commodities:

```
Pⁿ = { [x⃗ // y⃗] : x⃗, y⃗ ∈ ℝ≥0ⁿ }
```

Each vector component is a different commodity (BTC, ETH, USD, etc.).

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

---

## Plain Text Accounting Systems

### Overview

**Plain Text Accounting (PTA)** is a methodology for bookkeeping using human-readable text files and command-line tools.

| System | Author | Language | Philosophy |
|--------|--------|----------|------------|
| **Ledger** | John Wiegley (2003) | C++ | Flexible, trusts user input |
| **hledger** | Simon Michael (2006) | Haskell | Ledger-compatible, more strict |
| **Beancount** | Martin Blais (2007) | Python | Pessimistic, maximum validation |

### Core Principles

1. **Human-readable data**: Plain text files, version-controllable
2. **Read-only tools**: Software reads data, never modifies it
3. **Double-entry bookkeeping**: Every transaction balances to zero
4. **User owns data**: No proprietary formats, no lock-in

### Data Model

**Transaction**:
```
2024-01-15 * "Coffee Shop"
  Expenses:Food:Coffee    $4.50
  Assets:Cash            -$4.50
```

**Account hierarchy**:
```
Assets:Bank:Checking
Liabilities:CreditCard:Visa
Expenses:Food:Groceries
Income:Salary:Employer
Equity:Opening
```

**Commodities**: Currencies, stocks, cryptocurrencies
```
$100.00          -- Currency
100 AAPL         -- Stock
0.5 BTC          -- Cryptocurrency
```

### Validation & Constraints

- **Transaction balance**: Every transaction must sum to zero
- **Balance assertions**: Assert expected balance at a point in time
- **Account open/close** (Beancount): Accounts must be opened before use
- **Inventory booking**: FIFO/LIFO for cost basis tracking

---

## Connection to Linear Logic

> **See also:** [[linear-negation-debt]] for detailed treatment of debt as linear negation.

### The Fundamental Parallel

| Accounting | Linear Logic |
|------------|--------------|
| Transaction balances to zero | Sequent is balanced |
| Debits = Credits | Resources in = Resources out |
| No creating value | No weakening |
| No destroying value | No contraction (if tracking) |
| T-account [x // y] | x ⊗ y⊥ (multiplicative with negation) |
| Transfer A→B | Linear implication A ⊸ B |
| Liability | Linear negation (A⊥) |

### Conservation as Cut-Free Proofs

The zero-sum property corresponds to:
```
Γ ⊢ Δ  where |Γ| = |Δ| (in some measure)
```

This is exactly the resource-counting property of linear logic!

### Tensor Product (⊗) as Transaction

A transaction transferring $100 from A to B:

```
Linear Logic:     [A] coin($, 100) ⊸ [B] coin($, 100)
PTA Transaction:  A: -$100, B: +$100
```

### Linear Negation as Liability

```
coin(BTC, 0.5)⊥ = obligation to provide 0.5 BTC
```

In PTA, **liabilities are negative assets** — the same idea!

```
Assets:Cash        $1000
Liabilities:Loan  -$1000   ← "owes $1000"
```

### Pacioli Group Relates to MULTIPLICATIVES

**Key insight**: The Pacioli group relates to multiplicatives, NOT additives.

- Additives (⊕, &): About **CHOICE** between alternatives
- Pacioli [x // y]: Tracks BOTH debit AND credit simultaneously

**Correct correspondence:**
```
[x // y]  ≈  x ⊗ y⊥
```
- x = asset/debit (positive resource)
- y⊥ = liability/credit (obligation)
- ⊗ = "have both simultaneously"

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

## Connection to CALC

> **See also:** [[ownership-design]] for CALC's ownership representation design.

### Coin Ownership

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

### What CALC Adds Beyond PTA

1. **Ownership modalities**: `[Alice]` vs `[Bob]` as first-class
2. **Authorization logic**: Explicit `A says transfer(...)` proofs
3. **Atomic swaps**: Multi-party consensus in logic
4. **Proof search**: Automated derivation of valid transfers
5. **Linear logic foundation**: Formal semantics, not just software

---

## Open Questions

### 1. Pacioli Group as Grading Structure

> **See also:** [[graded-resource-tracking]] for graded modal types and [[insights]] for key discoveries.

**Key insight**: The Pacioli group should be a GRADING STRUCTURE, not formula structure!

In graded linear logic (Granule-style):
```
□_r A   =  "r copies of A"
```

**Proposal: Use Pacioli group P as the grading ring:**
```
□_{[x//y]} A  =  "have x of A, owe y of A"
```

Then:
- Grade addition: [a//b] + [c//d] = [a+c // b+d] ✓
- Grade multiplication: [a//b] · [c//d] = ??? (needs definition)
- Settlement: □_{[x//y]} A ⊗ □_{[y//x]} A⊥ ⊢ □_{[0//0]} 1

### 2. K-Theory Connection

If accounting relates to K₀, what does this mean for:
- Multi-commodity tracking (vector bundles?)
- Hierarchical accounts (sheaves?)
- Time-varying balances (spectral sequences?)

### 3. Categorical Semantics

Can we give accounting a proper categorical semantics where:
- Objects = account states
- Morphisms = transactions
- The zero-sum constraint is built into the category structure?

### 4. Star-Autonomous Accounting

Star-autonomous categories are the categorical semantics of classical linear logic.
- Can accounting be given star-autonomous semantics?
- What is the dualizing object?
- Does the Pacioli group relate to the self-duality A ≅ (A⊥)⊥?

### 5. How Do Balance Assertions Map to Logic?

Balance assertions are **invariants** checked at specific points. In logic, might be a **predicate guard** or **precondition**:

```
check(date(2024-01-15), [Alice] coin($, 1234.56))
```

---

## Summary

Algebraic accounting reveals that double-entry bookkeeping has deep mathematical structure:

1. **Pacioli Group**: T-accounts form a group via "group of differences"
2. **Graph Theory**: Accounts as nodes, transactions as edges, zero-sum property
3. **Linear Algebra**: Incidence matrices, null space = conservation
4. **Category Theory**: Limits verify constraints, colimits aggregate
5. **Plain Text Accounting**: Battle-tested implementations (Ledger, hledger, Beancount)

**The parallel to linear logic is striking:**
- Conservation = resource-sensitivity
- T-accounts = formulas with negation
- Transactions = linear implications
- Liabilities = linear negation

**Key insight**: PTA systems have been doing "applied linear logic" for 500+ years without knowing it.

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

### Plain Text Accounting
- [Plain Text Accounting](https://plaintextaccounting.org/)
- [Ledger CLI](https://ledger-cli.org/)
- [hledger](https://hledger.org/)
- [Beancount Documentation](https://beancount.github.io/docs/)

### Linear Logic
- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- [nLab: Linear Logic](https://ncatlab.org/nlab/show/linear+logic)
- [Wadler, "A Taste of Linear Logic"](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)

### Grothendieck Group
- [Wikipedia: Grothendieck Group](https://en.wikipedia.org/wiki/Grothendieck_group)

---

*Created: 2026-02-10 (merged from algebraic-accounting.md and plain-text-accounting.md)*
