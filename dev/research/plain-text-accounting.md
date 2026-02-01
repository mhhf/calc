# Plain Text Accounting: Deep Research

This document explores plain text accounting systems (Ledger, hledger, Beancount), their data models, mathematical foundations, and relevance to CALC's research goals.

---

## Overview

**Plain Text Accounting (PTA)** is a methodology for bookkeeping using human-readable text files and command-line tools. The three major implementations are:

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

---

## The Fundamental Invariant

The cornerstone of double-entry bookkeeping is elegantly simple:

> **The sum of all postings in a transaction must equal zero.**

Mathematically, for any transaction with postings p₁, p₂, ..., pₙ:

```
p₁ + p₂ + ... + pₙ = 0
```

This is the **conservation law** of accounting—value cannot be created or destroyed, only transferred between accounts.

### The Accounting Equation

From the transaction-level constraint follows the global equation:

```
Assets + Liabilities + Equity + Income + Expenses = 0
```

Or equivalently (using sign conventions):

```
Assets = Liabilities + Equity
```

This parallels Newton's third law: "for every asset acquired, there must be a corresponding liability or equity source."

---

## Data Model

### Transactions

A transaction represents a single economic event:

```
2024-01-15 * "Coffee Shop"
  Expenses:Food:Coffee    $4.50
  Assets:Cash            -$4.50
```

Components:
- **Date**: When the event occurred
- **Status**: `*` (cleared) or `!` (pending)
- **Description**: What happened
- **Postings**: Account-amount pairs (minimum two)

### Postings

A posting represents value flow to/from one account:

```
Account:Name    Amount [Commodity] [{Cost}] [@ Price]
```

The amount can be positive (debit) or negative (credit), or one posting can be elided (inferred to balance).

### Accounts

Hierarchical names using colon separators:

```
Assets:Bank:Checking
Liabilities:CreditCard:Visa
Expenses:Food:Groceries
Income:Salary:Employer
Equity:Opening
```

Five standard types (Beancount enforces these):
1. **Assets** — what you own
2. **Liabilities** — what you owe
3. **Equity** — net worth / capital
4. **Income** — value received
5. **Expenses** — value consumed

### Commodities

Currencies, stocks, or any countable unit:

```
$100.00          -- Currency (symbol before)
100 AAPL         -- Stock (symbol after)
0.5 BTC          -- Cryptocurrency
```

Key insight: **PTA systems don't distinguish currencies from commodities**—they're all just units with quantities.

---

## Validation & Constraints

### Transaction Balance (All Systems)

Every transaction must sum to zero. This is the fundamental check.

### Balance Assertions (hledger, Beancount)

Assert expected balance at a point in time:

```
2024-01-15 balance Assets:Checking  $1,234.56
```

- **hledger**: Checked in date order
- **Beancount**: Checked at beginning of date
- **Ledger**: Order-dependent, less strict

### Account Open/Close (Beancount)

```
2024-01-01 open Assets:Checking USD
2024-12-31 close Assets:Checking
```

Beancount rejects postings to unopened or closed accounts.

### Commodity Constraints (Beancount)

Account can be restricted to certain commodities:

```
2024-01-01 open Assets:Bitcoin BTC
```

### Inventory Booking (Beancount)

When selling assets with cost basis, must match against existing lots:

| Method | Behavior |
|--------|----------|
| STRICT | Exact lot match required |
| FIFO | First-in-first-out |
| LIFO | Last-in-first-out |
| NONE | No matching (like Ledger) |

---

## Mathematical Foundations: The Pacioli Group

David Ellerman's work reveals the algebraic structure underlying double-entry bookkeeping.

### The Group of Differences

T-accounts can be formalized as **ordered pairs** [debit // credit]:

```
[x // y] where x, y ≥ 0
```

Operations:
- **Addition**: [a // b] + [c // d] = [a+c // b+d]
- **Identity**: [0 // 0]
- **Inverse**: inverse of [a // b] is [b // a]
- **Equality**: [a // b] = [c // d] iff a + d = b + c

This is the **Pacioli Group** P, isomorphic to the integers (or reals):

```
Debit isomorphism:  [x // y] ↦ x - y
Credit isomorphism: [x // y] ↦ y - x
```

### Why Pairs Instead of Signed Numbers?

Historical and practical reasons:

1. **Bookkeepers used unsigned numbers** (no negative amounts)
2. **T-accounts preserve provenance**: separate debit/credit trails
3. **Auditing**: can verify debits and credits independently
4. **Error detection**: cross-sum equality is a checksum

### Generalization to Vectors

Ellerman extends to the **multidimensional Pacioli Group** Pⁿ:

```
[x⃗ // y⃗] where x⃗, y⃗ ∈ ℝ≥0ⁿ
```

This handles multiple commodities simultaneously—each dimension is a different commodity.

### Category Theory Connection

Recent work (2025) formalizes accounting using category theory:

- **Limits**: verify constraints (balance equations)
- **Colimits**: aggregate (sum accounts)
- **Endofunctors**: model temporal evolution

Micro-level double-entry systems compose into macro-level accounting via categorical universals.

---

## Inventory and Position Tracking

Beancount distinguishes:

### Position

A position is units of a commodity with optional acquisition info:

```
25 AAPL {$150.00, 2024-01-15, "lot1"}
```

Components:
- Amount (25)
- Commodity (AAPL)
- Cost basis ($150.00)
- Acquisition date (2024-01-15)
- Label ("lot1")

### Inventory

An inventory is a collection of positions, functioning as a map:

```
Inventory = { Commodity × CostBasis → Quantity }
```

Two operations:
- **Augmentation** (buying): always creates new positions
- **Reduction** (selling): must match existing positions

This is crucial for capital gains calculation.

---

## Connection to Linear Logic

The parallels between PTA and linear logic are striking:

### Resource Semantics

| Plain Text Accounting | Linear Logic |
|-----------------------|--------------|
| Transaction balances to zero | Sequent balances (cut elimination) |
| Can't create value from nothing | No weakening (can't discard) |
| Can't duplicate value | No contraction (can't copy) |
| Value transfers, not copied | Linear implication (⊸) |
| Transaction = transformation | Proof = computation |

### The Conservation Principle

In linear logic: "Each assumption must be used exactly once."

In PTA: "Each dollar must come from somewhere and go somewhere."

Both enforce **resource conservation**.

### Tensor Product (⊗) as Transaction

A transaction transferring $100 from A to B:

```
Linear Logic:     [A] coin($, 100) ⊸ [B] coin($, 100)
PTA Transaction:  A: -$100, B: +$100
```

The tensor product combines resources; the transaction shows both sides.

### Linear Negation as Liability

Our sketch.md hypothesizes debt as linear negation:

```
coin(BTC, 0.5)⊥ = obligation to provide 0.5 BTC
```

In PTA, **liabilities are negative assets**—the same idea!

```
Assets:Cash        $1000
Liabilities:Loan  -$1000   ← "owes $1000"
```

The accounting equation A = L + E can be written:

```
A + L⊥ + E⊥ = 0   (where L⊥, E⊥ are liabilities/equity as negations)
```

---

## Relevance to CALC Research

### Validation for Our Design Decisions

Our sketch.md chose:

| Decision | PTA Validation |
|----------|----------------|
| Quantity as term `coin(BTC, 0.322)` | PTA: Amount is data, not type |
| Explicit authorization `A says ...` | PTA: Implicit (who enters data) |
| Currency as term | PTA: Commodity is just a symbol |
| Fixed-point 18 decimals | PTA: Arbitrary precision, commodity-specific |

PTA systems confirm that **quantity-as-data** is the right approach.

### What PTA Does Better

1. **Multi-commodity accounts**: A single account can hold BTC, ETH, USD
2. **Cost basis tracking**: Knows *when* and *at what price* acquired
3. **Lot matching**: FIFO/LIFO for tax purposes
4. **Balance assertions**: Check expected state at any point

### What We Could Borrow

1. **Hierarchical accounts**: `[Alice]:wallet:cold:btc` structure
2. **Transaction metadata**: dates, descriptions, tags
3. **Balance assertions**: periodic consistency checks
4. **The zero-sum invariant**: fundamental validation rule

### What We Add That PTA Lacks

1. **Ownership modalities**: `[Alice]` vs `[Bob]` as first-class
2. **Authorization logic**: Explicit `A says transfer(...)` proofs
3. **Atomic swaps**: Multi-party consensus in logic
4. **Proof search**: Automated derivation of valid transfers
5. **Linear logic foundation**: Formal semantics, not just software

### The Deeper Connection

PTA implements the *operational* version of what linear logic provides *logically*:

| PTA (Operational) | Linear Logic (Logical) |
|-------------------|------------------------|
| Transaction balances | Sequent cut-free |
| No copying amounts | No contraction |
| No deleting amounts | No weakening |
| Account = resource pool | Formula = resource |
| Journal = trace | Proof = derivation |

The Pacioli group structure is precisely the **group completion** of the monoid of non-negative resources—which is what linear logic's additive conjunction (⊕) provides!

---

## Open Questions

### 1. Is the Pacioli Group Related to Linear Logic's Additives?

The group of differences [x // y] feels like it should connect to:
- A ⊕ A⊥ (additive disjunction with negation)
- The "par" connective (⅋)

**TODO**: Study this connection formally.

### 2. How Do Balance Assertions Map to Logic?

Balance assertions are **invariants** checked at specific points:

```
2024-01-15 balance Assets:Checking $1,234.56
```

In logic, this might be a **predicate guard** or **precondition**:

```
check(date(2024-01-15), [Alice] coin($, 1234.56))
```

How do we formalize periodic invariant checking?

### 3. Can Lot Matching Be Expressed in Linear Logic?

FIFO/LIFO lot matching is a **strategy** for reducing inventory:

```
sell 10 AAPL → which lot to reduce?
```

This is like a **choice** in proof search—which cut to make first?

### 4. Multi-Commodity Accounts

PTA allows:
```
Assets:Wallet
  100 BTC
  500 ETH
```

In our notation:
```
[Alice] (coin(BTC, 100) ⊗ coin(ETH, 500))
```

Is tensor the right connective? Or should we use additive (&)?

---

## Summary

Plain text accounting provides a **battle-tested operational semantics** for resource tracking that has strong parallels to linear logic:

1. **Conservation** = No weakening + No contraction
2. **Double-entry** = Balanced sequents
3. **T-accounts** = Pacioli group (group of differences)
4. **Transactions** = Linear transformations (proofs)
5. **Liabilities** = Linear negation (obligations)

The algebraic structure (Pacioli group) and categorical formulations (limits, colimits) suggest a deep mathematical foundation that CALC could leverage.

**Key insight**: PTA systems have been doing "applied linear logic" for 500+ years without knowing it.

---

## References

### PTA Tools & Documentation
- [Plain Text Accounting](https://plaintextaccounting.org/)
- [Ledger CLI](https://ledger-cli.org/)
- [hledger](https://hledger.org/)
- [Beancount Documentation](https://beancount.github.io/docs/)
- [Beancount vs Ledger/hledger Comparison](https://beancount.github.io/docs/a_comparison_of_beancount_and_ledger_hledger.html)

### Mathematical Foundations
- [Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment" (arXiv)](https://arxiv.org/abs/1407.1898)
- [Ellerman, "Mathematics of Double Entry Bookkeeping"](https://www.ellerman.org/mathematics-of-double-entry/)
- [Macroeconomic Accounting via Category Theory (arXiv 2025)](https://arxiv.org/abs/2508.14132)

### Linear Logic
- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- [nLab: Linear Logic](https://ncatlab.org/nlab/show/linear+logic)
- [Wadler, "A Taste of Linear Logic"](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)

### Accounting Fundamentals
- [Wikipedia: Double-entry bookkeeping](https://en.wikipedia.org/wiki/Double-entry_bookkeeping)
- [Wikipedia: Accounting equation](https://en.wikipedia.org/wiki/Accounting_equation)

---

*Last updated: 2026-01-29*
