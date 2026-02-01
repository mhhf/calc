# Sketch: Modeling Coin Ownership in Linear Logic

This document explores design options for representing cryptocurrency ownership, transfers, and exchanges in CALC's linear logic framework.

---

## The Problem

Model these statements in linear logic:
1. `Alice owns 0.322 BTC`
2. `Alice sends 0.1 BTC to Bob`
3. `Alice sells Bob 0.1 BTC for 0.5 ETH`

Requirements:
- Conservation: coins can't be created or destroyed (except by minting/burning)
- Authorization: transfers require owner consent
- Atomicity: exchanges happen all-or-nothing
- Quantities: real-number amounts (or fixed-point)

---

## Design Space

### Dimension 1: Quantity Representation

| Option | Syntax | Example |
|--------|--------|---------|
| **(a) Grade on modality** | `[A]_q C` | `[Alice]_{0.322} BTC` |
| **(b) Term in predicate** | `[A] coin(C, q)` | `[Alice] coin(BTC, 0.322)` |
| **(c) Counted copies** | `[A] C ⊗ [A] C ⊗ ...` | 322 million satoshi facts |

**Decision: (b) Term in predicate**

Rationale:
- Simpler modal structure
- Quantities as terms allow FFI to arithmetic
- Matches Nomos/Move/Cardano implementations
- Conservation requires arithmetic reasoning anyway

### Dimension 2: Authorization Model

| Option | Mechanism | Example |
|--------|-----------|---------|
| **(a) Explicit "says"** | `A says transfer(...)` | `(Alice says ok) ⊗ [Alice] coin(...) ⊸ [Bob] coin(...)` |
| **(b) Implicit consumption** | Consuming `[A] φ` requires A's key | `[Alice] coin(...) ⊸ [Bob] coin(...)` |

**Decision: (a) Explicit "says"**

Rationale:
- Clear separation of resource and authorization
- Can model partial signatures, multi-sig
- Matches authorization logic literature (Garg et al.)
- Authorization itself can be linear (one-time) or exponential (standing permission)

### Dimension 3: Currency Representation

| Option | Syntax | Implication |
|--------|--------|-------------|
| **(a) Currency as type** | Different sorts: `BTC`, `ETH` | Type system prevents mixing |
| **(b) Currency as term** | `coin(currency, amount)` | More flexible, single coin type |

**Decision: (b) Currency as term**

Rationale:
- Allows currency to be a variable/parameter
- Simpler: one `coin` predicate, not one per currency
- Can still enforce non-mixing via predicates

### Dimension 4: Numeric Precision

| Option | Representation | Notes |
|--------|----------------|-------|
| **(a) Real numbers** | ℝ≥0 | Theoretical, may have precision issues |
| **(b) Integers (smallest unit)** | ℕ (satoshis, wei) | Matches actual blockchains |
| **(c) Fixed-point** | 18 decimal places | Practical compromise |

**Decision: (c) Fixed-point (18 decimals)**

Rationale:
- Matches Ethereum's standard (wei = 10⁻¹⁸ ETH)
- Avoids floating-point precision issues
- Integers under the hood, real-number presentation

### Dimension 5: Debt / Negative Quantities

**Open question.** Two approaches:

| Option | Representation | Example |
|--------|----------------|---------|
| **(a) Negative numbers** | Ring instead of semiring | `coin(BTC, -0.5)` = debt |
| **(b) Negated predicate** | Linear negation | `coin(BTC, 0.5)⊥` = obligation |

**Leaning toward: (b) Negated predicate**

Rationale:
- Linear negation already has "debt" semantics in the literature
- `A⊥` = "I owe you an A" or "obligation to provide A"
- Keeps quantities non-negative (simpler arithmetic)
- Needs deeper study (see Open Questions)

---

## Proposed Syntax

### Sorts

```
principal : Alice, Bob, ...
currency  : BTC, ETH, USD, ...
amount    : fixed-point (18 decimals)
formula   : linear logic formulas
```

### Core Predicates

```
coin(C, q)           -- A coin resource: currency C, amount q
                     -- Linear: must be used exactly once

[A] φ                -- Ownership modality: A owns/controls φ
                     -- From authorization logic

A says ψ             -- Authorization: A affirms ψ
                     -- Can be linear (one-time) or exponential (!)
```

### Derived Notions

```
-- Alice owns 0.322 BTC
[Alice] coin(BTC, 0.322)

-- Alice owes Bob 0.5 ETH (tentative, using linear negation)
[Alice] coin(ETH, 0.5)⊥
-- or equivalently: [Bob] has a claim on Alice for 0.5 ETH
```

---

## Inference Rules

### Splitting and Merging

Coins can be split or merged freely (no authorization needed):

```
Split:
─────────────────────────────────────────────────────────
[A] coin(C, q₁ + q₂)  ⊢  [A] coin(C, q₁) ⊗ [A] coin(C, q₂)

Merge:
─────────────────────────────────────────────────────────
[A] coin(C, q₁) ⊗ [A] coin(C, q₂)  ⊢  [A] coin(C, q₁ + q₂)
```

Conservation is enforced: `q₁ + q₂ = q₁ + q₂` (trivially).

### Transfer (with authorization)

```
Transfer:
───────────────────────────────────────────────────────────────────
(A says transfer(B, C, q)) ⊗ [A] coin(C, q)  ⊢  [B] coin(C, q)
```

- Requires A's explicit consent (`A says ...`)
- The authorization is consumed (linear) — one-time permission
- For standing permissions, use `!(A says transfer(B, C, q))`

### Exchange (atomic swap)

```
Exchange:
─────────────────────────────────────────────────────────────────────────────────
(A says swap(B,C₁,q₁,C₂,q₂)) ⊗ (B says swap(A,C₂,q₂,C₁,q₁)) ⊗
[A] coin(C₁, q₁) ⊗ [B] coin(C₂, q₂)
  ⊢
[B] coin(C₁, q₁) ⊗ [A] coin(C₂, q₂)
```

Both parties must consent. The swap is atomic — all or nothing.

---

## Example Derivations

### Example 1: Alice owns 0.322 BTC

Simply represented as:
```
[Alice] coin(BTC, 0.322)
```

### Example 2: Alice sends 0.1 BTC to Bob

Starting state:
```
[Alice] coin(BTC, 0.322)
```

Derivation:
```
[Alice] coin(BTC, 0.322)
  ⊢ [Alice] coin(BTC, 0.222) ⊗ [Alice] coin(BTC, 0.1)     -- Split

(Alice says transfer(Bob, BTC, 0.1)) ⊗ [Alice] coin(BTC, 0.1)
  ⊢ [Bob] coin(BTC, 0.1)                                   -- Transfer
```

Final state (after combining):
```
[Alice] coin(BTC, 0.222) ⊗ [Bob] coin(BTC, 0.1)
```

### Example 3: Alice sells Bob 0.1 BTC for 0.5 ETH

Starting state:
```
[Alice] coin(BTC, 0.1) ⊗ [Bob] coin(ETH, 0.5)
```

Derivation (using Exchange rule):
```
(Alice says swap(...)) ⊗ (Bob says swap(...)) ⊗
[Alice] coin(BTC, 0.1) ⊗ [Bob] coin(ETH, 0.5)
  ⊢
[Bob] coin(BTC, 0.1) ⊗ [Alice] coin(ETH, 0.5)
```

---

## Open Questions

### 1. Linear Negation as Debt?

In classical linear logic, negation has a "debt" or "obligation" interpretation:
- `A` = I have resource A
- `A⊥` = I owe resource A (obligation to provide A)

The key rules:
```
A ⊗ A⊥ ⊢ ⊥       -- Having A and owing A cancel out (to contradiction? or zero?)
⊢ A ⅋ A⊥          -- Can always produce "A or owe A" (trivial obligation)
```

**Questions to study:**
- Does `[Alice] coin(BTC, 0.5)⊥` mean "Alice owes 0.5 BTC"?
- How does ownership modality interact with negation?
- Is `[Alice] A⊥` the same as `([Alice] A)⊥`?
- What's the game-semantic interpretation?

**Research pointers:**
- Girard's original linear logic paper (negation as "anti-resources")
- Abramsky's game semantics for linear logic
- Mellies' work on tensorial logic

### 2. Interaction of [A] and says

We have two authorization mechanisms:
- `[A] φ` — ownership modality (A controls φ)
- `A says ψ` — affirmation modality (A asserts ψ)

How do they interact?
- Is `[A] (B says φ)` meaningful? (Alice owns Bob's assertion?)
- Is `A says ([B] φ)` meaningful? (Alice asserts Bob owns something?)
- What's `[A] [B] φ`? (Nested ownership?)

### 3. Multi-sig and Thresholds

How to express:
- `[Alice ∧ Bob] coin(BTC, 1.0)` — both must consent to spend
- `[2-of-{A,B,C}] coin(BTC, 1.0)` — any 2 of 3 can spend

The `says` approach handles this:
```
(Alice says ok) ⊗ (Bob says ok) ⊗ [Alice ∧ Bob] coin(...)  ⊢  ...
```

But what's the relationship between `[A ∧ B]` as a modality and `(A says) ⊗ (B says)`?

### 4. Ownership vs Possession

Subtle distinction:
- **Possession**: I have the private key (can sign)
- **Ownership**: I have the legal/logical right

In our model, `[A] coin(...)` conflates these. Do we need to separate them?

Example: Custodial wallet
- Exchange possesses coins (has keys)
- User owns coins (has claim)

### 5. Conservation as Axiom or Derived?

Should conservation be:
- **(a) Axiom**: The split/merge rules are primitive
- **(b) Derived**: From more fundamental arithmetic + linear logic

If derived, we need to axiomatize arithmetic in the logic. This connects to FFI questions (see `ffi-logics.md`).

---

## Connection to Existing Research

### Authorization Logic (Garg et al.)

Our `A says φ` comes from BL/BLL family. Key insight:
- Linear `says` = one-time authorization (consumed)
- Exponential `!(A says φ)` = standing permission

See: [[authorization-logic]]

### Nomos / Session Types

Nomos models assets as linear channels:
```
type token = /\ +{ transfer: address ^ token, burn: 1 }
```

Quantity is tracked as data, not in the type. Same as our approach.

The `acquire-release` discipline prevents re-entrancy — relevant for our atomic swaps.

See: [[nomos]]

### Graded Modal Types (Granule)

If we used approach (a) (quantity as grade), we'd have:
```
[Alice]_{0.322} BTC
```

This connects to Granule's `□_r A` where r is from a semiring.

The semiring for amounts would be (ℝ≥0, +, ×, 0, 1) or its fixed-point approximation.

See: [[QTT]]

### Move Language

Move's resource types:
```
struct Coin has store { value: u64 }
```

- `has store` = can be stored (linear)
- No `copy` or `drop` abilities
- Quantity is a field, not a type parameter

This validates our approach (b): quantity as term, not type.

---

## Next Steps

1. **Formalize the rules** in ll.json syntax
2. **Implement coin predicate** as new formula type
3. **Study linear negation** for debt semantics
4. **Prototype** simple transfer derivations
5. **Connect to multi-sig** via composite principals

---

## References

- [[authorization-logic]] — `says` modality, principals
- [[nomos]] — session types for smart contracts
- [[QTT]] — graded modal types
- [[multi-type-display-calculus]] — ownership modalities as types
- [[bibliography]] — full citations

---

*Last updated: 2026-01-29*
