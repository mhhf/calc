---
title: "Ownership Design: User-Centric Linear Logic for Digital Assets"
created: 2026-02-10
modified: 2026-02-10
summary: Comprehensive design for representing coin ownership, transfers, and atomic swaps using ownership modalities and linear logic with user-centric rather than contract-centric approach.
tags: [ownership, design, digital-assets, transfers, atomic-swaps]
category: "Ownership"
unique_contribution: "User-centric ownership modality [P] A for digital assets with transfer, split, merge, and atomic swap rules formalized in linear logic."
---

# Ownership Design: User-Centric Linear Logic for Digital Assets

Comprehensive design document for representing ownership, transfers, and exchanges in CALC's linear logic framework. Explores design space, formalizes rules, and provides worked examples.

> **See also:** [[authorization-logic]] for says/speaks-for modalities, [[multimodal-linear-logic]] for ownership modality design, [[financial-primitives]] for derivatives, [[linear-negation-debt]] for debt semantics, [[graded-resource-tracking]] for quantity grading.

---

## Table of Contents

1. [The Problem](#the-problem)
2. [Design Space](#design-space)
3. [The Core Question: User-Centric vs Contract-Centric](#the-core-question)
4. [User-Centric Ownership](#user-centric-ownership)
5. [Fresh Names and Resource Creation](#fresh-names-and-resource-creation)
6. [Contracts and Internal State](#contracts-and-internal-state)
7. [The Minimal Core](#the-minimal-core)
8. [Worked Examples](#worked-examples)
9. [Design Decisions Summary](#design-decisions-summary)
10. [Remaining Challenges](#remaining-challenges)
11. [References](#references)

---

## The Problem

Model these statements in linear logic:
1. `Alice owns 0.322 BTC`
2. `Alice sends 0.1 BTC to Bob`
3. `Alice sells Bob 0.1 BTC for 0.5 ETH`

Requirements:
- **Conservation**: coins can't be created or destroyed (except by minting/burning)
- **Authorization**: transfers require owner consent
- **Atomicity**: exchanges happen all-or-nothing
- **Quantities**: real-number amounts (or fixed-point)

---

## Design Space

### Dimension 1: Quantity Representation

| Option | Syntax | Decision |
|--------|--------|----------|
| Grade on modality | `[A]_q C` | ✗ |
| **Term in predicate** | `[A] coin(C, q)` | ✓ |
| Counted copies | `[A] C ⊗ [A] C ⊗ ...` | ✗ |

**Rationale**: Simpler modal structure. Quantities as terms allow FFI to arithmetic. Matches Nomos/Move/Cardano.

### Dimension 2: Authorization Model

| Option | Mechanism | Decision |
|--------|-----------|----------|
| **Explicit "says"** | `A says transfer(...)` | ✓ |
| Implicit consumption | Consuming `[A] φ` requires A's key | ✗ |

**Rationale**: Clear separation of resource and authorization. Can model partial signatures, multi-sig. Matches authorization logic literature.

### Dimension 3: Currency Representation

| Option | Syntax | Decision |
|--------|--------|----------|
| Currency as type | Different sorts: `BTC`, `ETH` | ✗ |
| **Currency as term** | `coin(currency, amount)` | ✓ |

**Rationale**: Allows currency to be a variable/parameter. One `coin` predicate, not one per currency.

### Dimension 4: Numeric Precision

| Option | Representation | Decision |
|--------|----------------|----------|
| Real numbers | ℝ≥0 | ✗ |
| Integers | ℕ (satoshis, wei) | ✗ |
| **Fixed-point** | 18 decimal places | ✓ |

**Rationale**: Matches Ethereum's standard. Avoids floating-point precision issues.

### Dimension 5: Debt / Negative Quantities

| Option | Representation | Decision |
|--------|----------------|----------|
| Negative numbers | Ring instead of semiring | ✗ |
| **Negated predicate** | `coin(BTC, 0.5)⊥` | ✓ (tentative) |

**Rationale**: Linear negation already has "debt" semantics. Keeps quantities non-negative.

---

## The Core Question

Two natural representations for "Alice owns 10 ETH":

| Representation | Meaning | Style |
|----------------|---------|-------|
| `[Alice] []_{10} eth` | Alice owns 10 of token-type `eth` | **User-centric** |
| `[eth] []_{10} balance(Alice)` | ETH contract records Alice's balance | **Contract-centric** |

**Why this matters:**
- Affects how transfers work
- Affects how contracts interact with assets
- Affects freshness and resource creation

---

## User-Centric Ownership

### The Intuition

```
[Alice] []_{10} eth
  │       │      │
  │       │      └── Token type (a name)
  │       └───────── Quantity (graded modality)
  └───────────────── Owner (ownership modality)
```

**Reading:** "Alice owns 10 units of eth"

### Transfer

```
[Alice] []_{10} eth ⊗ ⟨Alice⟩ transfer(Bob, 5, eth)
⊢
[Alice] []_{5} eth ⊗ [Bob] []_{5} eth
```

Clean! Alice's authorization + Alice's ownership → split ownership.

### Split and Merge

Coins can be split or merged freely (no authorization needed):

```
Split:
─────────────────────────────────────────────────────────
[A] coin(C, q₁ + q₂)  ⊢  [A] coin(C, q₁) ⊗ [A] coin(C, q₂)

Merge:
─────────────────────────────────────────────────────────
[A] coin(C, q₁) ⊗ [A] coin(C, q₂)  ⊢  [A] coin(C, q₁ + q₂)
```

### Exchange (Atomic Swap)

```
(A says swap(B,C₁,q₁,C₂,q₂)) ⊗ (B says swap(A,C₂,q₂,C₁,q₁)) ⊗
[A] coin(C₁, q₁) ⊗ [B] coin(C₂, q₂)
  ⊢
[B] coin(C₁, q₁) ⊗ [A] coin(C₂, q₂)
```

Both parties must consent. The swap is atomic — all or nothing.

### What Prevents Counterfeiting?

**Principle:** You can only create `[A] []_r T` if:
1. You introduced T as a fresh name (minting), OR
2. You received `[A] []_r T` through a valid derivation (transfer)

The **logic itself** prevents counterfeiting. There's no rule that produces tokens from nothing.

---

## Fresh Names and Resource Creation

### The Freshness Principle

**Principle:** Resources can be created if and only if the token type name is fresh.

When processing `⟨A⟩ create_token(fresh, n)`:
1. Generate fresh name `t` (never used before)
2. Create `[t] !is_token`
3. Create `[A] []_n t`

Since `t` is fresh, this isn't counterfeiting — it's legitimate creation.

### What "Fresh" Means

A name is fresh if it has never appeared in:
- Any resource in the pool
- Any past transaction
- Any rule definition

### Fresh Name Generation Options

| Option | Mechanism |
|--------|-----------|
| **Implicit in `[fresh]`** (chosen) | Server substitutes fresh names |
| Core primitive | `fresh_name(n)` linear resource |
| Hash-based | User picks, server rejects collisions |

### Is `[T] !is_token` Necessary?

**Short answer:** No, but it's useful.

Freshness alone prevents counterfeiting. The marker serves:
1. **Coordination** — agree on "the real" token
2. **Extensibility** — attach metadata, custom rules
3. **Discovery** — query "all token types"

**Recommendation:** Make `[T] !is_token` optional. Minimal token creation:
```
⟨A⟩ mint(fresh, n)  ⊢  [A] []_n fresh
```

---

## Contracts and Internal State

### When Contracts Need to Hold Assets

For atomic swaps, AMMs, escrow, the contract needs to hold assets during the protocol.

### Deposit Pattern

When Alice deposits into a contract, ownership transfers:

```
[Alice] []_{10} eth ⊗ ⟨Alice⟩ deposit(swap, 10, eth)
⊢
[swap] []_{10} eth ⊗ [swap] credited(Alice, 10, eth)
```

### Withdraw Pattern

```
[swap] []_{10} eth ⊗ [swap] credited(Alice, 10, eth) ⊗ ⟨Alice⟩ withdraw(swap, 10, eth)
⊢
[Alice] []_{10} eth
```

### Contract Creation with Deposit (WITH Clause)

```
⟨Alice⟩ [fresh] body  WITH  resources
⊢
[n] body[n/fresh] ⊗ [n] resources[n/fresh]
```

This is a single atomic operation that:
1. Generates fresh name `n`
2. Creates the contract body (rules, state) scoped to `[n]`
3. Deposits the resources into `[n]`

### Rules Inside Contracts

Rules are **persistent implications** `!(P ⊸ Q)` in the pool. They're global but patterns handle scoping:

```
[swap] !([swap] escrowed(A, r, T) ⊗ condition ⊸ result)
```

The rule is global but patterns require `[swap]` wrappers.

### Cross-Contract Calls

Contracts don't "call" each other. They post resources that other rules consume:

```
-- Contract A posts a request
[A] request_from(A, B, action, args)

-- Contract B has a rule that consumes it
[B] !(request_from(A, B, action, args) ⊸ handle(B, A, action, args))
```

This is message-passing, not procedure calls.

---

## The Minimal Core

**Connectives:**
- `A ⊗ B` — multiplicative conjunction (tensor)
- `A ⊸ B` — linear implication (lollipop)
- `!A` — of course (persistence)
- `[P] A` — ownership modality (P owns A)
- `⟨P⟩ A` — authorization modality (P authorizes A)
- `[]_r A` — graded modality (quantity r of A)

**Core Rules:**

1. **Creation** (generates fresh names):
```
⟨A⟩ [fresh] body  WITH  resources
⊢
[n] body[n/fresh] ⊗ [n] resources[n/fresh]
```

2. **Transfer** (moves ownership):
```
[A] X ⊗ ⟨A⟩ transfer(B, X)  ⊢  [B] X
```

3. **Rule Application** (forward-chaining):
```
!(P ⊸ Q) ⊗ P  ⊢  !(P ⊸ Q) ⊗ Q
```

Everything else (tokens, swaps, AMMs) is built from these primitives.

---

## Worked Examples

### Simple Token Creation

Alice creates a new token "ACME" with 1 million supply:

```
⟨Alice⟩ mint(fresh, 1000000)
⊢
[Alice] []_{1000000} fresh
```

### Transfer

Alice sends 50 tokens to Bob:

```
Pool:
[Alice] []_{1000000} t₁

Alice posts:
⟨Alice⟩ transfer(Bob, 50, t₁)

Transfer rule fires:
[Alice] []_{1000000} t₁ ⊗ ⟨Alice⟩ transfer(Bob, 50, t₁)
⊢
[Alice] []_{999950} t₁ ⊗ [Bob] []_{50} t₁
```

### Atomic Swap

**Step 1: Alice creates swap contract with deposit**
```
Alice posts:
⟨Alice⟩ [fresh] (
  !([fresh] []_{1} btc ⊗ ⟨Bob⟩ accept(fresh)
    ⊸
    [Alice] []_{1} btc ⊗ [Bob] []_{10} eth) ⊗
  !(⟨Alice⟩ cancel(fresh) ⊗ [fresh] []_{10} eth
    ⊸
    [Alice] []_{10} eth)
)  WITH  [Alice] []_{10} eth

Pool becomes:
[s] !(accept_rule) ⊗ [s] !(cancel_rule) ⊗ [s] []_{10} eth ⊗ [Bob] []_{1} btc
```

**Step 2a: Bob accepts**
```
Bob posts:
⟨Bob⟩ accept(s)  WITH  [Bob] []_{1} btc

Accept rule fires:
Final pool: [Alice] []_{1} btc ⊗ [Bob] []_{10} eth  ✓
```

**Step 2b (alternative): Alice cancels**
```
Alice posts:
⟨Alice⟩ cancel(s)

Cancel rule fires:
Final pool: [Alice] []_{10} eth ⊗ [Bob] []_{1} btc  (back to original)
```

### AMM (Constant Product)

```
⟨Creator⟩ [fresh] (
  !([fresh] []_x eth ⊗ [fresh] []_y usdc ⊗
    [A] []_dx eth ⊗ ⟨A⟩ swap(fresh, eth, dx)
    ⊸
    [fresh] []_{x+dx} eth ⊗ [fresh] []_{y-dy} usdc ⊗
    [A] []_dy usdc)
    WHERE dy = y - (x*y)/(x+dx)
)  WITH  ([Creator] []_{1000} eth ⊗ [Creator] []_{1000000} usdc)
```

---

## Design Decisions Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Ownership representation | User-centric `[Alice] []_r T` | Intuitive, composable |
| Token type anchor | Optional `[T] !is_token` | Freshness suffices for safety |
| Fresh name generation | Implicit in `[fresh]` syntax | Simple, sufficient |
| Contract asset holding | `WITH` clause for atomic deposit | Clean, atomic |
| Rule scoping | Global, patterns handle scoping | Flexible, explicit |
| Rules | Persistent implications `!(P ⊸ Q)` | Unified with logic |

### Key Observations

1. **User-centric ownership is primary.** Users hold `[User] []_r token` directly.
2. **Contracts hold assets temporarily.** During a swap, `[swap] []_r token` is escrow.
3. **WITH clause is essential.** Enables atomic deposit during contract creation.
4. **Fresh names are token/contract identities.** No separate "is_token" marker needed.
5. **Rules are just persistent implications.** No special "rule" type needed.

---

## Remaining Challenges

### Arithmetic Constraints

AMM example used `WHERE dy = y - (x*y)/(x+dx)`. Options:

| Option | Mechanism |
|--------|-----------|
| **FFI** (recommended) | External oracle computes |
| Arithmetic as resources | Complex but pure |
| Graded modality operations | Requires grade expression computation |

### Time and Expiration

Options and futures need expiration:

| Option | Mechanism |
|--------|-----------|
| **External time oracle** (recommended) | `⟨Oracle⟩ now(t)` |
| Stages (Ceptre-style) | Time advances between stages |

### Proving Conservation

**Theorem (No Counterfeiting):**
If token `t` is created with supply `n`, the total of `[]_r t` across all owners equals `n`.

**Proof sketch:**
- Creation: `⟨A⟩ mint(fresh, n) ⊢ [A] []_n fresh` — total is n
- Transfer: preserves total
- No other rules create `[]_r T` from nothing

### Attack Vectors

1. **Front-running**: Commit-reveal schemes or accept as feature
2. **Reentrancy**: Not directly possible (message-passing, not calls)
3. **Integer overflow**: Use arbitrary precision (BigInt)

---

## Open Questions

### Linear Negation as Debt?

In classical linear logic:
- `A` = I have resource A
- `A⊥` = I owe resource A (obligation)

**Questions to study:**
- Does `[Alice] coin(BTC, 0.5)⊥` mean "Alice owes 0.5 BTC"?
- How does ownership modality interact with negation?
- Is `[Alice] A⊥` the same as `([Alice] A)⊥`?

### Multi-sig and Thresholds

How to express:
- `[Alice ∧ Bob] coin(BTC, 1.0)` — both must consent
- `[2-of-{A,B,C}] coin(BTC, 1.0)` — any 2 of 3

The `says` approach handles this:
```
(Alice says ok) ⊗ (Bob says ok) ⊗ [Alice ∧ Bob] coin(...)  ⊢  ...
```

### Ownership vs Possession

Subtle distinction:
- **Possession**: I have the private key (can sign)
- **Ownership**: I have the legal/logical right

In our model, `[A] coin(...)` conflates these. May need separation for custodial scenarios.

---

## References

### Authorization Logic
- [[authorization-logic]] — `says` modality, principals
- `dev/ownership-authorization-plan.md` — implementation plan

### Related Systems
- [[nomos]] — session types for smart contracts
- [[graded-resource-tracking]] — graded modal types
- [[multi-type-display-calculus]] — ownership modalities as types

### Move Language
Move's resource types validate our approach:
```
struct Coin has store { value: u64 }
```
- `has store` = can be stored (linear)
- Quantity is a field, not a type parameter

---

*Created: 2026-02-10 (merged from sketch.md and ownership-representation.md)*
*Status: Design converging — ready for formalization*
