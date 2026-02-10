---
title: "Financial Primitives in CALC"
created: 2026-02-10
modified: 2026-02-10
summary: Mapping financial derivatives (futures, options, swaps, leverage) to linear logic connectives and additive choice for modeling market mechanisms.
tags: [finance, derivatives, options, markets, linear-logic]
---

# Financial Primitives in CALC

Research on how basic financial derivatives and market mechanisms map to linear logic / CALC machinery.

> **See also:** [[ownership-design]] for ownership representation, [[linear-negation-debt]] for debt semantics, [[accounting-foundations]] for mathematical foundations.

---

## Table of Contents

1. [Overview](#overview)
2. [Financial Primitives Analysis](#financial-primitives-analysis)
   - [Futures Contracts](#1-futures-contracts)
   - [Options](#2-options)
   - [Swaps](#3-swaps-interest-rate-currency-etc)
   - [Leverage](#4-leverage)
   - [Markets / Order Books](#5-markets--order-books)
   - [Auctions](#6-auctions)
3. [Summary: What Maps Naturally](#summary-what-maps-naturally)
4. [Additional Features CALC Needs](#what-additional-features-calc-needs)
5. [Peyton-Jones Combinators](#the-peyton-jones-combinators)
6. [Recommendations](#recommendations)
7. [References](#references)

---

## Overview

CALC already models:
- **Ownership:** `[Alice] coin(BTC, 0.5)`
- **Transfer:** `[Alice] A ⊸ [Bob] A`
- **Atomic Swap:** `[Alice] A ⊗ [Bob] B ⊸ [Alice] B ⊗ [Bob] A`

Can we extend this to richer financial primitives?

---

## Financial Primitives Analysis

### 1. Futures Contracts

**Definition:** Obligation to buy/sell an asset at a future date at a predetermined price.

**Structure:**
```
Future(underlying, quantity, price, expiry, direction)
```

**Linear Logic Encoding:**

A future is a **deferred linear implication** with a time constraint:

```
-- Long future (obligation to buy)
[Alice] cash(USD, price) ⊸_{at_expiry} [Alice] coin(underlying, quantity)

-- Short future (obligation to sell)
[Alice] coin(underlying, quantity) ⊸_{at_expiry} [Alice] cash(USD, price)
```

**What's needed:**
- **Temporal modality:** `⊸_{at_time}` (can only exercise at specific time)
- **Obligation vs right:** Future is OBLIGATION (must execute), not optional

**Encoding without time:**
```
-- Future as a pair of obligations (one for each party)
[Alice] obligation(buy, BTC, 1.0, 50000 USD, Dec-2026)
⊗
[Bob] obligation(sell, BTC, 1.0, 50000 USD, Dec-2026)
```

At expiry, these obligations must be settled:
```
settlement:
  [Alice] obligation(buy, ...) ⊗ [Bob] obligation(sell, ...) ⊗
  [Alice] cash(USD, 50000) ⊗ [Bob] coin(BTC, 1.0)
  ⊸
  [Alice] coin(BTC, 1.0) ⊗ [Bob] cash(USD, 50000)
```

**Fit with CALC:** MEDIUM — needs temporal extension or explicit obligation type.

---

### 2. Options

**Definition:** Right (not obligation) to buy (call) or sell (put) at a strike price.

**Structure:**
```
Option(underlying, quantity, strike, expiry, type: Call|Put)
```

**Linear Logic Encoding:**

Options are about **CHOICE** — this maps to additive connectives!

```
-- Call option (right to buy)
call_option : [Alice] (
  (cash(USD, strike) ⊸ coin(underlying, quantity))  -- exercise
  &                                                   -- internal choice
  1                                                   -- let expire
)

-- Put option (right to sell)
put_option : [Alice] (
  (coin(underlying, quantity) ⊸ cash(USD, strike))  -- exercise
  &
  1                                                   -- let expire
)
```

**Key insight:** Options use **additive conjunction (&)** — the holder chooses!
- & = "I can choose which branch"
- The other branch is discarded

**Premium:** The option itself has value (premium), paid upfront:
```
-- Buying a call option
buy_call:
  [Alice] cash(USD, premium) ⊗ [Bob] call_option(...)
  ⊸
  [Alice] call_option(...) ⊗ [Bob] cash(USD, premium)
```

**Fit with CALC:** GOOD — additive & models choice naturally!

---

### 3. Swaps (Interest Rate, Currency, etc.)

**Definition:** Agreement to exchange cash flows over time.

**Structure:**
```
Swap(leg1, leg2, schedule)
```

**Linear Logic Encoding:**

We already have atomic swaps! Swaps generalize to sequences:

```
-- Single-period swap (atomic swap)
[Alice] A ⊗ [Bob] B ⊸ [Alice] B ⊗ [Bob] A

-- Multi-period swap (iterated)
swap_period_1 ⊗ swap_period_2 ⊗ ... ⊗ swap_period_n
```

**For interest rate swaps:**
```
-- Fixed-for-floating swap
-- Alice pays fixed, receives floating
-- Bob pays floating, receives fixed

period_i:
  [Alice] cash(USD, fixed_amount) ⊗ [Bob] cash(USD, float_amount_i)
  ⊸
  [Alice] cash(USD, float_amount_i) ⊗ [Bob] cash(USD, fixed_amount)
```

**What's needed:**
- **Scheduling:** Link periods together
- **Netting:** Typically only net difference exchanged
- **Variable rates:** `float_amount_i` depends on external rate

**Fit with CALC:** GOOD — swaps are iterated atomic swaps.

---

### 4. Leverage

**Definition:** Amplified exposure, typically via borrowing.

**Structure:**
```
Leverage(base_position, multiplier, collateral)
```

**Linear Logic Encoding:**

Leverage involves **debt** (linear negation):

```
-- 2x leverage on BTC
-- Alice puts up 1 BTC collateral
-- Borrows 1 BTC worth of USD
-- Buys 1 more BTC
-- Total exposure: 2 BTC

[Alice] coin(BTC, 1.0)                     -- collateral
⊗ debt(Alice, lender, USD, btc_price)      -- borrowed funds
⊗ [Alice] coin(BTC, 1.0)                   -- additional position from loan
```

**Liquidation:**
```
-- If BTC price drops, collateral insufficient
-- Liquidation rule:
liquidate:
  [Alice] coin(BTC, 1.0) ⊗ debt(Alice, lender, USD, amount)
  ⊗ (btc_price < liquidation_threshold)    -- external condition
  ⊸
  [lender] coin(BTC, 1.0) ⊗ settled
```

**What's needed:**
- **Debt type** (already researched)
- **External price oracle**
- **Conditional execution**

**Fit with CALC:** MEDIUM — needs debt + oracles.

---

### 5. Markets / Order Books

**Definition:** Mechanism for price discovery via bid/ask matching.

**Structure:**
```
Market(base_asset, quote_asset, order_book)
Order(direction: Buy|Sell, price, quantity, owner)
```

**Linear Logic Encoding:**

An order book is a **collection of offers**:

```
-- Limit buy order (bid)
bid: [Alice] cash(USD, price * quantity) ⊸ [Alice] coin(BTC, quantity)

-- Limit sell order (ask)
ask: [Bob] coin(BTC, quantity) ⊸ [Bob] cash(USD, price * quantity)
```

**Order matching** is finding compatible orders:
```
match:
  [Alice] cash(USD, p) ⊗ [Bob] coin(BTC, q)
  ⊗ (alice_bid_price ≥ bob_ask_price)    -- price compatibility
  ⊸
  [Alice] coin(BTC, q) ⊗ [Bob] cash(USD, p)
```

**Order book as formula:**
```
order_book = (bid₁ & bid₂ & ... & bidₙ) ⊗ (ask₁ & ask₂ & ... & askₘ)
```

Using & means "one of these" can be selected.

**What's needed:**
- **Aggregation** of orders
- **Price priority** (best price matches first)
- **Time priority** (earlier orders match first)

**Fit with CALC:** PARTIAL — basic matching works, priority ordering needs extension.

---

### 6. Auctions

**Definition:** Price discovery via competitive bidding.

**Types:**
- **English:** Ascending price, highest bidder wins
- **Dutch:** Descending price, first taker wins
- **Sealed-bid:** Hidden bids, various rules

**Linear Logic Encoding:**

**English auction (ascending):**
```
-- Bid is a potential purchase
bid: [Alice] cash(USD, bid_amount) ⊸ [Alice] item

-- Winner is highest bidder
-- Others get refunds (their bids are "returned")
auction_result:
  (bid₁ ⊕ bid₂ ⊕ ... ⊕ bidₙ)    -- external choice: one wins
```

Using ⊕ (additive disjunction) = "environment chooses which"
The auction mechanism is the "environment" that chooses the winner.

**Dutch auction (descending):**
```
-- Price starts high, decreases
-- First to accept wins
dutch_round:
  offer(price_t) & proceed_to_next_round

-- If accepted:
accept: [Alice] cash(USD, price_t) ⊸ [Alice] item

-- If declined:
decline: offer(price_{t+1})
```

**Sealed-bid auction:**
```
-- All bids are committed
committed_bids = commit(bid₁) ⊗ commit(bid₂) ⊗ ... ⊗ commit(bidₙ)

-- Reveal phase
reveal:
  committed_bids ⊸ revealed_bids ⊸ winner_selection
```

**What's needed:**
- **External choice** (⊕) for winner selection
- **Commitment schemes** for sealed bids
- **Time/phase structure**

**Fit with CALC:** PARTIAL — needs choice + commitment.

---

### 7. Bid/Ask Spread

**Definition:** Difference between best buy and sell prices.

```
spread = best_ask - best_bid
```

This is a **derived quantity**, not a primitive.

In CALC, the spread emerges from the order book state.

---

### 8. Put/Call (as Composite)

Already covered under Options:
- **Call:** Right to buy at strike
- **Put:** Right to sell at strike

**Put-Call Parity:**
```
call + cash(strike) = put + underlying
```

This is a **theorem** in finance that should be provable in CALC!

```
-- If we have:
-- call: (cash(strike) ⊸ underlying) & 1
-- put: (underlying ⊸ cash(strike)) & 1

-- And the underlying + cash(strike)
-- We should be able to derive the parity relation
```

---

## Summary: What Maps Naturally

| Primitive | Linear Logic | Fit | Needs |
|-----------|--------------|-----|-------|
| **Futures** | Deferred ⊸ | MEDIUM | Temporal modality |
| **Options** | A ⊸ B & 1 | GOOD | Additive & (have it!) |
| **Swaps** | Iterated atomic swap | GOOD | Scheduling |
| **Leverage** | Position + debt | MEDIUM | Debt type + oracles |
| **Markets** | Collection of offers | PARTIAL | Priority ordering |
| **Auctions** | Bids with ⊕ | PARTIAL | Commitment, phases |

---

## What Additional Features CALC Needs

### 1. Temporal Modalities

For futures, options expiry, schedules:

```
A ⊸_{at_time} B      -- can only use at specific time
□_{until_time} A     -- A available until time
◇_{after_time} A     -- A becomes available after time
```

**Research:** Temporal linear logic, Linear Temporal Logic (LTL)

### 2. External Oracles / Conditionals

For leverage liquidation, floating rates:

```
A ⊗ (condition) ⊸ B    -- conditional linear implication
oracle(price_feed) : □ price(BTC, USD)   -- external data
```

**Research:** FFI for logics, oracle patterns

### 3. Commitment Schemes

For sealed-bid auctions, privacy:

```
commit(v) : Commitment    -- hides value v
reveal(c, v) ⊸ (c = commit(v))  -- proves opening
```

**Research:** Cryptographic commitments, zero-knowledge

### 4. Aggregation / Collections

For order books, portfolios:

```
bag(A) : Type    -- multiset of A
fold : bag(A) ⊗ (A ⊗ B ⊸ B) ⊗ B ⊸ B    -- aggregate
```

**Research:** Linear containers, graded types with bag semiring

---

## The Peyton-Jones Combinators

Reference: [Composing Contracts](https://www.microsoft.com/en-us/research/publication/composing-contracts-an-adventure-in-financial-engineering/)

Peyton-Jones, Eber, and Seward defined ~10 combinators for financial contracts:

| Combinator | Meaning |
|------------|---------|
| `zero` | Worthless contract |
| `one(k)` | Receive 1 unit of currency k |
| `give(c)` | Obligations reversed |
| `and(c₁, c₂)` | Both contracts |
| `or(c₁, c₂)` | Choice of contract |
| `cond(o, c₁, c₂)` | Conditional |
| `scale(o, c)` | Scale by observable |
| `when(o, c)` | Acquire when condition |
| `anytime(o, c)` | American option |
| `until(o, c)` | Contract until condition |

**Connection to CALC:**

| Combinator | CALC Equivalent |
|------------|-----------------|
| `zero` | 1 (unit) |
| `one(k)` | coin(k, 1) |
| `give(c)` | Linear negation? Or role swap |
| `and(c₁, c₂)` | c₁ ⊗ c₂ |
| `or(c₁, c₂)` | c₁ & c₂ (holder chooses) or c₁ ⊕ c₂ (counterparty chooses) |
| `cond(o, c₁, c₂)` | Needs oracle extension |
| `scale(o, c)` | Needs graded types |
| `when(o, c)` | Temporal modality |
| `anytime(o, c)` | Temporal + choice |
| `until(o, c)` | Temporal modality |

**Key insight:** Many combinators need temporal or oracle extensions that CALC doesn't currently have.

---

## Recommendations

### Short-term

1. **Model options using &** — additive conjunction gives choice to holder
2. **Model swaps as iterated atomic swaps** — already have the primitive
3. **Add explicit debt type** — for leverage, lending

### Medium-term

1. **Add temporal modalities** — for futures, expiry, schedules
2. **Add oracle mechanism** — for external prices, conditions
3. **Study LTL integration** — temporal logic for finance

### Long-term

1. **Full Peyton-Jones combinator library** — as CALC primitives
2. **Formal verification of financial identities** — put-call parity, etc.
3. **Integration with ACTUS** — standard financial contract types

---

## References

### Financial Contract DSLs

- [Peyton-Jones et al., Composing Contracts](https://www.microsoft.com/en-us/research/publication/composing-contracts-an-adventure-in-financial-engineering/) — Seminal paper
- [LexiFi MLFi](https://www.lexifi.com/company/technology/) — Industrial implementation
- [ACTUS](https://www.actusfrf.org/) — Algorithmic Contract Types

### Temporal Logic and Finance

- [ACTUS + LTL verification](https://medium.com/casperblockchain/finance-as-a-reactive-system-verifying-actus-traces-with-linear-temporal-logic-190ddc2e02e5)
- [Temporal Type Theory](https://arxiv.org/abs/1710.10258) — Topos-theoretic approach

### Linear Logic

- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- Girard, "Linear Logic" (1987)

---

*Last updated: 2026-01-29*
