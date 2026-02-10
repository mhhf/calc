# Linear Negation as Debt Semantics

This document explores the interpretation of linear negation (A⊥) as "debt" or "obligation," and its relevance to CALC's coin ownership modeling.

> **See also:** [[accounting-foundations]] for Pacioli group and conservation, [[financial-primitives]] for derivative modeling, [[ownership-design]] for coin ownership, [[ludics-and-orthogonality]] for game semantics and orthogonality.

---

## Table of Contents

1. [Overview](#overview)
2. [Formal Properties](#the-formal-properties)
3. [Interpretations of A⊥](#interpretations-of-a)
4. [The Debt Interpretation](#the-debt-interpretation)
5. [Application to CALC](#application-to-calc)
6. [Connection to Accounting](#connection-to-accounting)
7. [Classical vs Intuitionistic](#classical-vs-intuitionistic-linear-logic)
8. [Game-Semantic Perspective](#game-semantic-perspective)
9. [Open Questions](#open-questions)
10. [Summary](#summary)
11. [References](#references)

---

## Overview

In classical linear logic, every formula A has a **dual** A⊥ (read "A perp" or "A dual"). Unlike classical negation (¬A = A → ⊥), linear negation is:

1. **Involutive**: (A⊥)⊥ = A
2. **Constructive**: Despite being involutive, it has computational content
3. **Resource-sensitive**: A⊥ represents a "dual resource" or "counter-resource"

The key insight for CALC: **A⊥ can be interpreted as an obligation to provide A** — debt, not possession.

---

## The Formal Properties

### Involution

The defining property of linear negation:

```
(A⊥)⊥ ≡ A
```

This differs from intuitionistic negation (¬¬A ≢ A) and matches classical negation's double-negation elimination.

### De Morgan Laws

Linear negation distributes over all connectives via De Morgan duality:

```
(A ⊗ B)⊥ ≡ A⊥ ⅋ B⊥     -- tensor ↔ par
(A ⅋ B)⊥ ≡ A⊥ ⊗ B⊥
(A & B)⊥ ≡ A⊥ ⊕ B⊥     -- with ↔ plus
(A ⊕ B)⊥ ≡ A⊥ & B⊥
(!A)⊥ ≡ ?A⊥            -- of-course ↔ why-not
(?A)⊥ ≡ !A⊥
1⊥ ≡ ⊥                 -- units
⊥⊥ ≡ 1
```

### Linear Implication

Linear implication is defined via negation and par:

```
A ⊸ B  ≡  A⊥ ⅋ B
```

Equivalently:
```
A ⊸ B  ≡  (A ⊗ B⊥)⊥
```

---

## Interpretations of A⊥

### 1. Girard's "Male/Female Plug" Analogy

Girard's original intuition:

> "Think of a sequent Γ as the interface of some electronic equipment... the negation corresponds to the complementarity between male and female plugs."

- A = male plug (provides)
- A⊥ = female plug (receives)
- A proof is "equipment" that connects compatible interfaces
- The axiom `⊢ A, A⊥` is like an "extension cord"

### 2. Action/Reaction Duality

From Girard:

> "Linear negation expresses a duality, a change of standpoint: action of type A = reaction of type A⊥"

Other formulations:
- Output/Input
- Answer/Question
- Supply/Demand
- Production/Consumption

### 3. Programs vs Counter-Programs

In computational interpretations:

```
A     = program of type A
A⊥    = counter-program (environment) for A
```

A and A⊥ are "syntactically equal but differ in the class of counter-programs allowed to interact with them."

### 4. Game Semantics: Player/Opponent Role Reversal

In game semantics (Blass, Abramsky, Hyland-Ong):

```
A     = game where Player has a winning strategy
A⊥    = same game with Player/Opponent roles swapped
```

- Negation = "interchange the roles of the two players"
- If A is "Proponent wins", then A⊥ is "Opponent wins"

### 5. Session Types: Dual Channel Endpoints

In the Caires-Pfenning correspondence:

```
A     = session type for one endpoint
A⊥    = session type for the dual endpoint
```

If channel c has type A on one end, it has type A⊥ on the other.

- A = output capability (send)
- A⊥ = input capability (receive)

### 6. Demand/Supply Duality

From the Stanford Encyclopedia:

> "A function of type α ⊸ β transforms a demand for β into a demand for α."

The contrapositive:
```
A ⊸ B  ≡  B⊥ ⊸ A⊥
```

Reads as: "Consuming A to produce B" ≡ "Transforming a demand for B into a demand for A"

---

## The Debt Interpretation

### Core Idea

```
A      = "I have resource A"
A⊥     = "I owe resource A" (obligation to provide A)
```

This interpretation is **not explicitly stated** in most linear logic literature but is **implicit** in:
- The male/female plug analogy (receiving = expecting input)
- The supply/demand duality
- The game-theoretic role reversal (Opponent = the party who "claims" the resource)

### Why Involution Makes Sense

```
(A⊥)⊥ = A
```

Interprets as:
```
"Owing an obligation to provide A" = "Having A"
```

Or equivalently:
```
"A debt of a debt" = "An asset"
```

This matches financial intuition! If Alice owes Bob, and Bob owes Carol, then (after settlement) Alice effectively owes Carol.

### Settlement: A ⊗ A⊥

In one-sided classical linear logic, we have the axiom:

```
⊢ A, A⊥    (identity/axiom rule)
```

Interpreted: "Having A and owing A is trivially satisfiable" — they cancel out.

In our setting, this becomes:

```
coin(BTC, q) ⊗ coin(BTC, q)⊥  ⊢  1
```

Meaning: "Having 0.5 BTC and owing 0.5 BTC cancel to unit (nothing)."

This is exactly **debt settlement**!

---

## Application to CALC

### Modeling Debt

From sketch.md, we proposed:

```
[Alice] coin(BTC, 0.5)⊥  = "Alice owes 0.5 BTC"
```

This keeps quantities non-negative while expressing debt via linear negation.

### Key Questions Resolved

**Q1: Does `[Alice] coin(BTC, 0.5)⊥` mean "Alice owes 0.5 BTC"?**

**A:** Yes, under the debt interpretation. The negation indicates obligation rather than possession.

**Q2: How does ownership modality interact with negation?**

**A:** Two possible readings:

```
[Alice] (coin(BTC, q)⊥)    -- Alice owns an obligation
([Alice] coin(BTC, q))⊥    -- Obligation to provide Alice's coin
```

These are **not the same**! We need to decide which makes sense.

**Proposal:** Use `[Alice] (A⊥)` to mean "Alice has an obligation."

The alternative `([Alice] A)⊥` would mean "someone has a claim against Alice's asset" — more like a lien than Alice's own debt.

**Q3: Is `[Alice] A⊥` the same as `([Alice] A)⊥`?**

**A:** In general, **no**. Modalities don't commute with negation:

```
[Alice] (A⊥) ≠ ([Alice] A)⊥
```

The first is "Alice controls an obligation."
The second is "The negation of Alice controlling A" = "Alice doesn't control A" or "There's a claim on Alice's A."

For debt modeling, prefer: `[Alice] (coin(C,q)⊥)` = "Alice has a debt of q units of C."

### The Settlement Rule

We can derive a settlement rule:

```
Settlement:
─────────────────────────────────────────────────────────
[A] coin(C, q) ⊗ [A] coin(C, q)⊥  ⊢  1
```

"If Alice has 0.5 BTC and owes 0.5 BTC, they cancel out."

This follows from the linear logic axiom `⊢ A, A⊥` plus the fact that both are under `[Alice]`.

### Borrowing / Creating Debt

To model borrowing:

```
Borrow (create debt):
─────────────────────────────────────────────────────────
(Alice says borrow(q, C)) ⊢ [Alice] coin(C, q) ⊗ [Alice] coin(C, q)⊥
```

Alice creates both an asset (the borrowed coins) and a liability (the debt). Net value: zero.

This is exactly how accounting works!

### Transfer of Debt

Debt can be transferred like assets:

```
Transfer Debt:
─────────────────────────────────────────────────────────
(Alice says transfer_debt(Bob, C, q)) ⊗ [Alice] coin(C, q)⊥  ⊢  [Bob] coin(C, q)⊥
```

"Alice transfers her debt to Bob" (with Bob's implicit consent via authorization logic).

---

## Connection to Accounting

### The Fundamental Parallel

| Accounting | Linear Logic |
|------------|--------------|
| Asset | A |
| Liability | A⊥ |
| Debit balance | Positive formula |
| Credit balance | Negated formula |
| Settlement | A ⊗ A⊥ ⊢ 1 |

### Why This Works

In double-entry bookkeeping:
- Assets = Liabilities + Equity
- Every transaction has equal debits and credits (sums to zero)

In linear logic:
- A⊥⊥ = A (involution)
- ⊢ A, A⊥ (axiom)
- A ⊗ A⊥ can be "cut" away

The accounting equation is a **conservation law**. Linear logic's resource semantics enforces the same conservation!

### T-Accounts as Dual Pairs

Recall from algebraic-accounting.md:

```
T-account = [debit // credit] = [x // y]
```

In linear logic terms:
```
[x // y] ≈ x ⊗ y⊥
```

Or possibly:
```
[x // y] ≈ x ⅋ y⊥
```

The correct correspondence depends on whether we want multiplicative (parallel) or additive (choice) structure.

---

## Classical vs Intuitionistic Linear Logic

### Classical Linear Logic (CLL)

- Negation is primitive and involutive
- One-sided sequents: ⊢ Γ
- Full De Morgan duality
- A ⊸ B = A⊥ ⅋ B

CLL is **better for the debt interpretation** because:
- Involution (A⊥)⊥ = A makes sense for debt
- Symmetry between assets and liabilities
- Settlement A ⊗ A⊥ ⊢ 1 is directly expressible

### Intuitionistic Linear Logic (ILL)

- Negation defined: ¬A = A ⊸ 0
- Two-sided sequents: Γ ⊢ A
- Asymmetric (no full duality)
- More constructive

ILL is **less suitable for debt** because:
- (¬¬A) ≠ A in general
- Can't directly express "owing an obligation = having"

### CALC's Position

CALC currently implements ILL (with persistent_ctx + linear_ctx). To support the debt interpretation, we may need to:

1. **Add linear negation** as a primitive (extend to CLL fragment)
2. **Or** use a "debt" predicate: `debt(C, q)` instead of `coin(C, q)⊥`
3. **Or** model debt at the modality level: `[Alice]⁻¹ A` (inverse ownership?)

Option 1 (CLL fragment) is cleanest but requires calculus extension.

---

## Game-Semantic Perspective

### Proponent vs Opponent

In game semantics:
- **Proponent (P)**: The party asserting/proving
- **Opponent (O)**: The party challenging/refuting

Negation swaps roles:
- A: P has winning strategy
- A⊥: O has winning strategy (P becomes O)

### Debt as Role Reversal

```
coin(BTC, q)      = "I (Proponent) have 0.5 BTC"
coin(BTC, q)⊥     = "You (Opponent) have a claim on 0.5 BTC from me"
```

Equivalently: "I'm in the Opponent role regarding 0.5 BTC" = "I owe it."

### Orthogonality (from Ludics)

In Ludics, two designs D and E are orthogonal (D ⊥ E) if their interaction converges.

For debt settlement:
```
asset ⊥ debt  iff  they can "interact" (settle)
```

The axiom ⊢ A, A⊥ says: "A formula is always orthogonal to its dual."

---

## Open Questions

### 1. Which Modality/Negation Order?

```
[Alice] (A⊥)    vs    ([Alice] A)⊥
```

For CALC, we need to decide: Does ownership commute with negation?

**Proposal:** They don't commute. Use `[Alice] (A⊥)` for "Alice's debt."

### 2. Multi-Party Debt — RESEARCHED

What is `[Alice] coin(BTC, q)⊥` vs `[Bob] coin(BTC, q)⊥`?

- `[Alice] coin(BTC, q)⊥` = Alice owes someone q BTC
- `[Bob] coin(BTC, q)⊥` = Bob owes someone q BTC

But to **whom**? The creditor isn't specified!

**Session Type Insight** (from Caires-Pfenning):

> "Duality, the cornerstone of session types and linear logic, ensures that the two endpoints of a channel have matching actions."

In session types, a channel c has:
- Type A on one endpoint (owner)
- Type A⊥ on the other endpoint (dual owner)

The **channel itself** specifies the bilateral relationship!

**Options for CALC:**

| Option | Syntax | Semantics |
|--------|--------|-----------|
| A: Explicit predicate | `debt(Alice, Bob, BTC, q)` | Clear, simple |
| B: Directed ownership | `[Alice → Bob] coin(BTC, q)` | Edge from debtor to creditor |
| C: Channel endpoints | Alice: `c : A`, Bob: `c⊥ : A⊥` | Session types approach |
| D: Composite principal | `[Alice ⊸ Bob] coin(BTC, q)` | Implicational composite |

**Analysis:**

- **Option A** (explicit predicate): Simplest, most readable. No new logic needed.
- **Option B** (directed ownership): Graph-theoretic, matches accounting intuition (edges).
- **Option C** (channel endpoints): Most principled (Curry-Howard), but requires channels.
- **Option D** (composite principal): Novel, but `A ⊸ B` as principal is unclear.

**Recommendation for CALC**: Use **Option A** (explicit predicate) initially:

```
debt(debtor, creditor, commodity, quantity)
```

This avoids complexity while being explicit. Later, can explore channel-based approach if needed.

**Connection to authorization logic:**

```
(Alice says owes(Bob, BTC, q)) ⊗ [Alice] coin(BTC, q)⊥
```

This reads: "Alice acknowledges debt to Bob AND controls the obligation."

**Settlement with creditor:**

```
[Alice] coin(BTC, q) ⊗ debt(Alice, Bob, BTC, q) ⊸ [Bob] coin(BTC, q)
```

"Alice's BTC + Alice's debt to Bob → Bob receives BTC" (debt payment)

### 3. Partial Settlement

Can we partially settle?

```
coin(BTC, 1.0) ⊗ coin(BTC, 0.5)⊥  ⊢  coin(BTC, 0.5)
```

"Having 1 BTC and owing 0.5 BTC leaves 0.5 BTC"

This requires arithmetic integration (FFI to subtraction).

### 4. CLL Extension for CALC — ANALYSIS

To fully support debt semantics, CALC would need:
- Linear negation (·)⊥ as primitive
- Par connective (⅋) — dual of tensor
- Why-not (?) — dual of bang
- Modified proof search (CLL is more complex)

**Is this worth the complexity?**

**Arguments FOR CLL extension:**
1. **Clean debt semantics**: A⊥ as primitive gives involution (A⊥)⊥ = A
2. **De Morgan duality**: Full symmetry between connectives
3. **Session types**: Classical F° uses full CLL, enables richer protocols
4. **Expressiveness**: Can state "either Alice pays or Bob pays" (⅋ = "one will happen")

**Arguments AGAINST CLL extension:**
1. **Proof search harder**: CLL has non-determinism in cut-elimination
2. **Polarization required**: Need focusing (already have) but more complex
3. **ILL suffices for many use cases**: Assets, transfers, atomic swaps all work in ILL
4. **Explicit debt predicate works**: `debt(A, B, C, q)` avoids needing negation

**From the literature** (Comparing session type systems, 2024):

> "The main divide between these type systems is the classical and intuitionistic presentations of linear logic."

Classical gives full duality; intuitionistic is more constructive.

**Recommendation:**

**SHORT-TERM**: Stay with ILL, use explicit `debt(A, B, C, q)` predicate.
- Simpler proof search
- Already have working implementation
- Debt can be modeled without negation

**MEDIUM-TERM**: Add linear negation (·)⊥ as a new connective.
- Keep ILL base, add negation
- Don't require full CLL (no ⅋, ?)
- Use negation only for debt semantics

**LONG-TERM**: Consider full CLL if:
- Need rich bidirectional protocols
- Want session type features
- Require par for "entangled disjunction"

**Key insight**: CALC's decision should be driven by use cases, not theoretical elegance. If explicit debt predicates work for all needed scenarios, CLL complexity isn't justified.

---

## Summary

Linear negation (A⊥) naturally interprets as **obligation/debt**:

| Formula | Interpretation |
|---------|----------------|
| A | Having resource A |
| A⊥ | Owing resource A (debt) |
| (A⊥)⊥ | Owing a debt = having (involution) |
| A ⊗ A⊥ | Asset + liability (can settle to 1) |

**Key insights:**

1. **Involution makes sense**: A debt of a debt = an asset
2. **Settlement is built-in**: A ⊗ A⊥ ⊢ 1 (cut rule)
3. **Matches accounting**: Assets/liabilities, conservation, double-entry
4. **Game semantics**: Debt = role reversal (Proponent → Opponent)
5. **Session types**: Debt = dual endpoint

**For CALC:**

- Use `[Alice] coin(C, q)⊥` for "Alice owes q of currency C"
- Consider CLL extension for full debt support
- Connect to authorization logic for creditor specification

---

## References

### Linear Logic Foundations
- [Girard, "Linear Logic: Its Syntax and Semantics"](https://girard.perso.math.cnrs.fr/Synsem.pdf)
- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- [nLab: Linear Logic](https://ncatlab.org/nlab/show/linear+logic)
- [Pfenning, Lecture Notes on Classical Linear Logic](https://www.cs.cmu.edu/~fp/courses/15816-f16/lectures/27-classical.pdf)

### Game Semantics
- [Blass, "A game semantics for linear logic" (1992)](https://philpapers.org/rec/BLAAGS-2)
- [Abramsky & Jagadeesan, "Games and full Completeness for MLL"](https://www.researchgate.net/publication/227330874_Games_and_full_Completeness_for_multiplicative_Linear_Logic)
- [nLab: Game Semantics](https://ncatlab.org/nlab/show/game+semantics)

### Session Types
- [Caires & Pfenning, "Session Types as Intuitionistic Linear Propositions"](https://link.springer.com/chapter/10.1007/978-3-642-15375-4_16)
- [Wadler, "Propositions as Sessions"](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf)
- [Caires, Pfenning, Toninho, "Linear Logic Propositions as Session Types"](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)

### Related CALC Research
- [[sketch]] — Coin ownership modeling
- [[algebraic-accounting]] — Pacioli group, conservation
- [[plain-text-accounting]] — Liabilities as negative assets
- [[authorization-logic]] — Principals, `speaks for`

---

*Last updated: 2026-01-29*
