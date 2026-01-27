# Quantitative Type Theory (QTT)

Comprehensive research document on QTT and its relationship to graded types, display calculus, and our project goals.

See also: [[display-calculus]] | [[RESEARCH]] | [[ANKI]]

---

## Table of Contents

1. [What is QTT?](#what-is-qtt)
2. [The Semiring Structure](#the-semiring-structure)
3. [Typing Rules](#typing-rules)
4. [QTT vs Granule (Graded Modal Types)](#qtt-vs-granule-graded-modal-types)
5. [QTT vs Multi-Type Display Calculus](#qtt-vs-multi-type-display-calculus)
6. [Implementations](#implementations)
7. [Relevance to Our Goals](#relevance-to-our-goals)
8. [Open Questions](#open-questions)
9. [Sources](#sources)

---

## What is QTT?

**Quantitative Type Theory** is a dependent type theory that tracks *how many times* each variable is used. It was developed by Conor McBride (2016) and formalized by Bob Atkey (2018).

### The Core Insight

Standard type systems distinguish:
- **Unrestricted variables**: can be used any number of times
- **Linear variables**: must be used exactly once

QTT generalizes this to **semiring-annotated variables**:
```
Γ, x :_ρ A ⊢ t : B
```
Where `ρ` is an element of a semiring indicating "how many times x is used in t".

### Why It Matters

1. **Combines linear + dependent types**: Previously very difficult
2. **Erasure**: `0` multiplicity means "compile-time only, erased at runtime"
3. **Resource tracking**: Generalizes to any semiring (counts, security levels, etc.)
4. **Practical**: Implemented in Idris 2

### Historical Context

| Year | Development |
|------|-------------|
| 2016 | McBride's "I Got Plenty o' Nuttin'" - original QTT idea |
| 2018 | Atkey's LICS paper - fixed substitution, gave categorical semantics |
| 2019 | Granule team's graded modal approach (ICFP) |
| 2021 | Idris 2 released with full QTT (Brady, ECOOP) |

---

## The Semiring Structure

### Definition

A **semiring** is a tuple `(S, +, ·, 0, 1)` where:
- `(S, +, 0)` is a commutative monoid (addition)
- `(S, ·, 1)` is a monoid (multiplication)
- `·` distributes over `+`
- `0 · a = 0 = a · 0` (zero annihilates)

### Why Semirings?

- **Addition** (`+`): Sums up multiple uses of a variable
- **Multiplication** (`·`): Accounts for nested/scaled usage
- **Zero** (`0`): No usage (erased)
- **One** (`1`): Single usage (linear)

### Common Semirings

 | Semiring        | Elements               | Use Case                 |
 | ----------      | ----------             | ----------               |
 | Zero-One-Many   | `{0, 1, ω}`            | Idris 2, basic linearity |
 | Natural Numbers | `(ℕ, +, ×, 0, 1)`      | Exact usage counting     |
 | Booleans        | `({0, 1}, ∨, ∧, 0, 1)` | Used/unused              |
 | Five-Point      | `{0, 1-, 1, 1+, ω}`    | Affine, linear, relevant |
 | Security Levels | `{public, secret}`     | Information flow         |
 | Real Numbers    | `(ℝ≥0, +, ×, 0, 1)`    | **Accounting!**          |

### Zero-One-Many Semiring (Idris 2)

```
+ | 0  1  ω        · | 0  1  ω
--+--------        --+--------
0 | 0  1  ω        0 | 0  0  0
1 | 1  ω  ω        1 | 0  1  ω
ω | ω  ω  ω        ω | 0  ω  ω
```

- `0`: Erased at runtime (type-level only)
- `1`: Used exactly once (linear)
- `ω`: Used any number of times (unrestricted)

---

## Typing Rules

### Context Operations

QTT requires operations on typing contexts:

1. **Scalar multiplication**: `ρ · Γ` - scale all multiplicities by ρ
2. **Pointwise addition**: `Γ₁ + Γ₂` - add multiplicities position-wise
3. **Zero context**: `0Γ` - all multiplicities are 0

### Key Rules (Simplified)

**Variable rule:**
```
─────────────────────────────
0Γ, x :_1 A ⊢ x : A
```
The variable x has multiplicity 1; all other variables have multiplicity 0.

**Application rule:**
```
Γ₁ ⊢ f : (x :_ρ A) → B    Γ₂ ⊢ a : A
────────────────────────────────────────
Γ₁ + ρ · Γ₂ ⊢ f a : B[a/x]
```
The argument's context is scaled by the function's multiplicity annotation.

**Lambda rule:**
```
Γ, x :_ρ A ⊢ t : B
─────────────────────────
Γ ⊢ λx.t : (x :_ρ A) → B
```

### The Substitution Problem

McBride's original system failed to admit substitution. Atkey fixed this by:
1. Separating "type formation" (always at 0 usage) from "term formation"
2. Careful treatment of how multiplicities flow through substitution

---

## QTT vs Granule (Graded Modal Types)

### Different Approaches to the Same Problem

Both QTT and Granule track "how much" variables are used, but differently:

| Aspect | QTT | Granule |
|--------|-----|---------|
| **Where grades live** | On binders (context) | On types (modalities) |
| **Notation** | `x :_ρ A` | `□_r A` |
| **Core idea** | Annotated variables | Graded comonads |
| **Dependent types** | Yes | Limited |
| **Polymorphism** | Limited | Grade polymorphism |

### QTT Style

```
Γ, x :_3 Int ⊢ x + x + x : Int
```
"x is used 3 times in this term"

### Granule Style

```
Γ ⊢ λx. x + x + x : □_3 Int → Int
```
"This function demands its argument 3 times"

### Graded Modal Dependent Type Theory (Grtt)

The Granule team developed **Grtt** which combines both approaches:
- Graded modalities (Granule-style)
- Dependent types (QTT-style)

This is the state of the art for combining all features.

### Which to Use?

| Goal | Recommended |
|------|-------------|
| Dependent types + linearity | QTT (Idris 2) |
| Grade polymorphism | Granule |
| Maximum expressivity | Grtt |
| Proof search | Neither directly (need sequent calculus) |

---

## QTT vs Multi-Type Display Calculus

### They Operate at Different Levels!

This is a crucial insight:

| Aspect | Multi-Type Display Calculus | QTT |
|--------|----------------------------|-----|
| **What it is** | Proof formalism | Type theory |
| **Purpose** | Construct proofs in logics | Type programs |
| **Focus** | Cut elimination, modularity | Resource tracking, erasure |
| **Output** | Proof trees | Typed terms |
| **Curry-Howard** | Logic side | Type side |

### Not Directly Comparable

Asking "is MTDC > QTT?" is like asking "is sequent calculus > Haskell?" - they're different tools:

- **MTDC**: How to present proof rules for multi-sorted logics
- **QTT**: How to type programs with resource tracking

### The Connection

They CAN be related via Curry-Howard:

```
Display Calculus for Linear Logic
            ↓ (Curry-Howard)
Linear Type Theory
            ↓ (add semiring grading)
QTT-like System
```

### For Multi-Type + Quantitative

To get both multi-type AND quantitative:

1. **Start with MTDC for linear logic** with graded modalities
2. **Types become sorts** in the display calculus
3. **Semiring grades** become modality indices
4. **Extract typing rules** via Curry-Howard

This is essentially what Granule does, but without the display calculus formalism.

### Key Insight

**MTDC gives you modular proof systems** (for designing logics)
**QTT gives you practical type systems** (for programming)

For our goals (proof search + accounting), we need BOTH:
- MTDC-style proof formalism for the logic
- QTT-style multiplicities for quantities

---

## Implementations

### Idris 2

The primary implementation of QTT.

```idris
-- Linear function: uses argument exactly once
dup : (1 x : a) -> (a, a)  -- ERROR: can't use x twice!

-- Unrestricted function: can use argument freely
dup : (x : a) -> (a, a)
dup x = (x, x)  -- OK

-- Erased argument: only for types, not runtime
id : (0 a : Type) -> a -> a
id _ x = x  -- 'a' is erased
```

**Semiring**: `{0, 1, ω}` (zero-one-many)

### Granule

Graded modal types with Z3 integration.

```granule
-- Graded modality: □_2 means "used twice"
dup : □_2 Int -> (Int, Int)
dup [x] = (x, x)

-- Grade polymorphism
id : ∀ {r : Nat} . □_r a -> □_r a
id [x] = [x]
```

**Semirings**: Multiple built-in (Nat, security levels, effects)

### Gerty

Research implementation of Graded Modal Dependent Type Theory.

https://github.com/granule-project/gerty

---

## Relevance to Our Goals

### Goal: Accounting with Linear Logic

We want:
1. **Quantities** that can be real numbers (0.5 BTC)
2. **Ownership** modalities ([Alice], [Bob])
3. **Proof search** to verify transactions

### How QTT Helps

| Feature | QTT Contribution |
|---------|------------------|
| Real-number quantities | Semiring over ℝ≥0 |
| Exact resource tracking | Multiplicities on variables |
| Erasure | 0-quantities for compile-time proofs |

### How MTDC Helps

| Feature | MTDC Contribution |
|---------|-------------------|
| Multi-type (owners, quantities) | Separate sorts |
| Modular rule design | Belnap's conditions |
| Proof search | Display property |

### Combined Approach

```
Multi-Type Display Calculus
+ Semiring-graded modalities (Granule-style)
+ Ownership sorts (Alice, Bob, ...)
= Foundation for accounting proofs
```

### Concrete Example

```
Types:
  - atprop: atomic propositions (USD, BTC)
  - owner: Alice, Bob, ...
  - quantity: ℝ≥0

Connective:
  owns : owner → quantity → atprop → formula
  -- "Alice owns 50.0 of USD" = owns Alice 50.0 USD

Sequent:
  owns Alice 100.0 USD ⊢ owns Alice 50.0 USD ⊗ owns Alice 50.0 USD
```

---

## Open Questions

### For Our Project

1. **Semiring for accounting**: What's the right semiring for real-number quantities?
   - `(ℝ≥0, +, ×, 0, 1)` works but what about negative quantities?
   - Do we need a *rig* (semiring without negation) or full ring?

2. **Proof search with quantities**: How does focusing work with graded modalities?
   - Granule doesn't do proof search
   - Need to adapt focused sequent calculus

3. **Integration with display calculus**: Can we design a display calculus that:
   - Has MTDC's multi-type expressivity
   - Has QTT's semiring-graded quantities
   - Supports efficient proof search

### Research Frontier

1. **Graded proof nets**: No known proof nets for graded/quantitative linear logic
2. **Quantity polymorphism in QTT**: Idris 2 doesn't support this yet
3. **Dependent + graded + multi-type**: Grtt is closest but still research-level

---

## Sources

### Primary Papers

- [Atkey: Syntax and Semantics of QTT (LICS 2018)](https://bentnib.org/quantitative-type-theory.html)
- [Brady: Idris 2: QTT in Practice (ECOOP 2021)](https://arxiv.org/abs/2104.00480)
- [McBride: I Got Plenty o' Nuttin' (2016)](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)
- [Choudhury et al.: Counting on QTT (2020)](https://richarde.dev/papers/2020/quantitative/quantitative.pdf)

### Granule and Graded Types

- [Orchard et al.: Quantitative Program Reasoning with Graded Modal Types (ICFP 2019)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- [Graded Modal Dependent Type Theory (ResearchGate)](https://www.researchgate.net/publication/344894610_Graded_Modal_Dependent_Type_Theory)
- [Granule Project](https://granule-project.github.io/)
- [Gerty Implementation](https://github.com/granule-project/gerty)

### Idris 2

- [Idris 2 Multiplicities Documentation](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html)
- [Linearity and Erasure in Idris 2](https://www.type-driven.org.uk/edwinb/linearity-and-erasure-in-idris-2.html)

### Related

- [Oleg's Blog: Dependent Linear types in QTT](https://oleg.fi/gists/posts/2020-12-18-dependent-linear.html)
- [QTT TypeScript Implementation](https://github.com/atennapel/qtt-ts)
- [Additive Pairs in QTT (Thesis)](https://dspace.cuni.cz/bitstream/handle/20.500.11956/127263/120390854.pdf)

---

## Summary: MTDC vs QTT

### The Bottom Line

**They're complementary, not competing:**

| For...                | Use...                                    |
| --------              | --------                                  |
| Designing proof rules | Multi-Type Display Calculus               |
| Typing programs       | QTT                                       |
| Proof search          | Sequent calculus (possibly display-style) |
| Quantitative tracking | Semiring grades (either approach)         |
| Multi-sort logic      | MTDC or labelled sequents                 |

### For Our Accounting Goal

The ideal system combines:
1. **MTDC's** multi-type expressivity (owners, quantities, propositions)
2. **QTT/Granule's** semiring-graded quantities
3. **Focused sequent calculus** for proof search

This is a **research contribution** - no existing system has all three.

### Can You Implement Granule in QTT?

**Partially.** QTT and Granule solve the same problem differently:
- QTT: grades on binders
- Granule: grades on modalities

Idris 2 (QTT) can express many Granule patterns, but lacks:
- Grade polymorphism
- Multiple semirings at once
- The full graded comonad structure

For our purposes, **Granule's approach** (graded modalities in linear logic) is more directly applicable because:
1. It has a sequent calculus presentation
2. It generalizes naturally to real numbers
3. It connects cleanly to proof theory

## Cross-References

See also in this knowledge base:
- [[exponential-display-problem]] — Why ! needs special treatment
- [[residuation]] — Galois connections and residuation
- [[logics-overview]] — Which logics can be displayed
- [[ANKI]] — Flashcards on graded modal types

---

*Last updated: 2026-01-27*
