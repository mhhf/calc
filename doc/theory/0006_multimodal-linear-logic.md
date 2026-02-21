---
title: "Multimodal Linear Logic for CALC"
created: 2026-02-10
modified: 2026-02-10
summary: Design for combining ownership, location, and graded modalities in linear logic with interaction semantics, composition rules, and negation handling.
tags: [multimodal, ownership, graded-types, location, modalities]
category: "Multi-Type Framework"
unique_contribution: "Three orthogonal modality families (ownership, location, graded) combined in linear logic using parametric indices rather than SELL subexponentials."
---

# Multimodal Linear Logic for CALC

This document addresses the design of a multimodal linear logic system for CALC, supporting ownership, location, and graded modalities that can interact, combine, and be negated in a theoretically sound manner.

> **See also:** [[authorization-logic]] for principal-based says modality, [[graded-resource-tracking]] for QTT/Granule, [[multi-type-display-calculus]] for MTDC implementation, [[ownership-design]] for coin ownership, [[linear-negation-debt]] for debt semantics.

---

## Table of Contents

1. [Core Question](#1-the-core-question)
2. [Three Families of Modalities](#2-three-families-of-modalities)
3. [Modalities vs Parameters](#3-modalities-vs-parameters-expressiveness-comparison)
4. [How Modalities Interact](#4-how-modalities-interact)
5. [Combining Modalities](#5-combining-modalities)
6. [Negation of Modalities](#6-negation-of-modalities)
7. [Multi-Type Display Calculus Evaluation](#7-multi-type-display-calculus-evaluation)
8. [Implementation Design](#8-implementation-design)
9. [Proofs Required](#9-proofs-required-for-soundness-and-completeness)
10. [Comparison with Existing Systems](#10-comparison-with-existing-systems)
11. [Design Decisions Summary](#11-design-decisions-summary)
12. [Future Work: Debt and CLL](#12-future-work-debt-and-classical-linear-logic)

---

## 1. The Core Question

We want linear types that can be "wrapped" by modalities:

```
[Alice] btc(100)                      -- ownership modality
@Exchange btc(100)                    -- location modality
[]_{100} btc                          -- graded (quantity) modality
[Alice] @Exchange:Trading []_{100} btc  -- combined modalities
```

**Key requirements:**
- Modalities must work for ALL linear types, not just specific constructors
- Theoretically sound (cut-elimination, consistency)
- Modalities can be combined, interact, and negated
- Implementation via mmll.family, mmll.calc, mmll.rules

---

## 2. Three Families of Modalities

### 2.1 Ownership Modality: [Principal]

**Syntax:** `[Alice] A`, `[Bob] A`, `[Alice ∧ Bob] A`

**Meaning:** "Principal P controls/owns resource A"

**From authorization logic (Garg-Pfenning):**
- `P says φ` = P affirms/claims φ
- `[P] A` = P possesses resource A
- Composite: `[A ∧ B]` (both must consent), `[A ∨ B]` (either suffices)

**Structural properties:**
- Linear (no contraction, no weakening) — resources can't be duplicated
- Transfer requires explicit consent

### 2.2 Location Modality: @Location

**Syntax:** `@Exchange A`, `@Alice:Coinbase:Trading A`

**Meaning:** "Resource A is located at L"

**Inspired by:**
- **Ambient Logic** (Cardelli-Gordon): Spatial hierarchy of locations
- **Distributed Linear Logic**: Resources at network locations
- **Subexponentials**: Indexed by preordered locations

**Location structure:**
- Hierarchical: `Alice:Exchange:Coinbase:Trading`
- Preorder: `Trading ≤ Coinbase ≤ Exchange ≤ Alice`
- Resources can move: `@L₁ A ⊸ @L₂ A` (transfer between locations)

### 2.3 Graded Modality: []_r

**Syntax:** `[]_{100} btc`, `[]_{0.5} A`

**Meaning:** "r units of A" (quantity, usage bound, sensitivity)

**From Bounded Linear Logic and Granule:**
- Grade r from a semiring (ℕ, ℝ≥0, etc.)
- `[]_r A ⊗ []_s A ⊢ []_{r+s} A` (additive combination)
- `[]_r (A ⊗ B) ⊢ []_r A ⊗ []_r B` (distribution)

**Semiring operations:**
- Addition (+): combining quantities
- Multiplication (·): scaling/iteration
- Zero (0): empty
- One (1): unit

---

## 3. Modalities vs Parameters: Expressiveness Comparison

### 3.1 The Parameter Approach

```
btc : owner -> location -> amount -> ltype

btc(Alice, Exchange, 100)
btc(Bob, Wallet, 50)
```

**Advantages:**
- Simple to implement (just type constructors)
- No special proof rules needed
- Familiar programming pattern

**Disadvantages:**
- **Type-specific**: Must define parameters for each type separately
- **No abstraction**: Can't write `[Alice] A` for arbitrary A
- **No interaction rules**: No generic transfer, combination rules
- **Duplication**: Same logic repeated for every resource type

### 3.2 The Modality Approach

```
[Alice] @Exchange []_{100} btc

-- Works for ANY type:
[Alice] @Exchange []_{100} eth
[Alice] @Exchange option(btc, 1000, 2026-12)
```

**Advantages:**
- **Universal**: Works for all linear types
- **Composable**: Modalities compose orthogonally
- **Generic rules**: Transfer, split, combine work uniformly
- **Extensible**: Add new resource types without new modality rules

**Disadvantages:**
- More complex proof theory
- Requires careful design of interactions
- Cut-elimination proofs needed

### 3.3 Expressiveness Theorem (Informal)

**Claim:** Modalities strictly generalize parameters.

**Proof sketch:**
- Parameters can encode specific modalities: `btc(Alice, L, n) ≈ [Alice] @L []_n btc`
- But modalities support: `[Alice] A` for arbitrary A
- Parameters cannot abstract over types this way

**Recommendation:** Use modalities for ownership/location/quantity; use parameters for type-specific attributes (strike price, expiry date).

---

## 4. How Modalities Interact

### 4.1 Orthogonal Composition

The three modality families are **orthogonal** — they operate on different dimensions:

| Modality | Dimension | Structure |
|----------|-----------|-----------|
| [P] | WHO | Principal lattice |
| @L | WHERE | Location preorder |
| []_r | HOW MUCH | Semiring |

**Composition is multiplicative:**
```
[Alice] @Exchange []_{100} btc
```

This is NOT nested — it's three independent annotations:
- Ownership: Alice
- Location: Exchange
- Quantity: 100

### 4.2 Interaction Rules

**Transfer (ownership change):**
```
(Alice says transfer(Bob)) ⊗ [Alice] @L []_r A  ⊢  [Bob] @L []_r A
```

**Move (location change):**
```
(Alice says move(L₁, L₂)) ⊗ [Alice] @L₁ []_r A  ⊢  [Alice] @L₂ []_r A
```

**Split (quantity division):**
```
[P] @L []_{r+s} A  ⊢  [P] @L []_r A ⊗ [P] @L []_s A
```

**Combine (quantity addition):**
```
[P] @L []_r A ⊗ [P] @L []_s A  ⊢  [P] @L []_{r+s} A
```

### 4.3 Modality Ordering

For each dimension, there's a natural ordering:

**Ownership:** Delegation/speaks-for
```
Alice speaks for Bob  ⟺  ∀φ. (Alice says φ) → (Bob says φ)
```

**Location:** Hierarchical containment
```
Trading ≤ Coinbase ≤ Exchange ≤ Alice
```

**Grades:** Semiring ordering
```
r ≤ s  ⟺  ∃t. r + t = s
```

---

## 5. Combining Modalities

### 5.1 Composite Principals

**Conjunction (both must consent):**
```
[Alice ∧ Bob] A  ≡  requires both Alice's and Bob's consent to use A
```

**Rules:**
```
Introduction:    [Alice] A ⊗ [Bob] A ⊗ agree(Alice,Bob)  ⊢  [Alice ∧ Bob] A
Elimination:     [Alice ∧ Bob] A  ⊢  [Alice] A
                 [Alice ∧ Bob] A  ⊢  [Bob] A
```

**Disjunction (either suffices):**
```
[Alice ∨ Bob] A  ≡  either Alice or Bob can use A
```

**Threshold (k-of-n):**
```
[2-of-{Alice,Bob,Carol}] A  ≡  any 2 of the 3 can use A
```

**Note:** Threshold expands combinatorially. Use explicit predicate: `threshold(k, principals, A)`.

### 5.2 Location Combination

**Location tensor (parallel locations):**
```
@(L₁ ⊗ L₂) A  ≡  A exists at both L₁ and L₂ (replicated)
```

**Location sum (choice of location):**
```
@(L₁ ⊕ L₂) A  ≡  A exists at either L₁ or L₂
```

### 5.3 Grade Combination

Grades combine via semiring operations:

```
[]_r A ⊗ []_s A  ⊢  []_{r+s} A    (addition)
[]_r []_s A      ⊢  []_{r·s} A    (multiplication/nesting)
```

---

## 6. Negation of Modalities

### 6.1 Classical Duality

In classical modal logic, □ and ◇ are De Morgan duals:
```
◇A = ¬□¬A
□A = ¬◇¬A
```

### 6.2 Ownership Negation

**What is `[Alice]⊥` or `¬[Alice]`?**

**Option A: Dual principal (lax/possibility):**
```
⟨Alice⟩ A  =  "Someone can give Alice resource A"
           =  "There exists a path where Alice receives A"
```

**Duality:**
```
[Alice] A  =  □_Alice A  =  "Alice definitely has A"
⟨Alice⟩ A  =  ◇_Alice A  =  "Alice possibly has/will have A"
```

**Option B: Obligation/debt (linear negation):**
```
[Alice] A⊥  =  "Alice owes A"
```

This uses linear negation on the content, not the modality.

**Recommendation:** Keep both:
- `⟨P⟩` as possibility/lax modality (for futures, options)
- `[P] A⊥` for debt (Alice has obligation to provide A)

### 6.3 Location Negation

**What is `@L⊥` or `¬@L`?**

**Option A: Everywhere-but-L:**
```
@(¬L) A  =  "A is at every location except L"
```

This is awkward and rarely useful.

**Option B: No location negation:**

Treat locations as purely positive. Use explicit predicates for constraints:
```
forbidden(L, A)  =  "A cannot be at L"
```

**Recommendation:** No location negation. Use explicit constraints.

### 6.4 Grade Negation

**What is `[]_r⊥` or `¬[]_r`?**

In bounded linear logic, grades don't negate directly. Instead:
```
[]_r A ⊗ []_s A⊥  ⊢  []_{r-s} A    (if r ≥ s)
```

This is **settlement** — canceling positive and negative quantities.

**For debt semantics:**
```
[]_r A     =  "have r units of A"
[]_r A⊥    =  "owe r units of A"
[]_r A ⊗ []_r A⊥  ⊢  1   (settlement)
```

---

## 7. Multi-Type Display Calculus Evaluation

### 7.1 Current CALC Implementation

CALC implements Benton's LNL:
- Two types: Cartesian (persistent_ctx) and Linear (linear_ctx)
- Adjunction: F ⊣ G where ! = F∘G
- Cut-elimination proven for this specific logic

### 7.2 Is MTDC Right for Multimodalities?

**Multi-Type Display Calculus (MTDC) advantages:**
- Multiple formula types with different structural rules
- Generic cut-elimination via Belnap conditions
- Heterogeneous connectives crossing types
- Modular: add connectives without re-proving cut-elim

**MTDC for our multimodalities:**

| Type | Meaning | Structure |
|------|---------|-----------|
| Lin | Linear resources | No W, no C |
| Cart | Cartesian/persistent | W, C |
| Own_P | P-owned resources | Indexed by principal |
| Loc_L | L-located resources | Indexed by location |
| Grd_r | r-graded resources | Indexed by grade |

**Problem:** This creates a **product of indices**, not separate types:
- We'd need type `Own_Alice ⊗ Loc_Exchange ⊗ Grd_100`
- This is a 3D lattice of types!

### 7.3 Alternative: Subexponential Linear Logic (SELL)

**SELL/MMLL approach:**
- Single formula type (linear)
- Multiple indexed exponentials: `!_a`, `?_a`
- Each index has structural + modal properties
- Preorder on indices controls interactions

**MMLL (Multi-Modal Linear Logic) supports:**
- Unbounded (W, C) vs Linear (no W, no C) per index
- Modal axioms: K (all), 4 (transitivity), D (seriality), T (reflexivity)
- Cut-elimination proven generically

**This is closer to what we need:**
```
!_{Alice,Exchange,100} btc
```

Single index = tuple of (principal, location, grade).

### 7.4 Alternative: Adjoint Logic with Grading

**Adjoint logic + grades (Hanukaev, Eades et al. 2023):**
- Modes form a preorder with adjunctions
- Each mode can have grades
- Combines substructural and graded reasoning

```
Modes: L (linear), U (unrestricted), Own_P, Loc_L
Grades: quantity semiring

□^r_m A  =  "at mode m, have r units of A"
```

### 7.5 SELL's Critical Limitation: Fixed Index Sets

**The problem with standard SELL/MMLL:**

In SELL, the subexponential signature Σ = (I, ≤, U) is **fixed at logic-definition time**:
- **I**: A fixed, finite set of indices
- **≤**: A fixed preorder on I
- **U**: Which indices are unbounded (allow W, C)

This means you must declare every principal and location upfront:
```
indices: { alice, bob, carol, exchange, wallet, ... }
```

**This doesn't work for blockchain/CALC because:**
- **Principals are open-ended**: Any public key can be a principal (infinite set)
- **Locations are programmable**: Paths like `Alice:Exchange:Coinbase:Trading` are user-defined
- **New entities appear dynamically**: Can't enumerate all addresses at logic-definition time

### 7.6 MTDC's Advantage: Parametric Indices

MTDC with **parametric types** handles open-ended indices naturally:

```
-- Index SORTS (not fixed indices!)
type Principal : Set           -- ANY element of a set (public keys)
type Location : Preorder       -- ANY element of a preorder (paths)
type Grade : Semiring          -- ANY element of a semiring (quantities)

-- Parametric modalities (work for ANY index value)
[_] : Principal -> formula -> formula    -- [P] A for any P
@_  : Location -> formula -> formula     -- @L A for any L
[]_ : Grade -> formula -> formula        -- []_r A for any r
```

**The key insight:**
- SELL's indices are part of the **logic signature** (fixed, finite)
- MTDC's indices can be **terms in the logic** (open, infinite)

### 7.7 Comparison: Fixed vs Parametric Indices

| Aspect | SELL (standard) | MTDC with parametric indices |
|--------|-----------------|------------------------------|
| Index set | Fixed at definition time | Open/infinite (terms) |
| New principals | Requires redefining the logic | Just new terms |
| Location paths | Must be enumerated | Programmable (term language) |
| Proof rules | Per-index or schematic | Fully parametric |
| Quantification | Limited | `∀P. [P] A ⊸ ...` works |

### 7.8 Revised Recommendation

**Stay with MTDC. Use parametric/indexed modalities within MTDC framework.**

The hybrid approach:
1. **MTDC as the meta-framework** — for its expressiveness and modularity
2. **Parametric index sorts** — Principal, Location, Grade as term-level indices
3. **Quantified rules** — `∀P Q. (P says transfer(Q)) ⊗ [P] A ⊢ [Q] A`

This gives:
- MTDC's ability to experiment with different logics
- Open-ended indices (any public key, any location path)
- Quantification over principals/locations
- Natural evolution from current LNL implementation

**What we lose vs pure SELL:** Nothing significant — we get SELL-style indexed modalities but with the flexibility of term-level indices.

**What we gain vs pure SELL:** Open-ended index domains, programmable locations, blockchain compatibility.

---

## 8. Implementation Design

### 8.1 File Structure

```
calculi/
├── mmll.family           -- Family definition
├── mmll.calc             -- Connectives and rules
└── mmll.rules            -- Domain-specific rules
```

### 8.2 mmll.family

```
family mmll {
  -- Base structural type
  type formula : structural {
    weakening: false
    contraction: false
  }

  -- Index SORTS (open-ended, not fixed sets!)
  -- These are TERM types, not enumerated indices
  sort Principal : type             -- any public key, address, etc.
  sort Location : type              -- hierarchical paths (programmable)
  sort Grade : semiring             -- quantities from a semiring

  -- Principal operations (for composite principals)
  conj : Principal -> Principal -> Principal    -- P ∧ Q
  disj : Principal -> Principal -> Principal    -- P ∨ Q

  -- Location operations (for hierarchical paths)
  root : Location
  child : Location -> String -> Location        -- L:name

  -- Grade operations (semiring)
  zero : Grade
  one : Grade
  add : Grade -> Grade -> Grade
  mul : Grade -> Grade -> Grade

  -- Modalities are PARAMETRIC over index sorts
  -- NOT a fixed subexponential signature!
}
```

**Key difference from SELL:** The sorts `Principal`, `Location`, `Grade` are **term types**, not a fixed enumeration. Any public key is a valid Principal. Any path expression is a valid Location.
```

### 8.3 mmll.calc

```
calc mmll extends ill {
  -- Ownership modality
  [_] : Principal -> formula -> formula
    @latex "[#1] #2"
    @polarity positive

  -- Possibility (dual)
  <_> : Principal -> formula -> formula
    @latex "\\langle #1 \\rangle #2"
    @polarity negative

  -- Location modality
  @_ : Location -> formula -> formula
    @latex "@_{#1} #2"
    @polarity positive

  -- Graded modality
  []_ : Grade -> formula -> formula
    @latex "\\Box_{#1} #2"
    @polarity positive

  -- Composite principals
  ∧ : Principal -> Principal -> Principal
  ∨ : Principal -> Principal -> Principal

  -- Authorization judgment
  says : Principal -> formula -> formula
    @latex "#1 \\text{ says } #2"
}
```

### 8.4 mmll.rules

```
rules mmll {
  -- =====================================================
  -- PARAMETRIC RULES (quantified over index sorts)
  -- These work for ANY principal P, Q, ANY location L, L'
  -- =====================================================

  -- Ownership introduction (parametric over Principal)
  Own_R : {P : Principal}
    Γ ⊢ A
    -------------------
    Γ ⊢ [P] A  when (P controls Γ)

  Own_L : {P : Principal}
    Γ, A ⊢ C
    -------------------
    Γ, [P] A ⊢ C

  -- Transfer (parametric over two Principals)
  Transfer : {P Q : Principal}
    (P says transfer(Q)) ⊗ [P] A ⊢ [Q] A

  -- Location rules (parametric over Location)
  Loc_R : {L : Location}
    Γ ⊢ A
    -------------------
    Γ ⊢ @L A  when (Γ at L)

  Move : {P : Principal} {L L' : Location}
    (P says move(L, L')) ⊗ [P] @L A ⊢ [P] @L' A

  -- Graded rules (parametric over Grade)
  Grd_R : {r : Grade}
    Γ ⊢ A
    -------------------
    Γ ⊢ []_r A

  Split : {r s : Grade}
    []_{r + s} A ⊢ []_r A ⊗ []_s A

  Combine : {r s : Grade}
    []_r A ⊗ []_s A ⊢ []_{r + s} A

  -- Settlement (with negation)
  Settle : {r : Grade}
    []_r A ⊗ []_r A⊥ ⊢ 1

  -- Composite principal rules (using Principal operations)
  Conj_Intro : {P Q : Principal}
    [P] A ⊗ [Q] A ⊗ agree(P,Q) ⊢ [conj P Q] A

  Conj_Elim_L : {P Q : Principal}
    [conj P Q] A ⊢ [P] A

  Conj_Elim_R : {P Q : Principal}
    [conj P Q] A ⊢ [Q] A
}
```

**Note:** The `{P : Principal}` syntax indicates these are **schematic/parametric rules** — they work for any term of type Principal, not just enumerated constants. This is what enables open-ended indices.

### 8.5 Architecture Transition from LNL

**Current LNL implementation (lnl.family):**
```javascript
// lib/sequent.js
class Sequent {
  persistent_ctx = {}   // Cartesian type (one fixed context)
  linear_ctx = {}       // Linear type (one fixed context)
  succedent = {}
}

// Bang_L hardcoded in prover.js
if (ruleName === "Bang_L") {
  // Move !A from linear_ctx to A in persistent_ctx
}
```

**Proposed MTDC extension (mmll.family):**
```javascript
// Generalized sequent with parametric contexts
class Sequent {
  // Instead of two fixed contexts, we have:
  // - A linear base context (unchanged)
  // - Parametric modality annotations on formulas

  linear_ctx = {}       // Base linear resources
  succedent = {}

  // Modalities are now FORMULA WRAPPERS, not separate contexts:
  // [Alice] @Exchange []_{100} btc
  // is a single formula in linear_ctx with nested modality structure
}
```

**Why this is a natural evolution:**

| LNL (current) | MMLL (proposed) |
|---------------|-----------------|
| `persistent_ctx` = one Cartesian context | `[P]` modality = indexed ownership (many) |
| `Bang_L` moves to persistent | `Own_L` unwraps ownership modality |
| Fixed two-type structure | Parametric modalities on single type |
| Hardcoded in prover.js | Declarative in mmll.rules |

**The key insight:** Instead of having separate *contexts* for each principal (which would explode), we keep one linear context but allow formulas to be *wrapped* in parametric modalities.

```
-- Old (would require context per principal):
alice_ctx: { btc(100) }
bob_ctx: { eth(50) }

-- New (modalities as formula wrappers):
linear_ctx: { [Alice] []_{100} btc, [Bob] []_{50} eth }
```

---

## 9. Proofs Required for Soundness and Completeness

### 9.1 Cut Elimination

**What to prove:** For any derivation using Cut, there's a cut-free derivation.

**Standard approach (MMLL/SELL):**
1. Define the cut rule:
   ```
   Γ ⊢ A    Δ, A ⊢ C
   -------------------
   Γ, Δ ⊢ C
   ```

2. Prove cut-elimination by double induction on:
   - Cut formula complexity
   - Derivation height

3. For subexponentials, also show principal cuts reduce:
   ```
   !_a introduction vs !_a elimination → smaller cut
   ```

**MMLL already has this:** The meta-logic/MMLL Coq formalization proves cut-elimination for the full system.

### 9.2 Identity Admissibility

**What to prove:** `A ⊢ A` is derivable for all A.

Follows from cut-elimination by standard argument.

### 9.3 Soundness

**What to prove:** If `Γ ⊢ A` is derivable, then Γ ⊨ A in the intended semantics.

**For CALC's multimodal logic, the semantics would be:**
- Phase semantics (following Girard)
- Or Kripke frames with accessibility for each modality index
- Or categorical semantics (symmetric monoidal closed categories)

**Subexponential semantics (Rogozin 2023):** Each modality interpreted as S4-like operator with reflexive-transitive relation.

### 9.4 Completeness

**What to prove:** If Γ ⊨ A then Γ ⊢ A.

For SELL/MMLL, completeness follows from:
1. Canonical model construction
2. Truth lemma
3. Canonical extensions (for distributive settings)

### 9.5 Specific Properties to Verify

| Property | What to prove |
|----------|---------------|
| **Transfer correctness** | `[P] A ⊸ [Q] A` only with `P says transfer(Q)` |
| **Location consistency** | `@L A` and `@L' A` disjoint when L ≠ L' |
| **Grade arithmetic** | Split/Combine preserve total quantity |
| **Composite principal** | `[P ∧ Q]` requires both consents |
| **Settlement** | `[]_r A ⊗ []_r A⊥ ⊢ 1` (debt cancellation) |

---

## 10. Comparison with Existing Systems

### 10.1 MMLL (meta-logic/MMLL)

**What it provides:**
- Focused first-order linear logic with subexponentials
- Each subexponential: unbounded or linear
- Modal axioms: K (all), 4, D, T
- Cut-elimination proven in Coq

**Gap for CALC:** No explicit principal/ownership semantics. We'd encode principals as indices.

### 10.2 Granule

**What it provides:**
- Graded modal types with semiring indices
- Linear types
- User-defined GADTs
- Multiple graded modalities simultaneously

**Gap for CALC:** No ownership or location modalities. Focused on resource usage, not authorization.

### 10.3 Nomos

**What it provides:**
- Session types with resource tracking
- Shared/linear modes (adjoint)
- Functional programming integration

**Gap for CALC:** Single shared/linear dimension, not full ownership lattice.

### 10.4 Authorization Logic (Garg-Pfenning)

**What it provides:**
- Principal-indexed "says" modality
- Composite principals (∧, ∨)
- Speaks-for delegation
- Linear variants exist

**Gap for CALC:** No location or graded modalities.

---

## 11. Design Decisions Summary

| Question | Recommendation |
|----------|----------------|
| Modalities vs parameters? | Modalities for ownership/location/quantity; parameters for type-specific attributes |
| How many modality families? | Three: [P] ownership, @L location, []_r grade |
| How do they combine? | Orthogonally (multiplicatively) |
| How do they negate? | [P] has dual ⟨P⟩; grades negate via A⊥; locations don't negate |
| MTDC or SELL? | **MTDC with parametric indices** (not pure SELL — need open-ended index domains) |
| Why not pure SELL? | SELL requires fixed index sets; we need dynamic principals (any public key) and programmable locations |
| Implementation? | mmll.family + mmll.calc + mmll.rules |
| Proofs needed? | Cut-elimination, soundness, completeness |

---

## 12. Future Work: Debt and Classical Linear Logic

### 12.1 Extending to CLL

For full debt semantics, need:
- Linear negation A⊥ (involutive)
- Par (⅋) — dual of tensor
- Why-not (?) — dual of bang

**Settlement rule:**
```
[]_r A ⊗ []_r A⊥ ⊢ 1
```

### 12.2 Debt as Modality

Alternatively, explicit debt modality:
```
debt(P, Q, r, A)  =  "P owes Q exactly r units of A"
```

With settlement:
```
[P] []_r A ⊗ debt(P, Q, r, A) ⊢ [Q] []_r A
```

---

## 13. References

### Subexponentials and MMLL
- [MMLL Coq Formalization](https://github.com/meta-logic/MMLL)
- [Rogozin, "Semantic Analysis of Subexponential Modalities" (2023)](https://arxiv.org/abs/2308.04521v1)
- [Nigam et al., "On Subexponentials, Focusing and Modalities"](http://nigam.info/docs/tcs-sellU.pdf)

### Graded Modal Types
- [Orchard et al., "Quantitative Program Reasoning with Graded Modal Types" (ICFP 2019)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- [The Granule Project](https://granule-project.github.io/granule.html)
- [Hanukaev et al., "Combining Dependency, Grades, and Adjoint Logic" (2023)](https://dl.acm.org/doi/10.1145/3609027.3609408)

### Adjoint Logic
- [Licata & Shulman, "Adjoint Logic with a 2-Category of Modes"](https://dlicata.wescreates.wesleyan.edu/pubs/ls15adjoint/ls15adjoint.pdf)
- [Pfenning, "Lecture Notes on Adjoint SAX"](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/15-adjsax.pdf)

### Multi-Type Display Calculus
- [Greco et al., "Multi-type Display Calculus for PDL"](https://arxiv.org/abs/1805.09144)
- [Frittella et al., "Multi-type Display Calculus for DEL"](https://hal.science/hal-01509398/document)

### Authorization Logic
- [Garg et al., "A Linear Logic of Authorization and Knowledge"](https://link.springer.com/chapter/10.1007/11863908_19)
- [Garg, "Principal-Centric Reasoning in Constructive Authorization Logic"](https://apps.dtic.mil/sti/pdfs/ADA506999.pdf)

### Ambient Logic
- [Cardelli & Gordon, "Anytime, Anywhere: Modal Logics for Mobile Ambients"](http://lucacardelli.name/papers/anytimeanywhere.us.pdf)

### Related CALC Research
- [[authorization-logic]] — Says, speaks for, controls
- [[algebraic-accounting]] — Pacioli group, T-accounts
- [[ownership-as-session-types]] — Mode-based ownership
- [[consensus-modalities-mpst]] — Composite principals
- [[linear-negation-debt]] — Debt as linear negation
- [[adjoint-logic-unifying-framework]] — Adjoint logic evaluation

---

*Last updated: 2026-02-07*
