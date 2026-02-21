---
title: "Adjunctions and Adjoint Logic"
created: 2026-02-10
modified: 2026-02-10
summary: Categorical adjunctions and Pfenning's adjoint logic framework unifying LNL, modal logics, and session types through mode preorders and adjoint modalities.
tags: [adjunction, adjoint-logic, category-theory, lnl, multimodal]
category: "Multi-Type Framework"
---

# Adjunctions and Adjoint Logic

Comprehensive research on categorical adjunctions, Pfenning's adjoint logic, and their application to CALC's multimodal framework.

---

## Table of Contents

1. [Categorical Adjunctions](#categorical-adjunctions)
2. [Key Examples of Adjunctions](#key-examples-of-adjunctions)
3. [Properties of Adjoint Functors](#properties-of-adjoint-functors)
4. [Adjunctions, Monads, and Comonads](#adjunctions-monads-and-comonads)
5. [Proof-Theoretic View](#proof-theoretic-view)
6. [Adjoint Logic](#adjoint-logic)
7. [What Adjoint Logic Unifies](#what-adjoint-logic-unifies)
8. [The Fibrational Framework](#the-fibrational-framework)
9. [Graded Adjoint Logic](#graded-adjoint-logic)
10. [Relevance to CALC](#relevance-to-calc)
11. [Assessment and Synthesis](#assessment-and-synthesis)
12. [References](#references)

---

## Categorical Adjunctions

### Definition via Hom-Set Isomorphism

An **adjunction** between categories C and D is a pair of functors:
- F : C → D (left adjoint)
- G : D → C (right adjoint)

together with a **natural bijection**:

```
Hom_D(F(X), Y) ≅ Hom_C(X, G(Y))
```

for all objects X in C and Y in D.

**Notation**: We write F ⊣ G to indicate F is left adjoint to G.

**Intuition**: "Morphisms out of F(X)" correspond to "morphisms into G(Y)." The left adjoint is "free," the right adjoint is "forgetful."

### Definition via Unit and Counit

Equivalently, an adjunction F ⊣ G consists of:
- **Unit**: η : Id_C → G ∘ F (natural transformation)
- **Counit**: ε : F ∘ G → Id_D (natural transformation)

satisfying the **triangle identities** (zig-zag equations):

```
(ε_F) ∘ (F η) = Id_F     -- "straighten left zig-zag"
(G ε) ∘ (η_G) = Id_G     -- "straighten right zig-zag"
```

**In string diagrams**: These say we can "pull the string straight" through a bend.

### Reconstructing the Bijection

Given unit η and counit ε, the bijection is:

```
φ : Hom_D(F(X), Y) → Hom_C(X, G(Y))
    φ(f) = G(f) ∘ η_X

ψ : Hom_C(X, G(Y)) → Hom_D(F(X), Y)
    ψ(g) = ε_Y ∘ F(g)
```

The triangle identities ensure φ and ψ are inverses.

---

## Key Examples of Adjunctions

### 1. Free ⊣ Forgetful

The paradigmatic example:

```
Free : Set → Mon     (free monoid on a set)
U : Mon → Set        (underlying set of a monoid)

Free ⊣ U
```

**Unit**: η_X : X → U(Free(X)) embeds a set into its free monoid.
**Counit**: ε_M : Free(U(M)) → M evaluates words in a monoid.

**The bijection**: "To define a homomorphism from a free monoid, just say where generators go."

### 2. Product ⊣ Diagonal ⊣ Coproduct

```
+ ⊣ Δ ⊣ ×

Coproduct (Sum)  ⊣  Diagonal  ⊣  Product
```

**Product adjunction**: `Hom(Z, X × Y) ≅ Hom(Z, X) × Hom(Z, Y)`
**Coproduct adjunction**: `Hom(X + Y, Z) ≅ Hom(X, Z) × Hom(Y, Z)`

### 3. Curry ⊣ Eval (Exponential Adjunction)

In a cartesian closed category:

```
(−) × A  ⊣  (−)^A

Product with A  ⊣  Exponential (function space)
```

**The bijection** (currying): `Hom(X × A, B) ≅ Hom(X, B^A)`

**In types**: `(X × A) → B ≅ X → (A → B)`

### 4. Limits and Colimits as Adjoints

```
colim_J  ⊣  Δ  ⊣  lim_J
```

**Limit**: Right adjoint to diagonal — "universal cone."
**Colimit**: Left adjoint to diagonal — "universal cocone."

---

## Properties of Adjoint Functors

### RAPL: Right Adjoints Preserve Limits

If G is a right adjoint (G = R in L ⊣ R), then G preserves all limits:
```
G(lim D) ≅ lim (G ∘ D)
```

**Dually**: Left adjoints preserve colimits (LAPC).

### Adjoint Functor Theorem

**Converse question**: If G preserves limits, is G a right adjoint?

**General AFT**: A functor G : D → C has a left adjoint if:
1. G preserves all small limits
2. G satisfies the **solution set condition**

### Uniqueness

Adjoints are unique up to unique isomorphism. If F ⊣ G and F ⊣ G', then G ≅ G'.

---

## Adjunctions, Monads, and Comonads

### Every Adjunction Induces a Monad and Comonad

Given F ⊣ G with unit η and counit ε:

**Monad** T = G ∘ F on C:
- Unit: η : Id → T
- Multiplication: μ = G ε F : T² → T

**Comonad** D = F ∘ G on D:
- Counit: ε : D → Id
- Comultiplication: δ = F η G : D → D²

### Kleisli and Eilenberg-Moore Categories

**Question**: Does every monad arise from an adjunction?

**Answer**: Yes, in two canonical ways!

**Kleisli category** C_T: The "free T-algebra" adjunction
**Eilenberg-Moore category** C^T: The "all T-algebras" adjunction

### The ! Modality as a Comonad

In linear logic, ! (of-course/bang) is a **comonad**:

```
ε : !A → A          (dereliction)
δ : !A → !!A        (digging)
```

**Two approaches to modeling !**:
1. **As a comonad** on a symmetric monoidal category
2. **As an adjunction** between cartesian and linear categories (Benton's LNL)

---

## Proof-Theoretic View

> **See also:** [[residuation]] for detailed treatment of Galois connections and residuated lattices.

### Adjunctions vs Galois Connections vs Residuation

| Concept | Setting | Notation |
|---------|---------|----------|
| Adjunction | Categories | F ⊣ G |
| Galois connection | Posets | f ⊣ g |
| Residuation | Residuated lattices | · ⊣ / ⊣ \ |
| Deduction theorem | Logic | ⊗ ⊣ → |

**Key insight**: These are all the same mathematical structure at different levels!

### Adjunctions in Sequent Calculus

In sequent calculus, adjunctions manifest as **bidirectional rules**:

```
Tensor-Implication Residuation:
─────────────────────────────
Γ, A ⊗ B ⊢ C    ⟺    Γ, A ⊢ B ⊸ C
```

### Display Postulates

> **See also:** [[display-calculus]] for Belnap's display calculus and C1-C8 conditions.

In **display calculus**, adjunctions appear as display postulates:

```
X ; Y ⊢ Z    ⟺    X ⊢ Y > Z
```

**Belnap's insight**: Display postulates encode residuation, enabling cut elimination.

### The LNL Decomposition

> **See also:** [[exponential-display-problem]] for why ! needs decomposition.

**Benton's LNL** decomposes ! via an adjunction:

```
Categories:  C (Cartesian)  ⟷  M (Linear/Monoidal)

Functors:    F : C → M      (embed cartesian into linear)
             G : M → C      (extract cartesian from linear)

Adjunction:  F ⊣ G

Comonad:     ! = F ∘ G
```

**In CALC**:
- persistent_ctx = the cartesian category C
- linear_ctx = the linear category M
- Bang_L = the F functor

---

## Adjoint Logic

### Historical Development

| Year | Contribution | Authors |
|------|--------------|---------|
| 1994 | LNL (Linear/Non-Linear) logic | Benton |
| 1996 | Adjoint λ-calculus | Benton, Wadler |
| 2009 | Judgmental deconstruction with mode preorder | Reed |
| 2016 | Adjoint logic with 2-category of modes | Licata, Shulman |
| 2017 | Fibrational framework | Licata, Shulman, Riley |
| 2018 | Adjoint logic (comprehensive treatment) | Pruiksma, Chargin, Pfenning, Reed |
| 2020 | Graded adjoint logic | Eades, Orchard |

### Core Idea

Instead of having ad-hoc modal operators, adjoint logic:
1. Parametrizes the logic by a **preorder (or 2-category) of modes**
2. Each mode can have different **structural properties** (weakening, contraction)
3. **Adjoint modalities** F and U (or ↑ and ↓) bridge between modes
4. Cut elimination follows **generically** from the framework

### Modes and Structural Properties

Each mode m has a set σ(m) ⊆ {W, C}:

| Property | Meaning | σ(m) contains |
|----------|---------|---------------|
| **Weakening (W)** | Antecedent need not be used | W ∈ σ(m) |
| **Contraction (C)** | Antecedent can be used multiple times | C ∈ σ(m) |

**Standard modes:**
- **Linear**: σ(L) = {} — use exactly once
- **Affine**: σ(A) = {W} — use at most once
- **Relevant**: σ(R) = {C} — use at least once
- **Cartesian/Intuitionistic**: σ(U) = {W, C} — use any number of times

**Monotonicity requirement**: If m ≥ k, then σ(m) ⊇ σ(k).

### The Adjoint Modalities

For modes m ≥ k, two modalities bridge between them:

```
↑ᵏₘ Aₖ   (upshift)   -- "lift" A from mode k to mode m
↓ᵐₖ Aₘ   (downshift) -- "project" A from mode m to mode k
```

These form an **adjunction**: F = ↓ᵐₖ ⊣ U = ↑ᵏₘ

From the adjunction:
- **Comonad**: ↓ᵐₖ ↑ᵏₘ A (like □ or !)
- **Monad**: ↑ᵏₘ ↓ᵐₖ A (like ○ or the lax modality)

---

## What Adjoint Logic Unifies

### 1. LNL Decomposition of !

Two modes: `{U, L}` with U > L.

```
F = ↓ᵁₗ : U → L    (Lin: embed intuitionistic into linear)
G = ↑ₗᵁ : L → U    (Mny: extract reusable part)

! A = F(G(A)) = ↓ᵁₗ ↑ₗᵁ A
```

**This is exactly CALC's current implementation!**

### 2. Intuitionistic S4

Two modes: `{V, U}` with V > U.
```
□ A = ↓ᵁᵥ ↑ᵁᵥ Aᵤ   (necessity = comonad)
```

### 3. Lax Logic

Two modes: `{U, X}` with U > X.
```
○ A = ↑ˣᵤ ↓ˣᵤ Aᵤ   (possibility = monad)
```

### 4. Session Types (Nomos)

> **See also:** [[nomos]] for comprehensive Nomos coverage.

Nomos uses adjoint modes for shared/linear channel discipline:

```
Modes = {shared, linear}  with shared > linear

/\ A = ↑ˢₗ A   (acquire: shared → linear)
\/ A = ↓ˢₗ A   (release: linear → shared)
```

### 5. Bunched Implications

```
Modes = {cartesian, linear}
Both tensor products (×, ⊗) and both implications (→, ⊸)
Adjoint modalities bridge between them
```

---

## The Fibrational Framework

### General Structure (Licata-Shulman-Riley 2017)

The framework abstracts common features:

1. **Context descriptors** are terms from a mode theory
2. **Types** are formed from context descriptors
3. **Two general connectives** (positive and negative) manipulate descriptors
4. **Cut/identity admissibility** proven once for the framework

### What It Covers

> "The resulting framework covers many existing connectives: non-associative, ordered, linear, affine, relevant, and cartesian products and implications; bunched logic; n-linear variables; the comonadic □ and linear exponential ! and subexponentials; monadic ♦ and ○; and adjoint logic F and G."

### Key Theorem

**Cut and identity are admissible** for the framework itself, which implies cut admissibility for any logic describable in the framework.

---

## Graded Adjoint Logic

> **See also:** [[graded-resource-tracking]] for graded modal types in general.

### Combining Grades and Modes (Eades & Orchard 2020)

```
□ᵣ A    (graded necessity, where r is from a semiring)
```

This enables tracking:
- **Exact usage counts**: r ∈ ℕ
- **Sensitivity bounds**: r ∈ ℝ≥0
- **Security levels**: r ∈ {public, secret}
- **Resource quantities**: r ∈ Currencies × Quantities

### Relevance to CALC

For coin quantities, we want:
```
[Alice] coin(BTC, r)   where r : ℝ≥0
```

Graded adjoint logic provides a framework where:
- **Mode** = principal (Alice, Bob, ...)
- **Grade** = quantity
- **Structural rules** depend on both mode and grade

---

## Relevance to CALC

### What CALC Already Has

**CALC's LNL implementation IS an adjunction**:

```
persistent_ctx  ≅  Cartesian category C
linear_ctx      ≅  Linear category M

Bang_L rule implements F : C → M
Implicit dereliction implements G : M → C
```

The adjunction F ⊣ G gives the ! comonad.

### Why Adjunctions Matter for CALC

1. **Cut elimination**: Adjunction structure guarantees cut admissibility
2. **Modularity**: Add new modalities by adding new adjunctions
3. **Semantic foundation**: Categorical models via adjunctions
4. **Resource management**: Residuation tracks resources

### Is Transfer an Adjunction?

**Analysis**: Ownership transfer `[Alice] A ⊸ [Bob] A` is NOT an adjunction.

**Issues**:
1. **Non-symmetric**: Transfer requires Alice's consent, not Bob's
2. **Linear, not adjoint**: Transfer consumes [Alice] A, creates [Bob] A — this is a morphism, not an adjunction
3. **Modes don't match**: Ownership is an index on formulas, not a mode

**Conclusion**: Ownership transfer is a **linear implication** (morphism):
```
transfer : [Alice] A ⊸ [Bob] A
```

The ownership modality `[P]` is an **index** (like in indexed categories), not a mode. Ownership might be better modeled as a **fibration** over the set of principals. (See [[fibrations-study-plan]] for this approach.)

---

## Assessment and Synthesis

### What Adjoint Logic Handles Well

| Feature | Support |
|---------|---------|
| LNL decomposition (!) | ✅ Direct embedding |
| Subexponentials | ✅ Modes as indices |
| Session types (shared/linear) | ✅ Nomos demonstrates |
| S4/lax modalities | ✅ Standard examples |
| Graded types | ✅ Via graded extension |
| Cut elimination | ✅ Generic proof |

### What Adjoint Logic Doesn't Handle Directly

| Feature | Support Level |
|---------|--------------|
| Principal identity (WHO owns) | ⚠️ Modes don't naturally identify principals |
| Composite principals (A ∧ B) | ❌ No mode products |
| Authorization (says, speaks for) | ❌ Different concern |
| Threshold (k-of-n) | ❌ Not expressible |

### Recommendation: Two-Layer Architecture

**Layer 1: Adjoint Logic (structural properties)**
```
Modes: {U (cartesian), L (linear), S (shared), A (affine), ...}
Morphisms: structural inclusions (U ≥ L, S ≥ L, ...)
Modalities: ↑/↓ for resource management
```

**Layer 2: Principal Index (epistemic properties)**
```
Principals: {Alice, Bob, shared, ...}
Index on formulas: [Alice] A, [Bob] A, [Alice ∧ Bob] A
Delegation: Alice speaks for Bob
Says: Alice says φ
```

**The combination**:
```
[Alice] (↓ᵁₗ A)    -- Alice controls a linear resource lifted from cartesian
```

Principal indexing is **orthogonal to** mode indexing — they combine multiplicatively.

### Conclusion

**Use adjoint logic as the structural foundation.** It:
- Already underlies CALC's LNL implementation
- Provides generic cut elimination
- Handles session types (via Nomos)
- Extends to graded types (via Eades-Orchard)

**But keep authorization separate.** Adjoint logic doesn't directly handle:
- Principal identity (who owns)
- Authorization reasoning (says, speaks for)
- Composite principals (A ∧ B)

---

## References

### Core Adjoint Logic Papers
- [Pruiksma et al., "Adjoint Logic" (2018)](http://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf)
- [Licata & Shulman, "Adjoint Logic with a 2-Category of Modes" (2016)](https://link.springer.com/chapter/10.1007/978-3-319-27683-0_16)
- [Licata, Shulman & Riley, "A Fibrational Framework" (FSCD 2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.25)

### Graded Extensions
- [Eades & Orchard, "Grading Adjoint Logic" (2020)](https://arxiv.org/abs/2006.08854)
- [Hanukaev & Eades, "Combining Dependency, Grades, and Adjoint Logic" (2023)](https://arxiv.org/abs/2307.09563)

### LNL and Linear Logic
- [Benton, "A Mixed Linear and Non-Linear Logic" (1994)](https://www.researchgate.net/publication/221558077)
- [nLab: !-modality](https://ncatlab.org/nlab/show/!-modality)
- [Schalk, "What is a categorical model for Linear Logic?"](http://www.cs.man.ac.uk/~schalk/notes/llmodel.pdf)

### Category Theory
- [nLab: Adjunction](https://ncatlab.org/nlab/show/adjunction)
- [Wikipedia: Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors)
- [Math3ma: What is an Adjunction?](https://www.math3ma.com/blog/what-is-an-adjunction-part-2)

### Applications
- [Das et al., "Resource-Aware Session Types for Digital Contracts" (Nomos)](https://arxiv.org/abs/1902.06056)
- [Pfenning, "Lecture Notes on Adjoint SAX" (15-836, 2023)](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/15-adjsax.pdf)

---

*Created: 2026-02-10 (merged from adjoint-logic-unifying-framework.md and adjunctions-deep-study.md)*
