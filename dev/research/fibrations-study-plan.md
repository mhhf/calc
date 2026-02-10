# Fibrations Study Plan

A minimal but complete study path to understand fibrations well enough to model ownership `[Alice] A` as "A in the fiber over Alice."

> **See also:** [[adjunctions-and-adjoint-logic]] for categorical background, [[ownership-design]] for ownership representation design.

---

## Table of Contents

1. [Why Fibrations for CALC?](#why-fibrations-for-calc)
2. [Prerequisites](#prerequisites-what-you-need-first)
3. [The Intuition First](#the-intuition-first)
4. [Study Path](#study-path)
5. [Reading Order Summary](#reading-order-summary)
6. [Key Concepts Checklist](#key-concepts-checklist)
7. [How This Applies to CALC](#how-this-applies-to-calc)
8. [References](#references)

---

## Why Fibrations for CALC?

**The ownership insight:** `[Alice] A` is NOT "A at mode Alice" but "A in the fiber over Alice."

This means:
- Base category = Principals (Alice, Bob, ...)
- Fiber over P = Resources owned by P
- Transfer `[Alice] A ⊸ [Bob] A` = Reindexing along principal morphism

Fibrations give us:
- Proper categorical semantics for ownership
- Connection to dependent types (Lawvere: fibrations ≈ dependent types)
- Clean composition of transfers
- Well-understood metatheory

---

## Prerequisites (What You Need First)

### Essential (must know solidly)

1. **Categories, Functors, Natural Transformations**
   - Objects, morphisms, composition, identity
   - Functors preserve structure
   - Natural transformations = "morphisms between functors"
   - **Source:** Fong & Spivak Ch 1-2, or any intro

2. **Universal Properties**
   - Products, coproducts
   - Initial/terminal objects
   - Uniqueness up to isomorphism
   - **Source:** Fong & Spivak Ch 3

3. **Adjunctions (basic)**
   - F ⊣ G means Hom(F(X), Y) ≅ Hom(X, G(Y))
   - Unit η and counit ε
   - Free ⊣ Forgetful as paradigm
   - **Source:** Fong & Spivak Ch 4, or Awodey Ch 9

### Helpful (makes fibrations easier)

4. **Pullbacks**
   - Universal property of pullback square
   - Pullback of morphisms
   - **Source:** Awodey Ch 5, or any standard reference

5. **Contravariance and Presheaves**
   - Contravariant functors F: C^op → Set
   - Presheaves as "varying sets"
   - **Source:** Fong & Spivak Ch 7

---

## The Intuition First

### Level 0: Families of Sets

Before fibrations, understand **indexed families**:

```
Family of sets indexed by I:
  For each i ∈ I, we have a set A_i
```

Example: For each principal P, we have their resources Res_P.

### Level 1: The Total Space

Given a family {A_i}_{i ∈ I}, we can form the **disjoint union**:

```
E = ∐_{i ∈ I} A_i = { (i, a) | i ∈ I, a ∈ A_i }
```

There's a natural projection:

```
p: E → I
p(i, a) = i
```

The **fiber** over i is p⁻¹(i) = A_i (we recover the original sets!).

### Level 2: The Key Insight

A fibration generalizes this:
- E is the "total category" (all resources, all principals)
- B is the "base category" (principals)
- p: E → B is the projection
- Fiber over b = p⁻¹(b) = resources owned by principal b

**The magic:** Given a morphism f: a → b in B (think: "speaks for" or transfer direction), we can "pull back" objects from fiber over b to fiber over a.

---

## Study Path

### Phase 1: Build Intuition (1-2 days)

**Goal:** Understand fibrations informally through examples.

1. **Read:** [Families and Fibrations](https://www.paolocapriotti.com/blog/2013/02/20/families-and-fibrations/index.html) by Paolo Capriotti
   - Short, clear, builds from indexed families
   - Shows how Set example generalizes

2. **Read:** [Grrr(othendieck) fibrations](https://matteocapucci.wordpress.com/2023/02/02/grrrothendieck-fibrations/) by Matteo Capucci
   - Informal introduction
   - Good pictures and intuition

3. **Exercise:** Draw the fibration for CALC ownership
   ```
   E = { (Alice, 0.5 BTC), (Bob, 1.0 ETH), (Alice, 100 USD), ... }
   B = { Alice, Bob, Carol, ... }
   p: E → B projects to owner
   Fiber over Alice = { 0.5 BTC, 100 USD, ... }
   ```

### Phase 2: The Definition (1-2 days)

**Goal:** Understand cartesian morphisms and the definition.

4. **Read:** [nLab: Grothendieck fibration](https://ncatlab.org/nlab/show/Grothendieck+fibration)
   - Focus on: Definition, Idea section, Examples
   - Skip: 2-categorical details on first pass

5. **Key concept: Cartesian morphism**

   A morphism e → e' in E over f: p(e) → p(e') in B is **cartesian** if:
   - It's the "best" lift of f ending at e'
   - Universal property: any other lift factors through it uniquely

   **For CALC:** A cartesian morphism over "Alice speaks for Bob" lifts Bob's resource to Alice's control.

6. **Read:** Vistoli's notes, Sections 3.1-3.3 (definition only)
   - [Notes on Grothendieck topologies, fibered categories and descent theory](https://homepage.sns.it/vistoli/descent.pdf)
   - Very clear, uses concrete examples

### Phase 3: The Equivalence (2-3 days)

**Goal:** Understand fibrations ↔ indexed categories.

7. **Key theorem:** There's an equivalence
   ```
   Fib(B) ≃ [B^op, Cat]
   ```
   Fibrations over B ↔ Contravariant pseudofunctors B → Cat

8. **What this means for CALC:**
   - Instead of fibration p: E → B
   - Think of assignment: P ↦ Res_P (each principal gets their resources)
   - Morphisms f: P → Q in B give functors Res_Q → Res_P (reindexing)

9. **The Grothendieck construction:** Converts between these views
   - From indexed family {Res_P}_{P ∈ B} to fibration
   - From fibration to indexed family

10. **Read:** Jacobs, Chapter 1.1-1.4 (first 30 pages)
    - [Categorical Logic and Type Theory](https://people.mpi-sws.org/~dreyer/courses/catlogic/jacobs.pdf)
    - Systematic treatment with type-theoretic motivation

### Phase 4: Connection to Dependent Types (2-3 days)

**Goal:** See how fibrations model dependent types.

11. **The Lawvere insight:**
    ```
    Fibrations ≈ Dependent Types
    ```
    - Base category B ≈ context of type variables
    - Fiber over b ≈ types depending on b
    - Cartesian morphisms ≈ substitution

12. **For CALC:**
    ```
    Principal P : Principal
    Resource A : Type
    [P] A : Type    -- "A depending on P"
    ```

    The fiber semantics says: `[P] A` lives in the fiber over P.

13. **Read:** Jacobs, Chapter 1.9-1.10 (indexed categories, relation to fibrations)

14. **Read:** [A Gentle Introduction to Categorical Logic and Type Theory](https://ericschmid-uchicago.github.io/notes/cl_and_tt_v2.pdf) by Eric Schmid
    - Sections on fibrations and dependent types

### Phase 5: Apply to CALC (1-2 days)

**Goal:** Write down the fibration for ownership.

15. **Define the base category:**
    ```
    Objects: Principals (Alice, Bob, shared, ...)
    Morphisms: Authority relations (speaks-for, delegation)
    ```

16. **Define the total category:**
    ```
    Objects: Pairs (P, A) where P is principal, A is resource
    Morphisms: (P, A) → (Q, B) over f: P → Q in base
    ```

17. **Verify cartesian morphisms exist:**
    - For transfer f: Alice → Bob (Alice speaks for Bob)
    - Cartesian lift of Bob's resource to Alice

18. **Check:** Does transfer compose correctly?
    ```
    [Alice] A ⊸ [Bob] A ⊸ [Carol] A
    ```
    Should correspond to composition in base.

---

## Reading Order Summary

| Order | Resource | Time | Focus |
|-------|----------|------|-------|
| 1 | Capriotti blog post | 30 min | Families → fibrations intuition |
| 2 | Capucci blog post | 30 min | Pictures, informal |
| 3 | nLab: Grothendieck fibration | 1-2 hr | Definition, examples |
| 4 | Vistoli notes 3.1-3.3 | 2-3 hr | Precise definition |
| 5 | Jacobs Ch 1.1-1.4 | 3-4 hr | Systematic treatment |
| 6 | Jacobs Ch 1.9-1.10 | 2-3 hr | Indexed categories |
| 7 | Schmid notes (fibration sections) | 2 hr | Type theory connection |

**Total time:** ~2 weeks at a few hours per day

---

## Key Concepts Checklist

By the end, you should understand:

- [ ] **Fibration** p: E → B (projection from total to base)
- [ ] **Fiber** E_b = p⁻¹(b) (objects over a given base object)
- [ ] **Cartesian morphism** (universal lift)
- [ ] **Cleavage** (systematic choice of cartesian lifts)
- [ ] **Grothendieck construction** (indexed family ↔ fibration)
- [ ] **Reindexing** (pulling back along base morphisms)
- [ ] **Connection to dependent types** (Lawvere correspondence)

---

## How This Applies to CALC

### The Ownership Fibration

```
Base B = Principal
  Objects: Alice, Bob, Carol, shared, ...
  Morphisms: f: P → Q means "P speaks for Q" (or authority relation)

Total E = Owned Resources
  Objects: (P, A) where P owns resource A
  Morphisms: authority-preserving resource morphisms

Projection p: E → B
  p(P, A) = P   (who owns it)

Fiber E_P = { A | P owns A }
  All resources owned by P
```

### Transfer as Reindexing

Given authority `f: Alice → Bob` (Alice speaks for Bob):

```
Reindexing f*: E_Bob → E_Alice
  "Alice can access Bob's resources"
```

The transfer rule `[Alice] A ⊸ [Bob] A` is a morphism in E over some f in B.

### Composition

```
Alice speaks for Bob, Bob speaks for Carol
⟹ Alice speaks for Carol (composition in B)

[Alice] A ⊸ [Bob] A ⊸ [Carol] A
⟹ [Alice] A ⊸ [Carol] A (composition in E)
```

Fibration structure ensures these compose correctly.

---

## References

### Primary Sources

- [Jacobs, Categorical Logic and Type Theory](https://people.mpi-sws.org/~dreyer/courses/catlogic/jacobs.pdf) — The comprehensive reference
- [Vistoli, Notes on fibered categories and descent](https://homepage.sns.it/vistoli/descent.pdf) — Clear geometric treatment
- [nLab: Grothendieck fibration](https://ncatlab.org/nlab/show/Grothendieck+fibration) — Reference

### Introductory

- [Capriotti, Families and fibrations](https://www.paolocapriotti.com/blog/2013/02/20/families-and-fibrations/index.html) — Best first read
- [Capucci, Grrr(othendieck) fibrations](https://matteocapucci.wordpress.com/2023/02/02/grrrothendieck-fibrations/) — Informal
- [Schmid, A Gentle Introduction to Categorical Logic and Type Theory](https://ericschmid-uchicago.github.io/notes/cl_and_tt_v2.pdf)

### Background Category Theory

- [Fong & Spivak, Seven Sketches](https://arxiv.org/abs/1803.05316) — Applied CT, your preferred book
- [Awodey, Category Theory](https://global.oup.com/academic/product/category-theory-9780199237180) — Standard reference

### Advanced

- [Streicher, Fibered Categories à la Bénabou](https://www2.mathematik.tu-darmstadt.de/~streicher/FIBR/FiBo.pdf) — Bénabou's approach
- [arXiv:1806.06129, Categorical Notions of Fibration](https://arxiv.org/pdf/1806.06129) — Survey

---

*Last updated: 2026-01-29*
