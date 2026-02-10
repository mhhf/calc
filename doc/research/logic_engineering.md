---
title: "Logic Engineering: Designing Sequent Calculi"
created: 2026-02-10
modified: 2026-02-10
summary: Methodology for designing sound and complete sequent calculi balancing proof-theoretic and model-theoretic approaches with cut elimination verification.
tags: [logic-design, sequent-calculus, proof-theory, semantics, methodology]
---

# Logic Engineering: Designing Sequent Calculi

How to design a "good" and correct sequent calculus. This document covers the fundamental question: syntax first or semantics first?

> **See also:** [[proof-calculi-foundations]] for hierarchy of proof systems, [[display-calculus]] for display methodology, [[residuation]] for Galois connections, [[DSL-approaches]] for practical implementation.

---

## Table of Contents

1. [The Central Question](#the-central-question)
2. [Two Approaches to Logic Design](#two-approaches)
3. [Proof-Theoretic Semantics](#proof-theoretic-semantics)
4. [Model-Theoretic Semantics](#model-theoretic-semantics)
5. [The Practical Answer: Iterate!](#the-practical-answer)
6. [Checklist for a "Good" Sequent Calculus](#checklist)
7. [Tools for Display](#tools-for-display)
8. [Open Questions](#open-questions)

---

## The Central Question

> Should I start with semantics and create syntax for my logic? Or start with a "good" syntax and come up with semantics, seeing where my semantics needs new connectives?

**Short answer:** Both approaches work, and the best logics often emerge from iterating between them.

**Historical reality:**
- Model-theoretic semantics (Tarski, 1930s) came first as a framework
- Proof-theoretic semantics (Gentzen, 1935; crystallized 1960s-80s) emerged later
- Modern logic design often starts with **computational intuitions** and works both directions

---

## Two Approaches

### Approach 1: Semantics First

**Start with:** A model of what you want to capture (sets, resources, worlds, etc.)

**Then:** Design syntax (connectives, rules) that is **sound** and **complete** w.r.t. that semantics.

**Advantages:**
- Clear notion of "correct" (soundness = can't prove false things)
- Semantic intuitions guide design
- Completeness is the goal

**Disadvantages:**
- May get "ugly" proof rules with side conditions
- Semantics may not suggest good proof search
- Some semantics have no complete proof system (second-order logic)

**Example:** Modal logic S5
1. Start with Kripke semantics (equivalence relation on worlds)
2. Try to write sequent rules
3. Discover standard rules don't work — need hypersequents or labels

### Approach 2: Syntax First (Proof-Theoretic)

**Start with:** A proof system with "nice" properties (cut elimination, subformula property)

**Then:** Ask what semantics validates this system.

**Advantages:**
- Guaranteed good proof-theoretic behavior
- Rules have local character (good for proof search)
- Meaning comes from rules themselves

**Disadvantages:**
- May capture something you didn't intend
- Harder to explain to non-logicians
- May need to iterate to match intended meaning

**Example:** Linear logic
1. Girard analyzed the "geometry" of proofs
2. Decomposed classical connectives based on structural behavior
3. Semantics (coherence spaces, phase spaces, etc.) came after

---

## Proof-Theoretic Semantics

> "The meaning of logical connectives is to be found in their introduction and elimination rules."

### Core Ideas

1. **Meaning = Inferential Role**: A connective's meaning IS its proof rules
2. **Introduction rules are definitional**: They define the connective
3. **Elimination rules must be harmonious**: They should only extract what the intro rules put in

### Harmony (Prawitz/Dummett)

A connective is **harmonious** if its elimination rule doesn't give you "too much":

**Conjunction (harmonious):**
```
  Γ ⊢ A    Γ ⊢ B           Γ ⊢ A ∧ B
  ─────────────── ∧I       ─────────── ∧E₁
     Γ ⊢ A ∧ B               Γ ⊢ A
```

The elimination only extracts A (which the intro put in).

**"Tonk" (disharmonious, Prior's example):**
```
  Γ ⊢ A                   Γ ⊢ A tonk B
  ───────────── tonk-I    ─────────────── tonk-E
  Γ ⊢ A tonk B               Γ ⊢ B
```

You can prove anything! The elim gives you B even though intro only required A.

### Girard's View

> "The thesis is that the meaning of logical rules is to be found in the well-hidden geometrical structure of the rules themselves."

Girard sees meaning in the **symmetry** and **duality** of rules, not in external interpretations.

---

## Model-Theoretic Semantics

> "The meaning of a formula is its truth conditions in all models."

### Core Ideas

1. **Meaning = Truth Conditions**: ⟦A ∧ B⟧ = true iff ⟦A⟧ = true and ⟦B⟧ = true
2. **Validity = True in all models**: ⊨ A means A is true in every interpretation
3. **Soundness/Completeness relate syntax to semantics**

### The Tarski Paradigm

For a formula φ in language L:
- Define a class of **models** (structures interpreting the symbols)
- Define **satisfaction** φ holds in model M under assignment
- Formula is **valid** if satisfied in all models

### Soundness and Completeness

**Soundness:** If ⊢ A (provable), then ⊨ A (valid)
- Proof system doesn't prove false things

**Completeness:** If ⊨ A (valid), then ⊢ A (provable)
- Everything true is provable

**The ideal:** A proof system that is sound AND complete for your intended semantics.

---

## The Practical Answer: Iterate!

Real logic design is **iterative**:

```
┌─────────────────────────────────────────────────────┐
│                                                     │
│   Intuitions about domain                           │
│        ↓                                            │
│   Draft semantics (what should be true?)            │
│        ↓                                            │
│   Draft proof rules (how to prove things?)          │
│        ↓                                            │
│   Check: Do rules have cut elimination?             │
│        │                                            │
│        ├── No → Revise rules or add connectives     │
│        │                                            │
│        ↓ Yes                                        │
│   Check: Are rules sound for semantics?             │
│        │                                            │
│        ├── No → Revise semantics or restrict rules  │
│        │                                            │
│        ↓ Yes                                        │
│   Check: Are rules complete for semantics?          │
│        │                                            │
│        ├── No → Add rules or weaken semantics       │
│        │                                            │
│        ↓ Yes                                        │
│   Done! (or iterate for better properties)          │
│                                                     │
└─────────────────────────────────────────────────────┘
```

### Example: Designing Linear Logic

1. **Intuition:** Resources that can't be duplicated or discarded
2. **Draft semantics:** Formulas as finite resources
3. **Draft rules:** Remove contraction/weakening from classical logic
4. **Problem:** Classical ∧ splits into two connectives!
   - A ⊗ B (have both simultaneously)
   - A & B (can choose one)
5. **Solution:** Add both, with their own rules
6. **Check:** Cut elimination? Yes!
7. **Check:** Sound/complete for coherence spaces? Yes!

### Example: Adding Modality [Owner]

1. **Intuition:** Resource ownership — [Alice]A means "Alice owns resource A"
2. **Draft semantics:** Multi-agent Kripke model? Or labeled resources?
3. **Draft rules:** How does [Alice] interact with ⊗, ⊸?
4. **Question:** Is [Alice] residuated? Does it have an adjoint?
5. **Iterate:** Try different rule shapes, check cut elimination
6. **Use display calculus methodology** if standard rules have side conditions

---

## Checklist for a "Good" Sequent Calculus

### Must Have

- [ ] **Cut elimination**: Cut rule is admissible (can be removed from proofs)
- [ ] **Soundness**: Only valid formulas are provable
- [ ] **Identity**: A ⊢ A is derivable

### Should Have

- [ ] **Subformula property**: Cut-free proofs only use subformulas of conclusion
- [ ] **Completeness**: All valid formulas are provable
- [ ] **Decidability**: Proof search terminates (for propositional fragment)

### Nice to Have

- [ ] **No global side conditions**: Rules depend only on principal formula
- [ ] **Symmetry**: Left and right rules have parallel structure
- [ ] **Modularity**: Adding connectives doesn't break existing rules
- [ ] **Properness**: Rules closed under uniform substitution

### Red Flags

- ⚠️ Rules with **eigenvariable conditions** referencing entire context
- ⚠️ Rules requiring **inspection of all formulas** in context
- ⚠️ **Non-invertible** rules where you must guess
- ⚠️ Cut elimination proof that's **ad-hoc** for this specific system

---

## Tools for Display

When designing a display calculus, you have two main tools:

### Tool 1: Residuation

For binary connectives that form a **Galois connection**:

```
A • B ⊢ C   iff   A ⊢ B → C   iff   B ⊢ A -o C
```

**Use when:** Your connective has a natural "implication" partner.

**Examples:**
- Tensor ⊗ is residuated by lolli ⊸
- Conjunction ∧ is residuated by implication →
- Par ⅋ is residuated by... itself (in a sense)

**Structural version:** For every logical residuation, there's a structural one:
```
X , Y ⊢ Z   iff   X ⊢ Y > Z   iff   Y ⊢ Z < X
```

### Tool 2: Adjoint Decomposition

For connectives that are **NOT** residuated but can be **decomposed**:

```
! = F ∘ G

where F ⊣ G (F is left adjoint to G)
```

**Use when:** Your connective changes the "mode" of a formula.

**Examples:**
- Exponential ! (linear → Cartesian → linear)
- Modal □ (possible → necessary)

**Key insight:** Adjoints aren't residuals of EACH OTHER, but they have a well-behaved relationship:
```
F(X) ⊢ Y   iff   X ⊢ G(Y)
```

This is like residuation but between DIFFERENT TYPES.

### Summary

| Connective Type | Tool | Example |
|-----------------|------|---------|
| Binary, symmetric | Residuation | ⊗ ↔ ⊸ |
| Mode-changing, unary | Adjoint decomposition | ! = F ∘ G |
| Self-dual | Structural negation | Classical negation |

---

## Open Questions

### For Your Research

1. **How do you know if a connective should be residuated or adjoint-decomposed?**
   - Is there a decision procedure?
   - What if neither works?

2. **Can all "interesting" logics be displayed?**
   - What's the limit of display calculus methodology?
   - Are there logics that inherently resist display?

3. **How do you design structural connectives?**
   - Is there a systematic way to derive them from logical connectives?
   - What properties must they satisfy?

4. **When semantics and syntax disagree, which wins?**
   - If you have a beautiful semantics but ugly proof theory, do you accept it?
   - If you have elegant rules but no obvious semantics, is that okay?

5. **How do you add quantification to display calculus?**
   - First-order variables have different scoping
   - How do eigenvariable conditions interact with display?

### Research TODO

- [ ] Study how Girard discovered linear logic (the "geometry" of proofs)
- [ ] Study Benton's LNL logic as example of adjoint decomposition
- [ ] Study multi-type display calculus methodology (Frittella et al.)
- [ ] Study labelled sequents and how they avoid display issues
- [ ] Study the relationship between categorical semantics and proof rules

---

## Sources

- [Proof-Theoretic Semantics (Stanford Encyclopedia)](https://plato.stanford.edu/entries/proof-theoretic-semantics/)
- [Girard: On the Meaning of Logical Rules I](https://girard.perso.math.cnrs.fr/meaning1.pdf)
- [Girard: Linear Logic - Syntax and Semantics](https://girard.perso.math.cnrs.fr/Synsem.pdf)
- [Structural proof theory - Wikipedia](https://en.wikipedia.org/wiki/Display_logic)
- [Substructural Logics (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-substructural/)

---

*Last updated: 2026-01-26*
