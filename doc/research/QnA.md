# Deep Answers: Proof Theory Questions

Accessible Q&A-style explanations of foundational proof theory concepts. For deeper treatment, see the dedicated documents referenced below.

---

## Related Documents

| Topic | Primary Document |
|-------|------------------|
| Residuation | [[residuation]] |
| Display calculus | [[display-calculus]] |
| Exponentials (!) problem | [[exponential-display-problem]] |
| Adjoint decomposition | [[adjunctions-and-adjoint-logic]] |
| Multi-type display calculus | [[multi-type-display-calculus]] |

---

## Table of Contents

1. [Are Structural Connectives Limited?](#1-are-structural-connectives-limited)
2. [What is Residuation and Why Don't All Connectives Have Residuals?](#2-what-is-residuation)
3. [How Were Exponentials Displayed in "Linear Logic Properly Displayed"?](#3-exponentials-in-linear-logic-properly-displayed)
4. [What is the Display Property?](#4-what-is-the-display-property)
5. [Which Connectives Don't Decompose into Left/Right Rules?](#5-decomposition-failures)
6. [Cut and Efficiency: Should We Sometimes Use Cut?](#6-cut-and-efficiency)
7. [What is Context-Sensitivity?](#7-context-sensitivity)
8. [Fixpoints and Cyclic Proofs](#8-fixpoints-and-cyclic-proofs)
9. [Non-Determinism in Classical Cut-Elimination](#9-non-determinism)

---

## 1. Are Structural Connectives Limited?

**Your question:** There are only a few structural connectives — does this mean the logics that are expressible are very limited?

### Short Answer: No!

The structural connectives are **not fixed** — you add structural connectives as needed for your logic. Different logics have different structural connectives.

### How It Works

**Basic linear logic** might have:
- `,` (comma) — structural counterpart of ⊗ (tensor)
- `;` (semicolon) — structural counterpart of ⅋ (par)
- `>` — structural counterpart of ⊸ (lolli)
- `I` — structural unit

**Modal logic** adds:
- `•` — structural counterpart of □ (box)
- `◦` — structural counterpart of ◇ (diamond)

**Multi-type display calculus** goes further — different TYPES of structures:
- Formulas of type "proposition"
- Formulas of type "action"
- Formulas of type "agent"

### The Real Limitation

The limitation is not the **number** of structural connectives, but the **requirement** that they form residuated pairs (Galois connections). This is where exponentials (`!`, `?`) cause problems — they're not residuated in the standard sense.

---

## 2. What is Residuation?

> **See also:** [[residuation]] for comprehensive treatment with algebraic details.

**Your question:** I need to understand residuation in depth, including why not all connectives have residuals.

### Definition

**Residuation** is a generalization of the relationship between multiplication and division, or between conjunction and implication.

Given a binary operation `•`, its **left residual** `\` and **right residual** `/` satisfy:

```
x • y ≤ z   iff   y ≤ x \ z   iff   x ≤ z / y
```

In other words: "x • y implies z" iff "y implies (x implies z)" iff "x implies (z given y)"

### Example: Linear Logic

For tensor (⊗) and linear implication (⊸):

```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C   iff   B ⊢ A -o C
```

This is exactly residuation! The lolli (⊸) is the residual of tensor (⊗).

**Structurally:**
```
X , Y ⊢ Z   iff   X ⊢ Y > Z   iff   Y ⊢ Z < X
```

The structural `>` is the residual of the structural comma `,`.

### Why Residuation Matters for Display Calculus

The **display postulates** (rules that shuffle structures around) are exactly the residuation laws:

```
X , Y ⊢ Z
─────────── (residuation)
X ⊢ Y > Z
```

This rule lets us "display" X by moving Y to the other side. Without residuation, you can't move things around, so you can't display arbitrary substructures.

### Why Not All Connectives Have Residuals

**1. Negation (¬):**

Negation is unary, so it doesn't fit the binary residuation pattern directly. In classical logic, negation swaps sides:

```
A ⊢ B   iff   ¬B ⊢ ¬A
```

This is a **Galois connection** but with a twist (it's contravariant). Display calculus handles this with a structural negation `*`.

**2. Exponentials (!, ?):**

The bang (!) and why-not (?) are **not residuated**. Here's why:

For residuation, you'd need something like:
```
!A ⊗ B ⊢ C   iff   !A ⊢ B ⊸ C   (?)
```

But `!` has special properties:
- `!A ⊢ !A ⊗ !A` (duplication/contraction)
- `!A ⊢ I` (discarding/weakening)

These properties **break** the residuation:
- If `!A ⊗ B ⊢ C` implied `!A ⊢ B ⊸ C`, and we could duplicate `!A`, we'd get `!A ⊗ !A ⊢ B ⊸ C`
- This would mean duplication on one side but not on the other

The structural rules for `!` would be **unsound** if given a standard structural counterpart.

**3. Fixpoint operators (μ, ν):**

Least/greatest fixpoint operators don't have residuals because they're defined recursively, not algebraically.

### Algebraic Perspective

In a **residuated lattice**, every operation has residuals by definition. The exponentials `!` and `?` form a **comonad** and **monad** respectively — different algebraic structure than residuated operations.

**Sources:**
- [Residuated lattice - Wikipedia](https://en.wikipedia.org/wiki/Residuated_lattice)
- [Substructural Logics and Residuated Lattices](https://link.springer.com/chapter/10.1007/978-94-017-3598-8_8)
- [Galois connection - Wikipedia](https://en.wikipedia.org/wiki/Galois_connection)

---

## 3. Exponentials in "Linear Logic Properly Displayed"

> **See also:** [[exponential-display-problem]] and [[adjunctions-and-adjoint-logic]] for the full treatment of ! decomposition.

**Your question:** If exponentials are not residuated "in the usual sense" — in which sense ARE they? What tools were used to display them?

### The Problem

From the paper:

> "If structural counterparts for exponentials were allowed in the language of Belnap's display calculus for linear logic, then the resulting calculus would lose the display property, due to the fact that this property critically hinges on the presence of certain structural rules (the so-called display rules) for all structural connectives, which would be unsound in the case of exponentials, precisely due to their not being residuated."

In other words: if you try to add a structural `!` with standard display postulates, you'd get:

```
!X , Y ⊢ Z
───────────── (would-be display postulate)
!X ⊢ Y > Z
```

But this is **unsound** because `!` allows contraction/weakening that shouldn't transfer across the turnstile this way.

### The Solution: Adjoint Decomposition

The key insight from Greco & Palmigiano:

> "The approach takes its move from Girard's initial idea about linear logic arising from the decomposition of classical and intuitionistic connectives and is based on viewing exponentials as compositions of adjoint maps."

**What does this mean?**

Instead of treating `!` as a single connective, decompose it into TWO connectives that form an **adjunction**:

```
! = F ∘ G

where:
  F : Cartesian → Linear    (left adjoint)
  G : Linear → Cartesian    (right adjoint)
```

This is Benton's **LNL (Linear/Non-Linear) logic** approach:
- Have TWO kinds of formulas: linear and non-linear (Cartesian)
- `!A` becomes "embed a linear formula into Cartesian world, then bring it back"

### Multi-Type Display Calculus

The solution uses **multi-type** display calculus:

1. **Type 1: Linear formulas** — no contraction, no weakening
2. **Type 2: Cartesian formulas** — contraction and weakening allowed

The exponential `!` is then a **bridge** between types:
- `F : Cartesian → Linear` — forget that you have contraction/weakening
- `G : Linear → Cartesian` — promote to unlimited use

Because `F` and `G` are **adjoints** (not residuals of each other, but related by an adjunction), they have well-behaved proof rules that preserve cut elimination.

### Why This Works

**Adjoints ARE like "directional residuals":**

```
F(X) ⊢ Y   iff   X ⊢ G(Y)
```

This is similar to residuation but between DIFFERENT types/categories!

**The key difference:**
- Residuation: `A • B ⊢ C` iff `A ⊢ B → C` (same type on both sides)
- Adjunction: `F(A) ⊢ B` iff `A ⊢ G(B)` (different types on each side)

For exponentials, this captures exactly the right behavior:
- Moving from Cartesian to Linear loses structural power (no more contraction)
- Moving from Linear to Cartesian gains structural power

### What Makes It "Proper"

> "Properness (i.e., closure under uniform substitution of all parametric parts in rules) is the main technical novelty of the present proposal."

A **proper** display calculus has rules that work for ANY substitution of structural variables. This makes cut elimination proofs simpler and more modular.

**Sources:**
- [Linear Logic Properly Displayed (ACM)](https://dl.acm.org/doi/10.1145/3570919)
- [arXiv:1611.04181](https://arxiv.org/abs/1611.04181)
- [nLab: !-modality](https://ncatlab.org/nlab/show/!-modality)

---

## 4. What is the Display Property?

> **See also:** [[display-calculus]] for Belnap's conditions C1-C8.

**Your question:** Can you remind me what the display property is?

### Definition

> "A Gentzen calculus has the **display property** if every antecedent [consequent] constituent can be displayed as the antecedent [consequent] standing alone."

In simpler terms: **any formula can be isolated on one side of the turnstile** using only structural rules.

### Example

Given the sequent:
```
(A , B) , C ⊢ D
```

Suppose we want to "display" B (make it the entire antecedent). Using display postulates:

```
(A , B) , C ⊢ D
────────────────── associativity
A , (B , C) ⊢ D
────────────────── residuation (move A right)
B , C ⊢ A > D
────────────────── residuation (move C right)
B ⊢ C > (A > D)
```

Now B is "displayed" — it's the entire left side!

### Why It Matters

**For cut elimination:**

The cut rule is:
```
X ⊢ A      A ⊢ Y
─────────────────── cut
     X ⊢ Y
```

To reduce a cut, you need the cut formula `A` to be the **principal formula** of the rules that produced it. But what if `A` is buried inside a structure?

```
X , A , Z ⊢ W      A , B ⊢ Y
──────────────────────────────── cut (?)
            ???
```

The display property lets you **first display A**, then apply cut cleanly:

```
X , A , Z ⊢ W
─────────────── display A
A ⊢ (X , Z) > W

A ⊢ (X , Z) > W      A , B ⊢ Y
───────────────────────────────── cut
            ...
```

**Belnap's insight:** If you have the display property AND satisfy conditions C1-C8, cut elimination follows automatically!

---

## 5. Which Connectives Don't Decompose into Left/Right Rules?

**Your question:** Which connectives don't break down nicely into subgoals? How can I check if a connective can be decomposed?

### The Ideal: Left and Right Introduction

In sequent calculus, each connective has:
- **Right rule**: introduces the connective on the RIGHT (in the succedent)
- **Left rule**: introduces the connective on the LEFT (in the antecedent)

For conjunction (∧):
```
  Γ ⊢ A    Γ ⊢ B
  ─────────────── ∧R
     Γ ⊢ A ∧ B

  Γ, A ⊢ C
  ─────────── ∧L₁
  Γ, A ∧ B ⊢ C
```

The premises are **strictly simpler** — they have subformulas of the conclusion.

### Connectives That Cause Problems

**1. Classical Negation (¬):**

The problem isn't decomposition per se, but **duplication and symmetry**:

```
  Γ ⊢ A, Δ
  ────────── ¬L
  Γ, ¬A ⊢ Δ

  Γ, A ⊢ Δ
  ────────── ¬R
  Γ ⊢ ¬A, Δ
```

These rules SWAP sides. Combined with contraction, this creates non-determinism in cut elimination.

**2. Modalities (□, ◇) in Some Logics:**

For S5 modal logic, the standard sequent rules don't work:

```
  □Γ ⊢ A
  ───────── □R (S5)
  □Γ ⊢ □A
```

The side condition "all formulas in Γ must be boxed" is **global** — it depends on the entire context, not just the principal formula. This breaks the local nature of sequent rules.

Solution: Use **hypersequents** or **labelled sequents**.

**3. Exponentials (!, ?):**

For bang (!):
```
  ?Γ ⊢ A
  ───────── !R
  ?Γ ⊢ !A
```

Again, a global side condition: all context formulas must be "why-not" (?). In standard sequent calculus, this works but complicates cut elimination. In display calculus, it's worse — no structural counterpart exists.

**4. Fixpoints (μX.φ, νX.φ):**

Least fixpoint (μ):
```
   φ[μX.φ/X] ⊢ A
   ─────────────── μL
     μX.φ ⊢ A
```

The problem: this unfolds infinitely! You can always unfold again:
```
   φ[φ[μX.φ/X]/X] ⊢ A
   ─────────────────── μL
     φ[μX.φ/X] ⊢ A
     ─────────────── μL
       μX.φ ⊢ A
```

There's no **termination** guarantee without extra machinery (cyclic proofs, annotations).

### How to Check Decomposability

A connective ○ decomposes well if you can write rules where:

1. **Subformula property**: Premises contain only subformulas of conclusion
2. **No global side conditions**: Rule applicability depends only on the principal formula, not the whole context
3. **Principal formula is consumed**: The connective being introduced doesn't appear in premises (or appears strictly smaller)
4. **Invertibility is clear**: You know whether the rule is invertible (can be applied eagerly) or requires choice

If any of these fail, you need extensions (hypersequents, labels, cyclic proofs, etc.).

---

## 6. Cut and Efficiency: Should We Sometimes Use Cut?

**Your question:** Does Boolos's result mean we should sometimes use cut even if cut-free proofs exist?

### Yes, Absolutely!

**Boolos's result (1984):**

> "In his essay 'Don't Eliminate Cut!' George Boolos demonstrated that there was a derivation that could be completed in a page using cut, but whose analytic proof could not be completed in the lifespan of the universe."

This is not an exaggeration. The blowup can be **non-elementary** — towers of exponentials:

```
With cut:     n steps
Without cut:  2^2^2^...^2 steps (tower of height n)
```

### Why This Happens

**Cut is composition:**
```
Proof of A → B  +  Proof of B → C  =  Proof of A → C (via cut)
```

Cut-free, you'd have to **inline** the proof of B everywhere it's used. If B is used many times (contraction!), this causes exponential blowup.

**Example:**
```
Lemma L: proves A → B
Theorem: uses L 100 times

With cut: Theorem + L = small
Without cut: Theorem with L inlined 100 times = huge
```

### Practical Implications

**1. Proof CHECKING vs proof SEARCH:**

- **Checking**: Cut-free is fine — just verify each step
- **Search**: Use cuts! Then optionally eliminate them if needed

**2. Human-readable proofs:**

> "Cuts are indispensable for formalizing proofs in a human-readable way."

Lemmas, definitions, and modular reasoning ALL use cut. Nobody writes cut-free proofs by hand.

**3. Proof compression:**

> "Cuts have a very strong compression power."

If you need to store or transmit proofs, keep the cuts!

**4. When to eliminate cut:**

- When you need the **subformula property** (e.g., interpolation theorems)
- When you're doing **proof-theoretic analysis** (consistency proofs)
- For **decidability proofs** (showing search terminates)

### The Nuanced Answer

**Use cut for:**
- Human reasoning
- Proof compression
- Modular proof development
- Interactive theorem proving

**Eliminate cut for:**
- Meta-theoretic analysis
- Decidability arguments
- Extracting computational content
- Interpolation/Beth definability

**Sources:**
- Boolos, "Don't Eliminate Cut!" Journal of Philosophical Logic 13 (1984) 373-378
- [Cut-elimination theorem - Wikipedia](https://en.wikipedia.org/wiki/Cut-elimination_theorem)
- [Eliminating cuts (Richard Zach)](https://people.ucalgary.ca/~rzach/blog/2005/03/eliminating-cuts.html)

---

## 7. What is Context-Sensitivity?

**Your question:** What does "context-sensitive rules" mean? Use examples.

### Definition

A rule is **context-sensitive** if its applicability depends on the **entire context**, not just the principal formula.

### Example 1: Modal Logic S5

The box-right rule for S5:

```
  □Γ ⊢ A
  ───────── □R
  □Γ ⊢ □A
```

**Side condition:** Every formula in Γ must be boxed (□).

This is context-sensitive because to apply □R, you must **inspect all formulas in the context**. You can't just look at the principal formula □A.

**Why is this problematic?**

In standard sequent calculus, rules should be **local** — you should be able to apply a rule by looking only at the principal formula. Global inspection breaks:
- **Modularity**: Can't reason about rules in isolation
- **Proof search**: Need to track global invariants
- **Cut elimination**: Harder to prove

### Example 2: Exponential Rules

The bang-right rule:

```
  ?Γ ⊢ A
  ───────── !R
  ?Γ ⊢ !A
```

**Side condition:** Every formula in Γ must be "why-not" (?).

Same problem — you need to check the entire context.

### Example 3: Type-Raising in Categorial Grammar

In combinatory categorial grammar (CCG):

```
X → T/(T\X)   if T is atomic
```

**Side condition:** T must be an **atomic** type.

This is context-sensitive because "atomic" is a global property, not determined by the rule itself.

### Solutions

**1. Labelled sequents:**

Add explicit labels (worlds) to track what rules are applicable:
```
w: □A, wRv, v: B ⊢ w: C
```

Now the "global" condition becomes "local" — just check the labels.

**2. Hypersequents:**

Use multiple sequents that interact:
```
Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ... | Γₙ ⊢ Δₙ
```

The side conditions become structural rules between components.

**3. Multi-type display calculus:**

Different types have different structural rules:
- Linear type: no contraction
- Cartesian type: contraction allowed

Context-sensitivity becomes type-sensitivity, which is handled cleanly.

---

## 8. Fixpoints and Cyclic Proofs

**Your question:** Why do fixpoints need cyclic proofs or annotations?

### The Problem

The μ-calculus has least (μ) and greatest (ν) fixpoint operators:

```
μX.φ(X)  =  the least X such that X = φ(X)
νX.φ(X)  =  the greatest X such that X = φ(X)
```

### The Naive Rule

For least fixpoint:
```
   φ[μX.φ/X] ⊢ A
   ─────────────── μL
     μX.φ ⊢ A
```

This says: to prove something about μX.φ, unfold it once and prove about φ[μX.φ/X].

**The problem:** You can unfold forever!

```
          ...
   ───────────────
   φ[φ[μX.φ/X]/X] ⊢ A
   ─────────────────── μL
     φ[μX.φ/X] ⊢ A
     ─────────────── μL
       μX.φ ⊢ A
```

There's no **base case**. The proof tree is infinite!

### Example: Termination

Consider the formula "all runs terminate":

```
νX.(□X)  =  "always eventually something, forever"
μX.(□X)  =  "eventually always done" (termination)
```

To prove μX.(□X), you'd need to show that unfolding eventually reaches a "done" state. But the naive rule just keeps unfolding.

### Solution 1: Cyclic Proofs

Allow the proof tree to be a **graph** (not a tree) with cycles:

```
       ┌──────────────────────┐
       │                      │
       ▼                      │
   φ[μX.φ/X] ⊢ A ◄────────────┘
   ─────────────── μL
     μX.φ ⊢ A
```

**Soundness condition:** On every infinite path through the (unfolded) proof, some fixpoint must "make progress" infinitely often.

> "In cyclic proof theory, one traces formulas through an infinite sequent calculus derivation obtained by unfolding the cyclic derivation. There is a PSPACE-complete soundness condition."

### Solution 2: Annotations

Add explicit **ordinal annotations** to track "how much unfolding is left":

```
   φ[μ^α X.φ/X] ⊢ A
   ───────────────── μL (α > 0)
     μ^(α+1) X.φ ⊢ A
```

The annotation α decreases with each unfolding. When α = 0, you must stop.

### Why Standard Sequent Calculus Doesn't Work

1. **No termination**: Infinite unfolding
2. **No subformula property**: μX.φ contains itself after unfolding
3. **Induction hidden**: The "reason" the fixpoint terminates is external to the rules

**Sources:**
- [Cyclic proofs for first-order μ-calculus](https://academic.oup.com/jigpal/article/32/1/1/6653082)
- [Proof Systems for Two-way Modal μ-Calculus](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/proof-systems-for-twoway-modal-calculus/428EBC95D512384C067BD4C0BB5910AC)

---

## 9. Non-Determinism in Classical Cut-Elimination

**Your question:** Why does non-determinism mean there isn't a good sequent calculus?

### The Problem

> "Cut-elimination for classical sequent calculus is known to have non-deterministic behaviour."

When you eliminate a cut, there may be **multiple ways** to proceed, leading to **different normal forms**.

### Example

Consider this proof with a cut on A ∨ B:

```
Proof 1: Γ ⊢ A ∨ B    (proved via left disjunct A)
Proof 2: A ∨ B ⊢ Δ    (case split on A and B)
───────────────────────────────────────────────── cut
                    Γ ⊢ Δ
```

To eliminate the cut, you need to "match" how A ∨ B was proved with how it was used.

But Proof 2 case-splits: it has branches for A and for B.
And Proof 1 only proved A.

**Non-determinism:** Do you:
- Follow the A branch (since that's what was proved)?
- Somehow also deal with the B branch?

In classical logic with **contraction**, A ∨ B might be used multiple times, in different ways!

### The Consequence: Multiple Normal Forms

> "Baaz and Hetzl construct a sequence of polynomial-length proofs having a non-elementary number of different cut-free normal forms."

Same proof, many different cut-free versions. They're not just "rearrangements" — they can have **different propositional structure** and extract **different computational content**.

### Why This Matters

**1. No canonical proof:**

In intuitionistic logic, cut-elimination gives you THE normal form. In classical logic, you get MANY. Which one is "the" proof?

**2. Computational content is ambiguous:**

Via Curry-Howard, proofs are programs. Different normal forms = different programs! Classical logic doesn't determine which program you get.

**3. Confluence fails:**

> "When considering cut-elimination in the sequent calculus for classical first-order logic, it is well known that this system, in its most general form, is neither confluent nor strongly normalizing."

No confluence = no unique normal form. Not strongly normalizing = might not even terminate (though it does terminate, just non-deterministically).

### Solutions

**1. Intuitionistic logic:**

Remove excluded middle. Cut-elimination becomes deterministic. This is Lafont's suggestion.

**2. Linear logic:**

Remove contraction. Cut-elimination becomes deterministic (for the multiplicative fragment).

**3. Polarization/focusing:**

Use a polarized calculus (like LKF) where positive and negative formulas are treated differently. This restores determinism by controlling when contraction happens.

**4. Choose a strategy:**

Fix a specific cut-elimination strategy. You get ONE normal form (not THE normal form, but at least a consistent choice).

### Herbrand Confluence

A weaker result: even if proofs differ, their **Herbrand disjunctions** (which witnesses they choose for existentials) can be the same:

> "All (possibly infinitely many) normal forms of the non-erasing reduction lead to the same Herbrand-disjunction."

So the "computational content" might agree at a coarser level.

**Sources:**
- [On the non-confluence of cut-elimination](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/on-the-nonconfluence-of-cutelimination/BACF2431183E810A3A6781194D075D9E)
- [Confluence in the sequent calculus (Proof Theory Blog)](https://prooftheory.blog/2021/09/23/confluence-in-the-sequent-calculus/)

---

## 10. Is My Understanding of Display Correct?

**Your question:** In order to display a property/connective we have tools of 'residuation' and 'adjoints'. Since ! can be displayed with adjoints and linear logic connectives can be residuated, linear logic with '!' can be displayed and hence its cut-elimination stuff is working — is my understanding correct?

### Yes, Essentially Correct!

Your understanding is on the right track. Let me refine it:

### The Two Tools

 | Tool                      | Used For                                       | Example   |
 | ------                    | ----------                                     | --------- |
 | **Residuation**           | Binary connectives with "implication" partners | ⊗ ↔ ⊸     |
 | **Adjoint decomposition** | Mode-changing connectives (not residuated)     | ! = F ∘ G |

### How Linear Logic Gets Displayed

**Multiplicative connectives (⊗, ⅋, ⊸):**
- These ARE residuated
- Standard display postulates work
- Cut elimination via Belnap's conditions

**Exponentials (!, ?):**
- NOT residuated in the standard sense
- BUT can be decomposed into adjoint pairs
- Multi-type display calculus handles them
- Cut elimination still works!

### The Key Insight

**Greco & Palmigiano's contribution:**

They showed that even though ! breaks standard residuation:
1. Decompose ! into F ∘ G (two adjoint functors)
2. F and G individually have "good" behavior (they're normal modal operators)
3. The composition inherits enough structure for cut elimination

So: **Residuation OR Adjoint decomposition → Display property → Cut elimination**

### A Subtlety

The "Linear Logic Properly Displayed" paper achieves **proper** display calculi, meaning:
- Rules closed under uniform substitution
- No ad-hoc exceptions
- The smoothest possible cut elimination proof

Earlier attempts (Belnap's original, others) had to "cheat" a bit with exponentials. Greco & Palmigiano fixed this.

---

## 11. Global Side Conditions: Can We Work With Them?

**Your question:** There is no way to work with global side conditions?! What else are they used for? What can they be useful for? Why are they difficult to work with — just because they can't be displayed easily?

### Can We Work With Global Side Conditions?

**Yes, but it's harder!**

Global side conditions are used in many sequent calculi. They work, but they break certain nice properties.

### What Global Side Conditions Are Used For

**1. Modal Logics (S5, etc.):**
```
  □Γ ⊢ A
  ───────── □R (S5)
  □Γ ⊢ □A
```
Side condition: "all of Γ must be boxed"

**2. Exponentials in Linear Logic:**
```
  ?Γ ⊢ A
  ───────── !R
  ?Γ ⊢ !A
```
Side condition: "all of Γ must be why-not"

**3. Eigenvariable Conditions (First-Order Logic):**
```
  Γ ⊢ A[y/x]
  ─────────── ∀R
  Γ ⊢ ∀x.A
```
Side condition: "y must not appear free in Γ or ∀x.A"

**4. Freshness Conditions (Nominal Logic, Pi-Calculus):**
```
Rules that require certain names to be "fresh" w.r.t. the context
```

**5. Type-Checking (Dependent Types):**
```
Side conditions about well-formedness of types in context
```

### Why They're Difficult

**1. Break locality:**

> "In standard sequent calculus, rules should be local — you should be able to apply a rule by looking only at the principal formula."

Global conditions require inspecting the WHOLE context.

**2. Complicate cut elimination:**

Cut elimination proofs become "ad-hoc" — you need to verify each logic separately, rather than using Belnap's generic theorem.

> "The usual structural proof theory of modal logic in Gentzen systems is described as ad-hoc. Formalisation arises through system-by-system fine tuning."

**3. Make proof search harder:**

You can't just decompose the goal; you need to track invariants about the entire proof state.

**4. Break display property:**

You CAN'T display a formula if moving it would violate the side condition!

```
□A, B ⊢ C     (B is not boxed)
─────────── (can't display A, would need to move B)
    ???
```

### Solutions

 | Approach              | How It Handles Side Conditions                        |
 | ----------            | -------------------------------                       |
 | **Labelled sequents** | Conditions become local label checks                  |
 | **Hypersequents**     | Conditions become structural rules between components |
 | **Multi-type**        | Conditions become type distinctions                   |
 | **Deep inference**    | Rules apply anywhere, avoiding some issues            |

### Are Side Conditions Ever Useful?

**Yes!** For practical systems:

- They keep the language **simple** (no extra structural machinery)
- They're **intuitive** (match how mathematicians think)
- They work fine for **checking** proofs (just verify conditions)

The problems arise mainly for:
- **Proof search** (need to guess/track)
- **Meta-theory** (ad-hoc cut elimination)
- **Modularity** (can't easily add connectives)

---

## 12. What Makes a Connective "Structural" vs "Logical"?

> **See also:** [[residuation]] and [[display-calculus]] for the formal treatment.

**Your question:** What makes a connective 'structural' and what makes it 'logical'? Why is `,` (comma) structural counterpart of ⊗ (tensor)? What is structural meaning here? How does this relate to Galois connection? What is a structural negation?

### The Fundamental Distinction

**Logical connectives:** Appear in FORMULAS (things we prove)
- Examples: ⊗, ⊸, ∧, →, !, □

**Structural connectives:** Appear in STRUCTURES (ways of combining formulas in sequents)
- Examples: , (comma), ; (semicolon), > , *

### Why the Distinction Exists

In a sequent `A, B ⊢ C`:
- `A`, `B`, `C` are **formulas** with logical connectives
- The **comma** is NOT a logical connective — it's how we combine formulas in the context

### The Comma IS NOT Conjunction!

**Subtle point:**

In `A, B ⊢ C`, the comma BEHAVES like conjunction (we have both A and B), but:

1. It's at a **different level** (structure, not formula)
2. It has **different rules** (structural rules, not logical rules)
3. It **doesn't appear in conclusions** (you don't prove `A, B`)

### Why Comma is "Counterpart" of Tensor

**Residuation connects them:**

| Structural | Logical |
|------------|---------|
| X , Y ⊢ Z | A ⊗ B ⊢ C |
| X ⊢ Y > Z | A ⊢ B ⊸ C |

The structural comma (,) and structural implication (>) have the SAME residuation relationship as the logical tensor (⊗) and lolli (⊸).

**The mapping:**
- Comma (,) ↔ Tensor (⊗)
- Structural implication (>) ↔ Lolli (⊸)
- Structural unit (I) ↔ Logical unit (1)

### How This Relates to Galois Connections

Each structural connective has a "meaning" via residuation:

```
X , Y ⊢ Z   iff   X ⊢ Y > Z
```

This IS a Galois connection! For each fixed X:
- f(Y) = X , Y (comma with X)
- g(Z) = X > Z (would be, but actually it's Y > Z)

The structural connectives form a **residuated algebra** that mirrors the logical connectives.

### What is Structural Negation?

**Structural negation (*)** handles the swap between antecedent and succedent:

```
X ⊢ Y   iff   *Y ⊢ *X
```

**Why it's needed:**

In classical logic, negation swaps sides:
- To prove ¬A, assume A and derive contradiction
- A ⊢ B is equivalent to ⊢ ¬A ∨ B

The structural * captures this "side-swapping" at the structure level.

**Example:**
```
A ⊢ B
─────── (structural negation)
*B ⊢ *A
```

If * is "classical", then *A ≈ ¬A at the formula level.

### Summary Table

 | Structural    | Logical Counterpart  | Residuation          |
 | ------------  | -------------------- | ------------         |
 | , (comma)     | ⊗ (tensor)           | , is residuated by > |
 | ; (semicolon) | ⅋ (par)              | ; is residuated by < |
 | >             | ⊸ (lolli)            | residual of ,        |
 | *             | ¬ (negation)         | involutive: **X = X  |
 | I             | 1 (unit)             | identity for ,       |

---

## 13. Why Doesn't Bang Have Residuals? (Detailed Explanation)

> **See also:** [[exponential-display-problem]] for the formal analysis.

**Your question:** In the rule `!A ⊗ B ⊢ C iff !A ⊢ B ⊸ C` — do you mean `!(A ⊗ B) ⊢ C` or `(!A) ⊗ B ⊢ C`? Why is duplication a problem? What makes structural rules for ! "unsound"?

### Clarification: `(!A) ⊗ B ⊢ C`

I meant `(!A) ⊗ B ⊢ C` — bang applied to A, then tensored with B.

### The Hypothetical Residuation

**IF** ! were residuated like ⊗, we'd have something like:

```
!A ⊗ B ⊢ C   iff   !A ⊢ B ⊸ C   iff   B ⊢ ???(!A ⊸ C)
```

But what would ??? be? There's no natural "dual" operation.

### Why Duplication is The Problem

**The key rules of !:**

```
!A ⊢ A           (dereliction: can use !A as A)
!A ⊢ !A ⊗ !A     (contraction: can duplicate !A)
!A ⊢ 1           (weakening: can discard !A)
```

**Now consider:**

```
!A ⊗ B ⊢ C
```

If we could move !A to the right freely (like with ⊗), we'd get:

```
!A ⊢ B ⊸ C
```

But now suppose we have TWO copies of !A via contraction:

```
!A ⊢ !A ⊗ !A    (contraction)
!A ⊗ !A ⊗ B ⊢ C  (use both)
```

If we move one !A right:
```
!A ⊢ (!A ⊗ B) ⊸ C
```

But we STILL have !A on the left! The "residual" doesn't fully capture what !A contributes.

### What "Unsound" Means

**Unsound = proves false things**

If we added structural rules for ! like:

```
!X , Y ⊢ Z
───────────── (hypothetical display postulate)
!X ⊢ Y > Z
```

Then we could prove things that SHOULDN'T be provable.

**Concrete example of why it breaks:**

1. Start with: `!A ⊢ !A ⊗ !A` (valid by contraction)
2. Apply hypothetical display postulate: `!A ⊢ !A > (!A ⊗ !A)`
3. This says: "from one !A, I can get (!A ⊸ (!A ⊗ !A))"
4. But `!A ⊸ (!A ⊗ !A)` means "consuming one !A gives me two !A"
5. Combined with dereliction, this would let us create resources from nothing!

**The issue:** The structural rules for ! would "forget" that contraction was used, making it seem like we can create unlimited resources.

### The Categorical Explanation

**! is a comonad, not a residuated operation.**

A **comonad** has:
- **Counit (ε):** !A → A (dereliction)
- **Comultiplication (δ):** !A → !!A (promotion)

These satisfy:
```
ε ∘ δ = id
!ε ∘ δ = id
δ ∘ δ = !δ ∘ δ
```

This is a DIFFERENT algebraic structure than residuation. You can't express comonad laws using just residuation.

### The Solution: Adjoint Decomposition

Instead of trying to residuate !, we DECOMPOSE it:

```
! = F ∘ G

F : Cartesian → Linear    (left adjoint, "forget linearity")
G : Linear → Cartesian    (right adjoint, "promote to unlimited")
```

Now F and G individually have nice behavior:
- F(X) ⊢ Y iff X ⊢ G(Y) (adjunction, not residuation)
- F preserves structure one way
- G preserves structure the other way

And ! = F ∘ G inherits enough structure for cut elimination!

---

*Last updated: 2026-02-10*
