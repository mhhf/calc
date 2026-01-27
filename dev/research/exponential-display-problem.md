# Why Exponentials Break Display Calculus

A rigorous explanation of why the linear logic exponential (!) cannot have a display postulate, and how the problem is solved.

---

## Table of Contents

1. [The Display Property Requirement](#the-display-property-requirement)
2. [What a Display Postulate for ! Would Need](#what-a-display-postulate-would-need)
3. [The Impossibility Proof](#the-impossibility-proof)
4. [Why No Such f Can Exist](#why-no-such-f-can-exist)
5. [Can We Introduce a New Connective?](#can-we-introduce-a-new-connective)
6. [The Solution: Multi-Type Systems](#the-solution)
7. [Summary](#summary)

---

## The Display Property Requirement

### What is the Display Property?

In display calculus, we want to be able to **isolate any substructure** on one side of the sequent. This is called the **display property**.

For example, in `(A , B) , C ⊢ D`, we should be able to isolate A:
```
(A , B) , C ⊢ D
─────────────────  (rearrange using display postulates)
A ⊢ ...something...
```

### Display Postulates Enable This

To move structures around, we use **display postulates** — structural rules that transform sequents while preserving provability.

For the comma (,), the display postulate is:
```
X , Y ⊢ Z   iff   X ⊢ Y > Z
```

**Critical requirement:** This must be a **bidirectional equivalence**. Both directions must preserve provability:
- If `X , Y ⊢ Z` is provable, then `X ⊢ Y > Z` is provable
- If `X ⊢ Y > Z` is provable, then `X , Y ⊢ Z` is provable

### Where Do Display Postulates Come From?

Display postulates mirror **logical residuation**:

| Level | Equivalence |
|-------|-------------|
| Logical | `A ⊗ B ⊢ C iff A ⊢ B ⊸ C` |
| Structural | `X , Y ⊢ Z iff X ⊢ Y > Z` |

The structural comma (,) corresponds to ⊗. The structural implication (>) corresponds to ⊸.

Because the logical equivalence is provable in both directions, the structural equivalence is **sound**.

---

## What a Display Postulate for ! Would Need

### The General Form

For a unary structural connective !_s (corresponding to !), a display postulate would have the form:

```
!A ⊢ B   iff   A ⊢ f(B)
```

for some function f on formulas.

**This is the general requirement.** Any display postulate for ! must fit this pattern for some choice of f.

### Why This Form?

To display something inside !_s X, we need to "remove" or "move" the !_s. The only way to do this while preserving the sequent structure is to transform `!_s X ⊢ Y` into `X ⊢ f(Y)` for some f.

---

## The Impossibility Proof

**Theorem:** There is no function f such that `!A ⊢ B iff A ⊢ f(B)` is sound for all formulas A and B.

**Proof:**

**Step 1.** Let p be a propositional variable (atomic formula).

**Step 2.** By the contraction rule for !:
```
!p ⊢ !p ⊗ !p   is PROVABLE
```

**Step 3.** Suppose there exists f making `!A ⊢ B iff A ⊢ f(B)` sound.

**Step 4.** By the forward direction of the equivalence:
```
p ⊢ f(!p ⊗ !p)   must be PROVABLE
```

**Step 5.** We analyze what `p ⊢ X` can prove. Since p is atomic:
- `p ⊢ p` is provable (identity)
- `p ⊢ Y` for other Y requires deriving Y from p

**Step 6.** To derive any formula containing ! on the right, we need the **promotion rule**:
```
!Γ ⊢ A
─────────  (promotion)
!Γ ⊢ !A
```
This requires the **entire left side** to be !-marked.

**Step 7.** We have only `p` on the left, not `!p`. Promotion does not apply.

**Step 8.** There is **no rule** that derives a !-containing formula on the right from a plain formula on the left.

**Step 9.** Therefore, for any f:
- If f(!p ⊗ !p) contains !, it's not provable from p
- If f(!p ⊗ !p) removes all !'s, say f(!p ⊗ !p) = p ⊗ p, then `p ⊢ p ⊗ p` is not provable (we have one p, need two)

**Step 10.** No matter what f is, `p ⊢ f(!p ⊗ !p)` is **NOT provable**.

**Step 11.** But `!p ⊢ !p ⊗ !p` IS provable.

**Step 12.** Contradiction. The equivalence `!A ⊢ B iff A ⊢ f(B)` derives an unprovable sequent from a provable one.

**Conclusion:** No such f exists. **QED**

---

## Why No Such f Can Exist

The proof above shows no f works, but let's understand **why** at a deeper level.

### The Asymmetry of !

The rules for ! are:

| Rule | Sequent | What it does |
|------|---------|--------------|
| Dereliction | `!A ⊢ A` | Removes ! (uses the resource once) |
| Contraction | `!A ⊢ !A ⊗ !A` | Duplicates ! |
| Weakening | Context: `Γ ⊢ Δ` implies `Γ, !A ⊢ Δ` | Discards ! |
| Promotion | `!Γ ⊢ A` implies `!Γ ⊢ !A` | Adds ! (requires !-marked context) |

**Key observation:** The first three rules go **from !A to something**. But promotion goes the other way **only under special conditions** (the context must be all !-marked).

This asymmetry means: **!A can prove things that A cannot prove.**

Specifically: `!A ⊢ !A ⊗ !A` but `A ⊬ anything involving !`

### The Core Issue

A display postulate `!A ⊢ B iff A ⊢ f(B)` would require A and !A to have **equivalent proving power** (modulo f). But they don't:

- !A can prove `!A ⊗ !A` (contraction)
- A cannot prove anything with ! in it (no applicable rule)

No f can bridge this gap.

---

## Can We Introduce a New Connective?

**Question:** Can we define a new connective f with rules that make `A ⊢ f(B)` provable whenever `!A ⊢ B` is provable?

### Attempt: Define f by What ! Does

We could try adding rules:
```
─────────── (f-intro from dereliction)
A ⊢ f(A)

─────────────────── (f-intro from contraction)
A ⊢ f(!A ⊗ !A)

─────────── (f-intro from weakening)
A ⊢ f(I)
```

**Problem 1: Circularity.** These rules are defined by what ! can prove. The connective f has no independent meaning — it's just encoding "!A ⊢ B" in syntax.

**Problem 2: The backward direction.** The display postulate must go both ways:
- Forward: `!A ⊢ B` implies `A ⊢ f(B)` ✓ (we designed f for this)
- Backward: `A ⊢ f(B)` implies `!A ⊢ B` ← **Dangerous!**

If someone derives `A ⊢ f(C)` through some chain of reasoning where `!A ⊢ C` is NOT provable, the backward direction would derive a false sequent. The system becomes **unsound** or loses **cut elimination**.

**Problem 3: Collapsing the distinction.** The whole point of linear logic is:
- A = linear resource (use exactly once)
- !A = unlimited resource (use any number of times)

If `A ⊢ f(B) iff !A ⊢ B`, then A and !A become interchangeable in proving power. This **collapses the linear/non-linear distinction** — destroying what makes linear logic meaningful.

### Conclusion

Within linear logic, no connective f can make the display postulate work without breaking the logic.

---

## The Solution: Multi-Type Systems

The key insight: **f does exist, but in an extended system with two types**.

### Benton's LNL (Linear/Non-Linear) Logic

Instead of one logic, we have two:

```
┌─────────────────┐         ┌─────────────────┐
│  LINEAR WORLD   │         │ CARTESIAN WORLD │
│                 │         │                 │
│  Resources used │   F,G   │  Values can be  │
│  exactly once   │ ←─────→ │  copied/dropped │
│                 │         │                 │
└─────────────────┘         └─────────────────┘
```

Two functors connect them:
- **F**: Cartesian → Linear (embeds Cartesian values into Linear)
- **G**: Linear → Cartesian (extracts reusable part from Linear)

### The Adjunction

F and G form an **adjunction** F ⊣ G:

```
F(X) ⊢_Linear Y   iff   X ⊢_Cartesian G(Y)
```

This IS a bidirectional equivalence! But between **different type systems**.

### Decomposing !

The exponential decomposes as:

```
!A = F(G(A))
```

- G(A) extracts the "reusable content" of A (moves to Cartesian world)
- F(G(A)) embeds it back into Linear world as an unlimited resource

### Why This Works

The adjunction provides bidirectionality **without collapsing the distinction**:
- Linear and Cartesian are **separate worlds**
- F and G are **bridges** between them
- The ! is not a primitive — it's a **round trip** through Cartesian

This is exactly what **multi-type display calculus** (Greco & Palmigiano, 2023) formalizes.

---

## Summary

### The Problem

| Requirement | Status |
|-------------|--------|
| Display postulate must be bidirectional | Required for cut elimination |
| Need `!A ⊢ B iff A ⊢ f(B)` for some f | General form for unary connective |
| Such f must exist | **IMPOSSIBLE** (proof above) |

### Why It's Impossible

1. Display postulate requires `!A ⊢ B iff A ⊢ f(B)` for some f
2. Contraction gives `!p ⊢ !p ⊗ !p` (provable)
3. So `p ⊢ f(!p ⊗ !p)` must be provable
4. But p cannot prove anything with ! (promotion requires !-marked context)
5. No f makes `p ⊢ f(!p ⊗ !p)` provable
6. Contradiction: no such f exists

### Why We Can't Just Add f

- Rules for f would be circular (defined by !'s provability)
- Backward direction would break soundness
- Would collapse linear/non-linear distinction

### The Solution

Extend to multi-type system:
- Two worlds: Linear and Cartesian
- Adjoint functors F ⊣ G connecting them
- Decompose ! = F ∘ G
- Adjunction provides bidirectional equivalence **across types**

---

## Sources

- [Linear Logic Properly Displayed (Greco & Palmigiano, 2023)](https://dl.acm.org/doi/10.1145/3570919) — The state-of-the-art proper display calculus for linear logic with exponentials
- [A Mixed Linear and Non-Linear Logic (Benton, 1994)](https://link.springer.com/chapter/10.1007/BFb0022251) — Original LNL paper showing ! = F ∘ G decomposition
- [Linear Logic (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-linear/)
- [Pfenning's 15-836 Lecture 10: Mixed Linear/Nonlinear](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/10-mixed.pdf)
- Belnap, N.D. (1982). Display Logic. Journal of Philosophical Logic, 11, 375-417.

## Cross-References

See also in this knowledge base:
- [[residuation]] — Why residuation is needed for display postulates
- [[QnA]] — Detailed Q&A on structural vs logical connectives
- [[logics-overview]] — Which logics can be displayed
- [[ANKI]] — Flashcards on LNL and multi-type display

---

*Last updated: 2026-01-27*
