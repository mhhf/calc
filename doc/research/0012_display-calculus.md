---
title: "Display Calculus: Deep Research"
created: 2026-02-10
modified: 2026-02-10
summary: Evaluation of Belnap's display calculus versus alternatives including focused sequent calculus and proof nets for CALC's multimodal linear logic goals.
tags: [display-calculus, sequent-calculus, proof-theory, Belnap, architecture]
category: "Proof Theory"
---

# Display Calculus: Deep Research

This document investigates whether display calculus is the right choice for this project, compares it with alternatives, and provides recommendations for the architecture going forward.

> **See also:** [[proof-calculi-foundations]] for hierarchy of proof formalisms, [[residuation]] for adjunction/residuation principles, [[multi-type-display-calculus]] for Greco & Palmigiano's MTDC approach, [[exponential-display-problem]] for the ! problem.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [What is Display Calculus?](#what-is-display-calculus)
3. [The Display Property](#the-display-property)
4. [Belnap's Conditions for Cut Elimination](#belnaps-conditions-for-cut-elimination)
5. [Structural Connectives and Residuation](#structural-connectives-and-residuation)
6. [Alternative Proof Calculi](#alternative-proof-calculi)
7. [Comparison Matrix](#comparison-matrix)
8. [Analysis of Current Implementation](#analysis-of-current-implementation)
9. [Recommendations](#recommendations)
10. [Sources](#sources)

---

## Executive Summary

**Key Finding:** The current implementation is a **hybrid** between display calculus structure (from calculus-toolbox) and focused proof search (Andreoli-style). This hybrid may be introducing unnecessary complexity.

**The Core Question:** Is display calculus the right foundation for our goals (quantitative types, multimodalities, accounting applications)?

**Short Answer:** Probably not in its pure form. For our use cases:
- **Focused sequent calculus** (like Celf/CLF) would be simpler and more efficient for proof search
- **Proof nets** would be more elegant for the pure linear logic fragment
- **Display calculus** shines for modal extensions, which we *do* want for multimodalities

**Recommendation:** Evolve toward a **focused sequent calculus** core with display-style structural rules only where needed for modal/multimodal extensions. This is essentially what the current implementation already does in `proofstate.js`, but the `ll.json` structure carries unused display machinery.

---

## What is Display Calculus?

Display calculus was introduced by **Nuel Belnap in 1982** as a generalization of Gentzen's sequent calculus. The key innovations are:

### 1. Structural Connectives

In standard sequent calculus, sequents have the form:
```
A₁, A₂, ..., Aₙ ⊢ B₁, B₂, ..., Bₘ
```

In display calculus, structures on each side can be built using **structural connectives** that mirror logical connectives:

```
X ; Y ⊢ Z        (structural conjunction/comma)
X ⊢ Y ; Z        (structural disjunction)
X > Y ⊢ Z        (structural implication antecedent)
I ⊢ X            (structural unit)
```

### 2. Display Postulates

Rules that allow "shuffling" structures around without changing provability:

```
X ; Y ⊢ Z          X ⊢ Y ; Z
─────────────  ↔  ─────────────   (residuation)
X ⊢ Y > Z          X ; Y ⊢ Z
```

### 3. Separation of Concerns

- **Structural rules**: manipulate structure (associativity, commutativity, exchange)
- **Logical rules**: introduce/eliminate logical connectives
- **Display postulates**: move formulas to "displayable" position

### Why was it invented?

Standard sequent calculus struggles with:
- Modal logics (need to track accessibility relations)
- Substructural logics (need fine control over structural rules)
- Non-classical logics generally

Display calculus provides a **uniform framework** where:
1. Cut elimination is guaranteed if 8 syntactic conditions are met
2. New logics can be defined by adding rules modularly
3. The "display property" ensures any formula can be made principal

---

## The Display Property

**Definition:** A calculus has the display property if for any sequent `X ⊢ Y` and any formula occurrence `A` within it, there exists a sequent `A ⊢ Z` or `W ⊢ A` (depending on polarity) that is **inter-derivable** with the original using only display postulates.

**Example:** Given `(A, B), C ⊢ D`, we can display `B` as:
```
(A, B), C ⊢ D
─────────────── (associativity)
A, (B, C) ⊢ D
─────────────── (residuation)
B, C ⊢ A > D
─────────────── (associativity)
B ⊢ C > (A > D)
```

**Why it matters:**
- Enables a generic cut-elimination proof
- Makes the calculus modular (add rules without breaking cut-elim)
- But: display postulates can **blow up proof search space**

---

## Belnap's Conditions for Cut Elimination

Belnap proved that ANY display calculus satisfying 8 syntactic conditions (C1-C8) admits cut elimination. The conditions include:

1. **C1 (Preservation of formulas):** Each formula in the premise of a rule is a subformula of some formula in the conclusion
2. **C2 (Shape-alikeness):** Congruent parameters in premises/conclusion
3. **C3 (Non-proliferation):** Principal formula appears exactly once in conclusion
4. **C4 (Position-alikeness):** Parameters in same position across premises
5. **C5 (Display of principal):** Principal formula is always displayable
6. **C6 (Closure under substitution):** Rules closed under uniform substitution
7. **C7 (Eliminability of matching principal):** Cuts on matching principals can be reduced
8. **C8 (Cut reduction preserves structure):** Cut reduction doesn't create new structure

**Practical implication:** If you define a calculus following these conditions, you get cut-elimination "for free" - no need to prove it manually. This is the main appeal of display calculus for logic designers.

---

## Structural Connectives and Residuation

### Residuation Principle

Display calculus requires that logical connectives come in **residuated pairs**. If we have a binary connective `⊗`, there should be connectives `⊸` and `−` such that:

```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C   iff   B ⊢ A − C
```

This is the **Galois connection** / **adjunction** pattern from category theory.

### In Linear Logic

| Connective | Residuation Property |
|------------|---------------------|
| ⊗ (tensor) | `A ⊗ B ⊢ C` iff `A ⊢ B ⊸ C` iff `B ⊢ A −○ C` |
| ⅋ (par)    | De Morgan dual of tensor: `A ⅋ B = (A⊥ ⊗ B⊥)⊥` |

Note: Tensor and par are **De Morgan duals of each other**, not self-dual. The lollipop (⊸) is the residual of tensor: `A ⊸ B = A⊥ ⅋ B`.

### Structural Counterparts

In display calculus, we have structural connectives mirroring these:

| Structural | Logical | Meaning |
|------------|---------|---------|
| X , Y      | A ⊗ B   | Both resources together |
| X > Y      | A ⊸ B   | If X then Y (hypothetical) |
| I          | 1       | Empty resource |

---

## Alternative Proof Calculi

### 1. Standard (Focused) Sequent Calculus

**What it is:** Gentzen's original sequent calculus, optionally with Andreoli's focusing discipline.

**Structure:**
```
Γ ; Δ ⊢ A
```
Where Γ is unrestricted context, Δ is linear context, A is goal.

**Used by:** Celf, Twelf, most logic programming implementations.

**Pros:**
- Simple, well-understood
- Focusing makes proof search tractable
- Direct correspondence to functional programs
- Efficient implementation

**Cons:**
- Doesn't scale well to modal logics
- Cut-elimination must be proven per-logic
- Less modular than display calculus

### 2. Proof Nets

**What it is:** Graphical representation of proofs that eliminates "bureaucratic" differences between sequent proofs.

**Structure:** Directed graphs with:
- Formula nodes
- Link nodes (for connectives)
- Correctness criterion (no cycles of certain types)

**Used by:** Theoretical linear logic, some implementations.

**Pros:**
- Canonical representation (no spurious proof differences)
- Cut elimination is local graph rewriting
- Linear time cut elimination for MLL
- Natural for parallel/concurrent interpretations
- Connection to quantum circuits

**Cons:**
- Harder to implement
- Correctness criterion is subtle (especially for exponentials)
- Less intuitive for beginners
- Not great for proof search (more for proof representation)

### 3. Deep Inference / Calculus of Structures

**What it is:** Proof calculus where inference rules can apply **anywhere** inside a formula/structure, not just at the root.

**Structure:**
```
S{A}        (structure S with hole filled by A)
─────
S{B}        (replace A with B anywhere in S)
```

**Key feature:** No sequent arrow - just structures being rewritten.

**Used by:** BV logic, some linear logic formalizations.

**Pros:**
- All rules are local (bounded effort to apply)
- Contraction/weakening reducible to atomic form
- Simpler cut elimination
- Can express connectives that sequent calculus cannot (e.g., BV's "seq")

**Cons:**
- Less familiar
- Proof search less studied
- Harder to relate to programming

### 4. Hypersequent Calculus

**What it is:** Sequents of sequents - a multiset of ordinary sequents.

**Structure:**
```
Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ... | Γₙ ⊢ Δₙ
```

Read as: "at least one of these sequents is provable."

**Used by:** S5 modal logic, intermediate logics.

**Pros:**
- Simpler than display calculus
- Good for certain modal logics (S5)
- Established methodology

**Cons:**
- Less expressive than display calculus
- Can be embedded into display calculus (display subsumes hypersequents)

### 5. Nested Sequent Calculus

**What it is:** Sequents containing sequents recursively (trees of sequents).

**Structure:**
```
Γ ⊢ Δ, [Γ' ⊢ Δ']
```

**Used by:** Modal logics, tense logics.

**Pros:**
- More expressive than hypersequents
- Fewer structural rules than display calculus
- Deep inference variant eliminates display postulates entirely

**Cons:**
- More complex than standard sequents
- Cut elimination proofs more involved

### 6. Labelled Sequent Calculus

**What it is:** Sequent calculus with explicit labels (worlds/states) and accessibility relations.

**Structure:**
```
w : A, wRv, v : B ⊢ w : C
```

**Used by:** Modal logic implementations, semantic tableaux.

**Pros:**
- Very expressive
- Direct connection to Kripke semantics
- Can handle almost any modal logic

**Cons:**
- "External" - labels are not part of the logic's language
- Can lose subformula property
- Proof search involves relation reasoning

---

## Comparison Matrix

| Criterion | Display | Focused Sequent | Proof Nets | Deep Inference | Nested |
|-----------|---------|-----------------|------------|----------------|--------|
| **Simplicity** | Low | High | Medium | Medium | Medium |
| **Proof Search Efficiency** | Low | High | N/A* | Medium | Medium |
| **Cut Elimination** | Generic | Per-logic | Elegant | Simple | Similar to display |
| **Modal Extensions** | Excellent | Poor | Poor | Good | Good |
| **Linear Logic** | Good | Excellent | Excellent | Good | Good |
| **Implementation Effort** | High | Low | High | Medium | Medium |
| **Multimodalities** | Excellent | Poor | Poor | Unknown | Good |
| **Canonical Proofs** | No | With focusing | Yes | Partial | No |

*Proof nets are for proof representation, not search.

---

## Analysis of Current Implementation

### What `ll.json` Defines

Looking at the current `ll.json`, we see display calculus structure:

**Structural Rules (RuleStruct):**
```json
"P_L": ["(?X1, ?X2), (?Y1, ?Y2) |- ?Z", "(?X1, ?Y1), (?X2, ?Y2) |- ?Z"],  // permutation
"A_L": ["?Y1, (?Y2, ?Y3) |- ?X", "(?Y1, ?Y2), ?Y3 |- ?X"],                // associativity
"I_L_L": ["?X |- ?Y", "I, ?X |- ?Y"],                                     // unit introduction
```

These are display postulates for a commutative, associative structure with unit.

**Logical Rules:**
```json
"Tensor_L": ["?X, -- : F?A * F?B |- -- : F?C", "?X, (-- : F?A, -- : F?B) |- -- : F?C"],
"Loli_R":   ["?X |- -- : F?A -o F?B", "?X, -- : F?A |- -- : F?B"],
```

These follow display calculus pattern - structural comma mirrors tensor.

### What `proofstate.js` Actually Does

The proof search in `proofstate.js` does **NOT** use display postulates for proof search. Instead, it uses:

1. **Focusing** (Andreoli-style): Inversion phase → Focus phase → Identity
2. **Direct multiset manipulation**: `linear_ctx` is treated as a multiset, not a structured term
3. **Pattern matching on rules**: Rules are applied by matching, not by display

**Key observation:** The display calculus structure in `ll.json` is largely **unused** by the actual proof search. The structural rules (P_L, A_L, etc.) are defined but the prover works directly with multisets.

### The Hybrid Nature

The system is a hybrid:
- **Data model**: Display calculus (structured terms, structural connectives)
- **Proof search**: Focused sequent calculus (multisets, focusing phases)
- **Rules**: Written in display style but applied differently

This hybrid introduces:
1. **Complexity**: Two models to understand
2. **Mismatch**: Rules written for display but used differently
3. **Unused machinery**: Structural rules mostly unused

---

## Recommendations

### For Current Goals

Given our goals (quantitative types, multimodalities, accounting):

#### 1. Short-term: Clarify the Hybrid

- Document what parts of display calculus are actually used
- Remove or mark as experimental the unused structural rules
- Make `proofstate.js` the source of truth for proof search

#### 2. Medium-term: Decide on Direction

**Option A: Embrace Display Calculus**
- If multimodalities are critical, display calculus is good
- Would need to actually use display postulates in proof search
- Higher implementation complexity
- Better for modal extensions

**Option B: Simplify to Focused Sequent Calculus**
- Follow Celf/CLF model
- Simpler implementation
- Better proof search performance
- Add modal extensions via labelled approach if needed

**Option C: Keep Hybrid but Clean Up**
- Keep display-style rule definitions (good for Isabelle export)
- Keep focused proof search (good for efficiency)
- Just clean up the unused parts

#### 3. Long-term: Consider Proof Nets

For the pure linear logic fragment, proof nets offer:
- Canonical proof representation
- Connection to quantum semantics (relevant to research goals)
- Elegant cut elimination

But proof nets are harder to extend with modalities.

### Specific Recommendations

| Goal | Recommended Approach |
|------|---------------------|
| Quantitative types (semiring grading) | Focused sequent calculus - just add coefficients to contexts |
| Multimodalities (ownership) | Display or nested sequent calculus - need structural control |
| Proof search efficiency | Focused sequent calculus - proven efficient |
| Isabelle formalization | Keep display-style rules - good for Isabelle export |
| Quantum semantics research | Consider proof nets for the MLL fragment |

### Decision Checklist

Before major refactoring, answer:

1. **How important are multimodalities?**
   - Critical → Keep display calculus infrastructure
   - Nice-to-have → Simplify to focused sequent calculus

2. **Is Isabelle export important?**
   - Yes → Keep display-style rule definitions
   - No → Can simplify rule format

3. **Is proof search performance critical?**
   - Yes → Ensure focused approach, avoid display postulates in search
   - No → Display postulates are fine

4. **Do we want canonical proof representation?**
   - Yes → Consider proof nets
   - No → Sequent-based is fine

---

---

## Additional Clarifications

### Display Calculus vs Focusing: Orthogonal Concepts

Display calculus and focusing are **orthogonal** - they solve different problems and can be combined:

| Concept | What it is | What it solves |
|---------|-----------|----------------|
| **Display Calculus** | Proof formalism (shape of sequents) | Modularity, modal extensions, generic cut-elimination |
| **Focusing** | Proof search strategy | Efficiency, reducing non-determinism |

**Combinations:**
- Display calculus WITHOUT focusing: works but inefficient proof search
- Focused sequent calculus WITHOUT display: standard Celf/CLF approach
- **Focused display calculus**: best of both worlds (see [arXiv:2011.02895](https://arxiv.org/abs/2011.02895))

### Why Display Calculus Handles Modalities Well

Modal operators need to track "scope" - what formulas are accessible from where.

**Problem in standard sequent calculus:** The comma (,) has fixed meaning. You can't express "this formula is in modal scope" vs "this formula is outside."

**Solution in display calculus:** Structural connectives mirror modal operators:
```
•X ⊢ Y     -- structural connective • indicates "inside modality"
```

Display postulates let you move formulas in/out of modal scope:
```
•X ⊢ Y          X ⊢ ◇Y
─────────  ↔   ─────────
X ⊢ ◇Y          •X ⊢ Y
```

For **multimodalities** (your goal), you need different structural operators for different modes:
```
[Alice]X , [Bob]Y ⊢ Z
```

This fits naturally in display calculus or labelled sequent calculus.

### Terminology Guide

| Term | Definition |
|------|------------|
| **Proof calculus / Proof system** | Formal system for constructing proofs (axioms + rules). Synonymous. |
| **Proof formalism** | The "shape" of judgments (sequents, hypersequents, nested sequents, proof nets) |
| **Proof search strategy** | How you search for proofs (focusing, tableaux, resolution) |
| **Proof representation** | How you represent completed proofs (trees, nets, lambda terms) |
| **Canonical proof** | A unique representative for each equivalence class of "essentially same" proofs |

### Approaches for Multimodal Quantitative Linear Types

Given the goal of multimodal quantitative linear types (exploration phase):

| Approach | Viability | Complexity | Notes |
|----------|-----------|------------|-------|
| **Focused Display Calculus** | Excellent | High | Best of both worlds |
| **Labelled Sequent Calculus** | Excellent | Medium | Most flexible for modalities |
| **Nested Sequent Calculus** | Good | Medium | Good balance |
| **Standard Focused + Subexponentials** | Good | Medium | CLF approach |
| **Display Calculus (unfocused)** | Possible | High | Current approach |
| **Deep Inference** | Unknown | High | Less studied for this |
| **Proof Nets** | Hard | Very High | Research frontier |

---

## Sources

### Primary References

- [Structural proof theory - Wikipedia (Display Logic)](https://en.wikipedia.org/wiki/Display_logic)
- [Hypersequent and Display Calculi – a Unified Perspective (Ciabattoni et al., Studia Logica 2014)](https://link.springer.com/article/10.1007/s11225-014-9566-z)
- [Display calculi and other modal calculi: a comparison (Synthese 2008)](https://link.springer.com/article/10.1007/s11229-008-9425-4)
- [Linear Logic Properly Displayed (ACM TOCL)](https://dl.acm.org/doi/10.1145/3570919)

### Proof Nets

- [Proof net - Wikipedia](https://en.wikipedia.org/wiki/Proof_net)
- [Linear Logic (Stanford Encyclopedia of Philosophy)](https://plato.stanford.edu/entries/logic-linear/)
- [proof net in nLab](https://ncatlab.org/nlab/show/proof+net)

### Deep Inference

- [Deep Inference - Alessio Guglielmi](http://alessio.guglielmi.name/res/cos/)
- [Calculus of structures - Wikipedia](https://en.wikipedia.org/wiki/Calculus_of_structures)
- [Deep Inference and the Calculus of Structures Linear Logic](http://alessio.guglielmi.name/res/cos/LL/index.html)

### Focused Proof Search

- [Focused proof - Wikipedia](https://en.wikipedia.org/wiki/Focused_proof)
- [Efficient Resource Management for Linear Logic Proof Search (CMU)](https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/focus.pdf)
- [focusing in nLab](https://ncatlab.org/nlab/show/focusing)

### Celf and CLF

- [Celf – A Logical Framework for Deductive and Concurrent Systems](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28)
- [15-816 Linear Logic / Software (CMU)](https://www.cs.cmu.edu/~fp/courses/15816-s12/software.html)

### Nested Sequents

- [Nested sequent calculus (Grokipedia)](https://grokipedia.com/page/nested_sequent_calculus)
- [From Display Calculi to Deep Nested Sequent Calculi (Springer)](https://link.springer.com/chapter/10.1007/978-3-662-44602-7_20)

### Calculus Toolbox

- [Calculus Toolbox: Introduction](http://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html)
- [Calculus Toolbox: Display Calculi](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculi.html)

---

## Appendix: Glossary

**Display Postulate**: A rule that shuffles structures around without affecting provability.

**Focusing**: Proof search discipline that alternates between invertible (async) and non-invertible (sync) phases.

**Residuation**: The relationship between connectives forming a Galois connection: `A ⊗ B ⊢ C iff A ⊢ B ⊸ C`.

**Structural Connective**: A connective at the structure level (e.g., comma) that mirrors a logical connective (e.g., tensor).

**Subformula Property**: A proof system has this if every formula in a cut-free proof is a subformula of the conclusion.

**Cut Elimination**: The property that the cut rule can be eliminated from any proof, yielding a direct proof.

---

## Appendix: Calculus-Toolbox-2

The original calculus-toolbox has a new version: [calculus-toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2)

**Key improvements over original:**
- **Runtime calculus loading**: No recompilation needed to change calculi
- **DSL-based specification**: Define calculi with a domain-specific language
- **Multi-type display calculi**: Supports connectives across multiple types (e.g., D.EAK calculus)
- **Formula abbreviations**: Hide complexity behind labels
- **LaTeX rendering**: Mathematical notation in UI

**Technology stack:** Haskell backend (65%), JavaScript frontend (31%)

**Relevance to our project:**
- The DSL approach is similar to our `ll.json` but more principled
- Multi-type support is relevant for multimodal extensions
- Runtime loading aligns with our "core + calculus plugin" architecture vision
- Could inspire our UI redesign

---

## Appendix: Par Residuals Explained

**The confusion:** I incorrectly wrote that par has "subtraction" and "co-subtraction" as residuals. Let me clarify properly.

### What Residuation Actually Is

Residuation is an **adjunction** (Galois connection). For a binary connective ★, its residuals are defined by:
```
A ★ B ⊢ C   iff   A ⊢ B → C   iff   B ⊢ A ← C
```

Where `→` is the right residual and `←` is the left residual.

### For Tensor (⊗) in Linear Logic

```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C   iff   B ⊢ C ○− A
```

- **Right residual of ⊗**: The lollipop `⊸` (A ⊸ B = A⊥ ⅋ B)
- **Left residual of ⊗**: The reverse lollipop `○−` (B ○− A = B ⅋ A⊥)

In **commutative** linear logic, these coincide: `A ⊸ B = B ○− A` because ⊗ is commutative.

### For Par (⅋) - The Tricky Part

Par does NOT have simple residuals in the same sense. Here's why:

In classical linear logic, par is **defined** via De Morgan duality:
```
A ⅋ B = (A⊥ ⊗ B⊥)⊥
```

The "residuation" for par comes from dualizing the tensor residuation:
```
C ⊢ A ⅋ B   iff   C ⊗ A⊥ ⊢ B   iff   C ⊗ B⊥ ⊢ A
```

This isn't expressed as a connective applied to C - it's about moving things to the other side via negation.

**In non-commutative linear logic** (Lambek calculus), you do get distinct left/right operations, but standard (commutative) linear logic doesn't distinguish them.

### The ? (Why Not) Connection

The `?` modality is NOT a residual of par. It's the **De Morgan dual of !**:
```
?A = (!A⊥)⊥
```

My earlier table was misleading. The correct picture is:

| Operation | Definition | Role |
|-----------|------------|------|
| A ⊸ B | A⊥ ⅋ B | Linear implication (right residual of ⊗) |
| B ○− A | B ⅋ A⊥ | Reverse implication (left residual of ⊗) |
| A ⅋ B | (A⊥ ⊗ B⊥)⊥ | De Morgan dual of tensor |
| !A | "of course" A | Exponential allowing contraction/weakening |
| ?A | (!A⊥)⊥ | Dual exponential |

---

## Appendix: Why Proof Nets + Modalities is Hard

### The Core Problem

Proof nets work beautifully for **MLL** (multiplicative linear logic) because:
1. The correctness criterion is local (graph properties)
2. Cut elimination is local graph rewriting
3. There's no "boxes" or nesting

### Exponentials (!) Already Cause Problems

When you add exponentials (!/?), you need **boxes** - regions of the proof net that are treated specially:
- Boxes can be duplicated (contraction) or deleted (weakening)
- This makes cut elimination non-local
- Correctness criteria become more complex

From [Girard's work](https://girard.perso.math.cnrs.fr/Proofnets.pdf): "The rules for exponentials follow a different pattern from the rules for other connectives, resembling the inference rules governing modalities in sequent calculus formalisations of the normal modal logic S4."

### Modal Logic: Even Harder

For modal operators (□, ◇), the situation is worse:

1. **No known proof nets for modal logics** - even simple ones like K or S4
2. Modal operators need to track "worlds" or "accessibility"
3. This requires structure that proof nets eliminate

From [Straßburger's open problems](https://www.lix.polytechnique.fr/~lutz/problems.html): "There are, so far, no proof nets for modal logics—not even with boxes."

### What CAN Be Done

1. **Subexponentials**: Index exponentials with labels, encode modalities as special exponentials
2. **Proof nets for specific modal logics**: Some progress on S4-like systems
3. **Multimodal Lambek calculus**: Proof nets exist (see [Moot & Puite](https://www.semanticscholar.org/paper/Proof-Nets-for-the-Multimodal-Lambek-Calculus-Moot-Puite/c5d077d1e9e09fa7bf6a75d7c556838c6f06f7a7))

### For Your Goals (Multimodal Quantitative Types)

Proof nets for full multimodal quantitative linear logic would be **research frontier** territory. Possible paths:
1. Use proof nets for the multiplicative fragment only
2. Use subexponentials to encode modalities
3. Accept boxes for quantitative/modal parts
4. Use a different representation (sequent calculus) for modal parts

---

## Appendix: Display Calculus vs Labelled Calculus

### Expressiveness Hierarchy

```
Standard sequent < Hypersequent < Nested sequent < Display ≈ Labelled
```

Both display and labelled calculi can handle a very wide range of logics, but they differ in philosophy:

### Display Calculus

**Internal**: Every proof step is a formula of the logic itself.
**Algebraic semantics**: Based on residuated structures.
**Modular cut-elimination**: Belnap's conditions give cut-elim for free.

**Pros:**
- Purer - no external semantic information in proofs
- Generic cut-elimination
- Good for structural rule manipulation

**Cons:**
- Display postulates can explode search space
- More complex proof objects

### Labelled Calculus

**External**: Proofs mention worlds/labels not in the logic's language.
**Kripke semantics**: Directly encodes accessibility relations.
**Most expressive**: Can handle almost any modal logic.

**Pros:**
- Very flexible - just add accessibility axioms
- Direct connection to Kripke semantics
- Simpler rules (no display postulates)

**Cons:**
- "External" - proofs are not purely syntactic
- May lose subformula property
- Cut-elimination more manual

### Research Backing

Both have extensive research:
- **Display**: Belnap (1982), Goré (1998), Wansing, Ciabattoni
- **Labelled**: Negri, von Plato, Viganò, Simpson

**Translation results**: For many logics (e.g., tense logics), display and labelled proofs can be translated back and forth (see [Goré et al.](https://dl.acm.org/doi/10.1145/3460492)).

### For Your Goals

If multimodalities are critical and you don't know exactly what modal logic you need:
- **Labelled sequent calculus** might be more practical (easier to experiment)
- **Display calculus** might be more principled (if you want generic cut-elimination)

Consider: **Labelled calculus for experimentation → Display calculus for final formalization**

---

## Appendix: Calculus-Toolbox-2 DSL Deep Dive

### The DSL Structure

Calculus-toolbox-2 uses a two-file DSL approach:
- `.calc` files define types and connectives
- `.rules` files define inference rules

### Type Definitions

```
default type atprop        -- atomic propositions (must mark one as default)
type agent                 -- additional types for multi-type calculi
```

### Connective Definitions

Syntax: `name : signature (parser_sugar, associativity, precedence, latex)`

```
-- Nullary (constants)
bot : formula ("0", NonAssoc, 10, "\bot")
top : formula ("1", NonAssoc, 10, "\top")

-- Binary formula connectives
and : formula -> formula -> formula ("_/\_", LeftAssoc, 6, "#1 \land #2")
imp : formula -> formula -> formula ("_->_", RightAssoc, 5, "#1 \to #2")

-- Structural connectives
comma : structure -> structure -> structure ("_;_", LeftAssoc, 3, "#1 ; #2")
turnstile_r : structure -> structure -> structure ("_>_", RightAssoc, 2, "#1 > #2")
```

The `_` marks holes in mixfix notation (like Agda/Isabelle).

### Rule Definitions (Natural Deduction Style)

```
A , B |- X
----------- andL
A /\ B |- X

X |- A    Y |- B
---------------- andR
X ; Y |- A /\ B
```

Variables are auto-inferred as atom/formula/structure based on connective usage.
Prefix `at_` forces atom level: `at_A` is always atomic.

---

## Appendix: Multi-Type Display Calculi

### What They Are

Standard display calculi have ONE type (formulas). **Multi-type display calculi** have MULTIPLE types that interact through connectives.

### The D.EAK Example

D.EAK (Dynamic Epistemic Actions and Knowledge) has:
- **Type `atprop`**: atomic propositions
- **Type `agent`**: epistemic agents (Alice, Bob, ...)

Connectives can span types:

```
box : formula{agent} -> formula{atprop} -> formula ("[_]_", NonAssoc, 4, "\Box_{#1} #2")
```

This defines `[a]φ` meaning "agent a knows φ".

### Why Multi-Type Matters

1. **Cleaner separation**: Different "sorts" of things don't mix accidentally
2. **Richer expressivity**: Can express relationships BETWEEN types
3. **Modular design**: Add new types without breaking existing rules
4. **Better for dynamic logics**: Actions, agents, propositions are different things

### For Your Goals (Multimodal Quantitative Types)

Multi-type display calculi are **highly relevant**:
- **Type `proposition`**: linear logic formulas
- **Type `owner`**: Alice, Bob, ... (for ownership modalities)
- **Type `quantity`**: semiring elements (for coefficients)

Example connective:
```
owned : formula{owner} -> formula{proposition} -> formula ("[_]_", ...)
```
Meaning: `[Alice]A` = "A is owned by Alice"

---

## Appendix: Formula Abbreviations

### The Problem

Complex proofs get cluttered with repeated subformulas:
```
(A -o B) * (B -o C) * (C -o D) |- (A -o B) * (B -o C) * (C -o D)
```

### Calculus-Toolbox-2 Solution

Define abbreviations and reference them with `{{...}}`:

```
-- Definition
let chain = (A -o B) * (B -o C) * (C -o D)

-- Usage in proofs
{{chain}} |- {{chain}}
```

### Implementation Ideas for Our Project

1. **Parse-time expansion**: `{{name}}` → substitute definition
2. **Display-time contraction**: Show abbreviated form in UI
3. **Bidirectional**: User can toggle between expanded/abbreviated view
4. **Nested abbreviations**: `{{outer}}` can contain `{{inner}}`

This is similar to Isabelle's `abbreviation` command or Coq's `Notation`.

---

## Sources

### Calculus-Toolbox-2
- [GitHub: calculus-toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2)
- [Calculus Toolbox Documentation](https://goodlyrottenapple.github.io/calculus-toolbox/)
- [Display Calculi Documentation](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculi.html)

### Multi-Type Display Calculi
- [Multi-type display calculus for dynamic epistemic logic (HAL)](https://hal.science/hal-01509398)
- [D.EAK Paper (arXiv)](https://arxiv.org/abs/1805.07586)
- [Journal of Logic and Computation (Oxford)](https://academic.oup.com/logcom/article-abstract/26/6/2017/2743523)
- [Software Tool Support (Springer)](https://link.springer.com/chapter/10.1007/978-3-319-94821-8_4)

---

*Last updated: 2026-01-23*

---

## Appendix: Educational Condition Checker UI

### Vision: "Calculus Health Check" Tab

An educational UI component that explains Belnap's conditions and shows how the current calculus satisfies (or violates) them.

### Mockup

```
┌─────────────────────────────────────────────────────────────────────┐
│  📋 Calculus Health Check                              [ll.json ▼]  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  This tool checks Belnap's 8 conditions for cut elimination.        │
│  If all conditions pass, cut elimination is GUARANTEED.             │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ C1 - Preservation of Formulas                         ✅    │   │
│  │                                                              │   │
│  │ "Each formula in a premise must be a subformula of some     │   │
│  │  formula in the conclusion. Structure may disappear,        │   │
│  │  but formulas cannot."                                      │   │
│  │                                                              │   │
│  │ Why it matters: Ensures the subformula property - proofs    │   │
│  │ only contain formulas from the goal.                        │   │
│  │                                                              │   │
│  │ [12 rules checked] [Show details ▼]                         │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ C2 - Shape-alikeness of Parameters                    ✅    │   │
│  │                                                              │   │
│  │ "Congruent parameters (same variable in premise and         │   │
│  │  conclusion) must have the same structure type."            │   │
│  │                                                              │   │
│  │ Example from Tensor_L:                                      │   │
│  │   ?X appears in both premise and conclusion                 │   │
│  │   Both occurrences are Structure type ✓                     │   │
│  │                                                              │   │
│  │ [Show details ▼]                                            │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ... (C3 through C8) ...                                           │
│                                                                     │
│  ════════════════════════════════════════════════════════════════  │
│                                                                     │
│  📊 Summary                                                         │
│  ─────────────────────────────────────────────────────────────────  │
│  Conditions passed: 8/8                                             │
│  Rules checked: 12 logical + 16 structural                          │
│                                                                     │
│  ✅ CUT ELIMINATION GUARANTEED                                      │
│                                                                     │
│  By Belnap's theorem (1982), any display calculus satisfying       │
│  conditions C1-C8 admits cut elimination. Your calculus qualifies! │
│                                                                     │
│  [Learn more about Belnap's theorem →]                             │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### Detailed Condition Explanations

For each condition, the UI would show:

| Condition | One-liner | Detailed Explanation | Example |
|-----------|-----------|---------------------|---------|
| **C1** | Formulas preserved | Formulas in premises are subformulas of conclusion formulas. Structure can disappear. | `Tensor_L`: premise has `F?A, F?B` which are subformulas of `F?A * F?B` in conclusion |
| **C2** | Shape-alike params | Same variable = same type | `?X` is always Structure, `F?A` is always Formula |
| **C3** | No proliferation | Each param maps to ≤1 thing in conclusion | `?X` appears once in conclusion |
| **C4** | Position-alike | Same variable = same side (left/right) | `?X` always on left of ⊢ |
| **C5** | Principal displayed | Principal formula is whole antecedent or consequent | `Tensor_L`: `F?A * F?B` is the formula being decomposed |
| **C6** | Closed under substitution | Can substitute any structure for variables | `?X` can be any structure |
| **C7** | Matching principals reducible | Cut on same principal can be eliminated | `Tensor_R` + `Tensor_L` cuts can be reduced |
| **C8** | Structure preserved in reduction | Cut reduction doesn't create new structure | Reducing cuts keeps structure bounded |

### Implementation Notes

The checker would be:
1. **Generic** - works on any `*.json` calculus definition
2. **Educational** - explains each condition clearly
3. **Interactive** - click to see which rules satisfy/violate
4. **Exportable** - generate report for documentation

### Why This Matters for Learning

Most textbooks state Belnap's conditions abstractly. This tool would:
- Make conditions **concrete** with examples from your calculus
- Show **why** cut elimination works (not just that it does)
- Help **design** new calculi by catching violations early
- Support **education-driven development**

---

## Appendix: ll.json Conformance Analysis

### Overview

This section analyzes whether `ll.json` conforms to the display calculus specification, identifies gaps, and discusses programmatic verification of cut elimination.

### Belnap's Eight Conditions (C1-C8) - Complete List

From Belnap's 1982 paper "Display Logic" (Journal of Philosophical Logic 11(4):375-417):

| Condition | Name | Description | ll.json Status |
|-----------|------|-------------|----------------|
| **C1** | Preservation of Formulas | Each formula in a premise is a subformula of some formula in the conclusion. Structure may disappear, but not formulas. | ✅ Satisfied |
| **C2** | Shape-alikeness | Congruent parameters are shape-alike (same structure type). | ✅ Satisfied |
| **C3** | Non-proliferation | Each parameter is congruent to at most one constituent in the conclusion. | ✅ Satisfied |
| **C4** | Position-alikeness | Congruent parameters are either all antecedent-parts or all consequent-parts. | ✅ Satisfied |
| **C5** | Display of Principal | If a formula is non-parametric (principal) in the conclusion, it is the entire antecedent or entire consequent. | ⚠️ Partially - rules use `?X, formula ⊢ Y` pattern |
| **C6** | Closure under Substitution | Rules are closed under uniform substitution of parameters. | ✅ Satisfied |
| **C7** | Eliminability of Matching Principals | If cut formula is principal in both premises, the cut can be eliminated. | ✅ Satisfied for defined rules |
| **C8** | Cut Reduction Preserves Structure | Reducing a cut doesn't create new structure. | ✅ Satisfied |

### What ll.json Has

**Structural Layer:**
```
Structure_Freevar    ?X, ?Y, ?Z, ?W     (structural metavariables: Γ, Δ, Σ, Π)
Structure_Comma      X, Y               (structural conjunction - mirrors ⊗)
Structure_Neutral    I                  (structural unit - mirrors 1)
Structure_Term_Formula  -- : A          (term-formula pairing)
```

**Logical Connectives:**
```
Formula_Tensor       A * B    (multiplicative conjunction)
Formula_Loli         A -o B   (linear implication)
Formula_With         A & B    (additive conjunction)
Formula_Bang         !A       (exponential)
```

**Inference Rules:**
- Identity (Id)
- Cut (SingleCut)
- Tensor_L, Tensor_R
- Loli_L, Loli_R
- With_L, With_L2, With_R
- Bang_L, Bang_R

**Structural Rules (Display Postulates):**
- P_L, P_R (permutation/exchange)
- A_L, A_L2, A_R, A_R2 (associativity)
- I_L_L, I_L_L2, I_L_R, I_L_R2 (left unit laws)
- I_R_L, I_R_L2, I_R_R, I_R_R2 (right unit laws)

### What's Missing from Full Display Calculus for Linear Logic

| Missing Element | What it is | Why it matters |
|-----------------|-----------|----------------|
| **Par (⅋)** | Multiplicative disjunction | De Morgan dual of ⊗. Display calculus should have both. |
| **Plus (+)** | Additive disjunction | De Morgan dual of &. Only & is defined. |
| **Why-not (?)** | Dual exponential | De Morgan dual of !. Only ! is defined. |
| **Bottom (⊥)** | Multiplicative false | Unit for ⅋. |
| **Zero (0)** | Additive false | Unit for +. |
| **Top (⊤)** | Additive true | Unit for &. |
| **One (1)** | Multiplicative true | Unit for ⊗. (Partially: `I` exists but not as logical 1) |
| **Structural ⅋** | Structural disjunction | Structural counterpart to par. |
| **Display postulates for ⅋** | Residuation for par | `X ; Y ⊢ Z ↔ X ⊢ Z > Y` style rules. |

### What's Extra / Unnecessary

| Element | Status | Notes |
|---------|--------|-------|
| **RuleStruct (P_L, A_L, etc.)** | UNUSED | Marked as unused in ll.json. Proof search uses multiset operations instead. |
| **Structure_Bin** | Partially used | Binary structure operations defined but proof search treats context as multiset. |
| **Term_Pair, Term_Concatenate** | Unused | Term-level operations not used in current rules. |
| **Monad_R, Formula_Monad** | Unused | Monadic extension defined but no complete rules. |
| **Formula_Lax, Formula_Forall** | Experimental | Additional connectives without full rule sets. |

### Conformance Verdict

**ll.json is a valid display calculus for the intuitionistic linear logic (ILL) fragment:**

1. ✅ **Correct structure**: Has the right shape for a display calculus
2. ✅ **Conditions C1-C8**: Rules satisfy Belnap's conditions
3. ✅ **Complete for ILL**: Has all connectives needed for intuitionistic fragment
4. ⚠️ **Unused structural rules**: Display postulates (P_L, A_L, etc.) defined but not used by focused proof search
5. ⚠️ **Hybrid architecture**: Display-style rules + focused multiset proof search

### Do You Need Par, Plus, Why-not?

**No!** These are only needed for *classical* linear logic. Belnap's conditions work on ANY display calculus, regardless of which connectives it has.

| Fragment | Connectives | Valid Display Calculus? |
|----------|-------------|------------------------|
| **ILL (your ll.json)** | ⊗, ⊸, &, ! | ✅ Yes |
| Classical LL | ⊗, ⅋, ⊸, &, +, !, ? | ✅ Yes |
| MLL only | ⊗, ⅋, ⊸ | ✅ Yes |
| Lambek | ⊗, /, \ (non-commutative) | ✅ Yes |

The conditions are about **rule shape**, not **which connectives exist**. Your ILL fragment is perfectly valid and Belnap's cut-elimination theorem applies.

### What About the Unused Structural Rules (P_L, A_L, etc.)?

**Two proof search strategies exist:**

```
┌─────────────────────────────────────────────────────────────────┐
│ PURE DISPLAY CALCULUS                                           │
│                                                                 │
│ Context = TREE of structures: ((A, B), C)                       │
│                                                                 │
│ To access B, must apply display postulates:                     │
│   ((A, B), C) ⊢ D                                               │
│   ───────────────── A_L (associativity)                         │
│   (A, (B, C)) ⊢ D                                               │
│   ───────────────── (more shuffling...)                         │
│   B ⊢ ...                                                       │
│                                                                 │
│ Uses: P_L, P_R, A_L, A_R, I_L_*, I_R_*                          │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ FOCUSED MULTISET (your proofstate.js)                           │
│                                                                 │
│ Context = MULTISET: {A, B, C}                                   │
│                                                                 │
│ Direct access to any formula - just pick B from the set.        │
│ No shuffling needed.                                            │
│                                                                 │
│ Uses: Direct multiset operations (add, remove, split)           │
│ Does NOT use: P_L, P_R, A_L, A_R, I_L_*, I_R_*                  │
└─────────────────────────────────────────────────────────────────┘
```

**Can you remove the structural rules?**

| Option | Pros | Cons |
|--------|------|------|
| **Remove them** | Cleaner ll.json, less confusion | Loses Isabelle export compatibility, loses educational value |
| **Keep but mark unused** | Isabelle export works, can show in UI for learning | Slightly cluttered ll.json |
| **Move to separate file** | Clean separation of concerns | More files to manage |

**Recommendation:** Keep them with clear documentation. They're valuable for:
- Isabelle/formal verification export
- Educational display in UI ("these are the display postulates")
- Future: if you ever want pure display calculus proof search

---

## Appendix: Programmatic Cut Elimination Verification

### Can Cut Elimination Be Checked Automatically?

**Short answer:** Partially yes, but requires effort.

### Approaches

#### 1. Syntactic Condition Checking (Feasible)

Belnap's C1-C8 are **syntactically checkable**. A program can:
- Parse rule definitions
- Check each condition against the rule structure
- Report violations

**What we could implement:**
```javascript
function checkC1(rule) {
  // Check: each formula in premises is subformula of conclusion
  const conclusionFormulas = extractFormulas(rule.conclusion);
  for (const premise of rule.premises) {
    for (const formula of extractFormulas(premise)) {
      if (!isSubformulaOf(formula, conclusionFormulas)) {
        return { valid: false, reason: `Formula ${formula} not in conclusion` };
      }
    }
  }
  return { valid: true };
}
```

**Complexity:** Medium. Need to parse rules and check structural properties.

#### 2. Isabelle/Coq Formalization (Gold Standard)

The calculus-toolbox approach:
- Define calculus in Isabelle/HOL
- Use Belnap's metatheorem (already formalized)
- Automatically get cut-elimination

**Existing work:**
- [Machine-checked Cut-elimination for Display Logic](https://www.semanticscholar.org/paper/Machine-checked-Cut-elimination-for-Display-Logic-Dawson-Gor%C3%A9/136a2e70d63f9a23dff5f75a02632dd55bf1b9fa) - First full formalization
- [Coq formalization for modal logics](https://www.semanticscholar.org/paper/Formalizing-Cut-Elimination-of-Coalgebraic-Logics-Tews/14f0291c9d835fd68616dee2f1f8e18456383815) - Generic approach

**Effort:** High. Need Isabelle/Coq expertise and formal encoding of ll.json.

#### 3. "Proper Display Calculus" Approach (Emerging)

Recent work on [Linear Logic Properly Displayed](https://dl.acm.org/doi/10.1145/3570919) shows that **properness** (closure under uniform substitution) is key.

**Key insight:** If rules satisfy:
- (a) Logical rules are reductive
- (b) Structural rules are weakly substitutive

Then cut elimination follows automatically.

### Practical Recommendation

**Phase 1: Implement syntactic checks as UI tab**

Create an educational "Calculus Health Check" tab in the web UI:
- Display each condition (C1-C8) with clear explanation
- Show which rules satisfy/violate each condition
- Interactive: click on a condition to see relevant rules highlighted
- Works on ANY calculus definition, not just ll.json

```
┌─────────────────────────────────────────────────────────┐
│  Calculus Health Check: ll.json (ILL fragment)          │
├─────────────────────────────────────────────────────────┤
│  ✅ C1 - Preservation of Formulas                       │
│     Every formula in premises is subformula of          │
│     conclusion. Structure may disappear, not formulas.  │
│     [View 12 rules that satisfy this]                   │
│                                                         │
│  ✅ C2 - Shape-alikeness                                │
│     Congruent parameters have the same structure type.  │
│     [View details]                                      │
│     ...                                                 │
│                                                         │
│  ══════════════════════════════════════════════════════ │
│  Result: All conditions satisfied!                      │
│  → Cut elimination is GUARANTEED by Belnap's theorem    │
└─────────────────────────────────────────────────────────┘
```

**Phase 2: Export to Isabelle for formal verification** (optional)
- Use existing calculus-toolbox Isabelle theories
- Generate `.thy` file from ll.json
- Run Isabelle to verify cut-elimination

**Phase 3: Trust the metatheorem**
- If C1-C8 pass, Belnap's theorem guarantees cut-elimination
- Document the verification
- No need for per-rule proof

### Genericity of the Checker

**The condition checker is calculus-agnostic.** Belnap's conditions are about the *shape* of rules, not the specific connectives. The same checker works for:

| Calculus | File | Description |
|----------|------|-------------|
| ILL (current) | `ll.json` | Intuitionistic multiplicative/additive linear logic |
| Classical LL | `classical-ll.json` | Full classical linear logic with duals |
| Lambek | `lambek.json` | Non-commutative (no exchange rule) |
| Bi-intuitionistic | `bi-int.json` | Both implication and co-implication |
| Modal logics | `s4.json`, `k.json` | Various modal logics |

This supports an **education-driven development** approach:
1. Define a calculus in JSON
2. Run the checker to learn which conditions are satisfied
3. Understand *why* cut elimination holds (or doesn't)
4. Iterate on the calculus design

### What Proofs Would Be Necessary?

If NOT using Belnap's metatheorem, a manual cut-elimination proof requires:

1. **Define complexity measures:**
   - Grade: number of connectives in cut formula
   - Rank: height of derivations above cut

2. **Show key lemmas:**
   - Substitution lemma
   - Weakening lemma (if applicable)
   - Inversion lemmas for each rule

3. **Main theorem (by induction):**
   - Base: cut on atomic formula
   - Inductive step: reduce grade or rank
   - Show all cases terminate

**Estimated effort:** 50-100 pages of proof, weeks of work.

**With Belnap's metatheorem:** Check 8 syntactic conditions, ~1 day of implementation.

---

## Appendix: Recommendations

### Immediate Actions

1. **Implement Calculus Health Check UI tab** - Educational display of C1-C8 conditions
   - Show each condition with explanation
   - Indicate which rules satisfy/violate
   - Works on any calculus definition (generic)

2. **Update ll.json metadata** - Mark structural rules clearly:
   ```json
   "RuleStruct": {
     "_note": "Display postulates. Not used by focused proof search, but kept for Isabelle export and educational display.",
     ...
   }
   ```

3. **Document hybrid architecture** - Explain in ll.json or separate doc:
   - Display-style rule definitions (for clarity, export)
   - Focused multiset proof search (for efficiency)

### Medium-term

1. **Isabelle export** for formal verification:
   - Generate `.thy` file from ll.json
   - Use calculus-toolbox theories as base
   - Machine-checked cut-elimination

2. **Support multiple calculi**:
   - Keep ll.json as ILL fragment
   - Add other `.json` files for different logics
   - Condition checker works on all

### Long-term (if needed)

1. **Extend to classical LL** (only if required):
   - Add Par (⅋), Plus (+), Why-not (?)
   - Add proper units and duals

2. **Multi-type display calculus** for multimodalities:
   - Types for propositions, owners, quantities
   - D.EAK-style architecture

### What NOT to Do

- ❌ Don't add Par/Plus/Why-not unless you actually need classical LL
- ❌ Don't remove structural rules - keep for export and education
- ❌ Don't feel obligated to use "pure" display calculus proof search - focused is better for efficiency
