---
title: "Logics of Interest: Display Calculus Expressibility"
created: 2026-02-10
modified: 2026-02-10
summary: Survey of linear, modal, and quantitative logics assessing display calculus expressibility from classical linear logic to QTT and graded modal types.
tags: [logics-survey, display-calculus, linear-logic, modal-logic, QTT]
category: "Proof Theory"
---

# Logics of Interest: Display Calculus Expressibility

Overview of logics relevant to the CALC project and whether they can be expressed via display calculus.

> **See also:** [[display-calculus]] for display calculus methodology, [[graded-resource-tracking]] for QTT/Granule, [[multi-type-display-calculus]] for MTDC approach, [[exponential-display-problem]] for ! handling.

---

## Table of Contents

1. [Summary Table](#summary-table)
2. [Classical Linear Logic (CLL)](#1-classical-linear-logic-cll)
3. [Intuitionistic Linear Logic (ILL)](#2-intuitionistic-linear-logic-ill)
4. [Full Intuitionistic Linear Logic (FILL)](#3-full-intuitionistic-linear-logic-fill)
5. [First-Order Logic (FOL)](#4-first-order-logic-fol)
6. [Multimodal Logic](#5-multimodal-logic)
7. [Quantitative Type Theory (QTT)](#6-quantitative-type-theory-qtt)
8. [Graded Modal Types (Granule)](#7-graded-modal-types-granule)
9. [Mixed Linear and Graded (mGL)](#8-mixed-linear-and-graded-logic-mgl)
10. [Linear Logic Properly Displayed](#9-linear-logic-properly-displayed)
11. [Hypersequent Calculus (HCP)](#10-hypersequent-calculus-hcp)
12. [Conclusions](#conclusions-for-your-project)

---

## Summary Table

| Logic | Display Calculus? | Notes | Key Reference |
|-------|-------------------|-------|---------------|
| **Classical Linear Logic (CLL)** | ✅ Yes | Fully supported, modular treatment | Restall 1991 |
| **Intuitionistic Linear Logic (ILL)** | ✅ Yes | Current ll.json implements this | Your project |
| **Full Intuitionistic Linear Logic (FILL)** | ✅ Yes | With exclusion connective | Clouston et al. 2013 |
| **Bi-Intuitionistic Linear Logic (BiILL)** | ✅ Yes | Extension of FILL | Dawson & Goré |
| **First-Order Logic (FOL)** | ✅ Yes | Quantifiers as modalities | "First Order Logic Properly Displayed" |
| **Multimodal Logic** | ✅ Yes | Multi-type display calculus excels here | Frittella et al. 2016 |
| **Dynamic Epistemic Logic** | ✅ Yes | D.EAK calculus | Greco & Palmigiano |
| **Quantitative Type Theory (QTT)** | ⚠️ Indirect | QTT is a type theory, not a logic; related via Curry-Howard | See note below |
| **Graded Modal Types (Granule)** | ⚠️ Indirect | Sequent calculus exists, not display-style | Orchard et al. 2019 |
| **Mixed Linear + Graded (mGL)** | ⚠️ Partial | Sequent calculus proven, display variant possible | CSL 2025 paper |
| **HCP (Hypersequent Calculus)** | ⚠️ Related | Different formalism, can embed in display | Ciabattoni et al. |

---

## Detailed Analysis

### 1. Classical Linear Logic (CLL)

**Display Calculus Support:** ✅ Full

Greg Restall's 1991 paper "[A Display Calculus for Classical Linear Logic](https://greg.restall.net//papers/dcll.html)" adds all connectives of CLL to Belnap's display logic:
- Multiplicatives: ⊗, ⅋, ⊸
- Additives: &, ⊕
- Exponentials: !, ?
- Units: 1, ⊥, ⊤, 0

The systems are **modular**: different systems for different fragments can be found by suitable restrictions.

**Cut Elimination:** ✅ Via Belnap's metatheorem

---

### 2. Intuitionistic Linear Logic (ILL)

**Display Calculus Support:** ✅ Full

This is what your current `ll.json` implements. ILL is CLL without:
- Par (⅋) - multiplicative disjunction
- Plus (+) - additive disjunction
- Why-not (?) - dual exponential

**Key insight from previous research:** You do NOT need to add the missing duals for Belnap's conditions to hold. ILL is a valid fragment.

**Cut Elimination:** ✅ Conditions C1-C8 satisfied

---

### 3. Full Intuitionistic Linear Logic (FILL)

**Display Calculus Support:** ✅ Full

FILL = ILL + Par. Its proof theory is notoriously difficult, but:

> "We develop a simple and annotation-free display calculus for FILL which satisfies Belnap's generic cut-elimination theorem." — [Clouston et al. 2013](https://arxiv.org/abs/1307.0289)

The display calculus actually handles **Bi-Intuitionistic Linear Logic (BiILL)** with an 'exclusion' connective.

**Cut Elimination:** ✅ Via Belnap's metatheorem

---

### 4. First-Order Logic (FOL)

**Display Calculus Support:** ✅ Full

[First Order Logic Properly Displayed](https://www.researchgate.net/publication/351624115_First_order_logic_properly_displayed) shows:
- Quantifiers treated as modal operators (∃ ≈ ◇, ∀ ≈ □)
- Sound, complete, conservative
- Subformula property
- **Cut elimination via Belnap-style metatheorem**
- All inference rules closed under uniform substitution, no side conditions

This means you could add quantifiers to linear logic using display calculus methodology.

---

### 5. Multimodal Logic

**Display Calculus Support:** ✅ Excellent

This is where display calculus **shines**. Multi-type display calculus handles:
- Multiple indexed modalities: □_i, ◇_i
- Different types: agents, propositions, actions
- Accessibility relations between modes

**D.EAK (Dynamic Epistemic Actions and Knowledge):**
> "The display approach is suitable to modularly chart the space of dynamic epistemic logics on weaker-than-classical propositional base." — [Frittella et al. 2016](https://academic.oup.com/logcom/article-abstract/26/6/2017/2743523)

**Relevance to your goals:** Ownership modalities `[Alice]A`, `[Bob]A` fit naturally here.

**Cut Elimination:** ✅ Belnap-style

---

### 6. Quantitative Type Theory (QTT)

**Display Calculus Support:** ⚠️ Indirect

QTT is a **type theory**, not a logic. It lives on the "type" side of Curry-Howard, while display calculus is on the "proof" side.

**Connection:**
```
Display Calculus for Linear Logic
            ↓ (Curry-Howard)
Linear Type Theory
            ↓ (add semiring grading)
QTT-like System
```

**What exists:**
- [Atkey's semantics](https://bentnib.org/quantitative-type-theory.html) - categorical foundations
- [Idris 2](https://arxiv.org/abs/2104.00480) - practical implementation
- No direct display calculus formulation

**For your goals:** Use display calculus for the logic layer, add QTT-style multiplicities on top.

---

### 7. Graded Modal Types (Granule)

**Display Calculus Support:** ⚠️ Indirect

Granule uses a sequent calculus, but not display-style:

> "The structure of the synthesis calculi mirrors a cut-free sequent calculus, with left and right rules for each type constructor." — Granule synthesis paper

**What exists:**
- [Granule ICFP 2019](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf) - graded modal types
- [Grtt](https://link.springer.com/chapter/10.1007/978-3-030-72019-3_17) - graded modal dependent types
- Sequent calculus presentations, not display

**Could it be display-ified?** Likely yes - the methodology exists, but no one has done it yet.

---

### 8. Mixed Linear and Graded Logic (mGL)

**Display Calculus Support:** ⚠️ Partial

Recent work from the Granule team ([CSL 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2025.32)):

> "We propose a sequent calculus, its proof theory and categorical model, and a natural deduction system which is shown to be isomorphic to the sequent calculus system."

The graded "of-course" modality !_r captures how many times a proposition is used.

**Key insight:** Graded modalities split into two modalities connecting graded logic with graded linear logic.

**Display variant:** Not yet, but the methodology from "Linear Logic Properly Displayed" could apply.

---

### 9. Linear Logic Properly Displayed

**The State of the Art:**

[Greco & Palmigiano's paper](https://dl.acm.org/doi/10.1145/3570919) introduces **proper** display calculi for:
- Intuitionistic linear logic
- Bi-intuitionistic linear logic
- Classical linear logic
- All with exponentials

**Key innovation:** Properness (closure under uniform substitution) enables:
- Smoothest proof of cut elimination
- Modular treatment of axiomatic extensions
- Overarching framework for vast class of linear logics

**Exponentials challenge solved:**
> "If structural counterparts for exponentials were allowed... the resulting calculus would lose the display property... This paper solves this by a proper treatment."

---

### 10. Hypersequent Calculus (HCP)

**Display Calculus Support:** ⚠️ Related but different

Hypersequents are a **different** proof formalism:
```
Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ... | Γₙ ⊢ Δₙ
```

**Relationship:**
```
Standard sequent < Hypersequent < Nested sequent < Display ≈ Labelled
```

Hypersequents can be **embedded** into display calculus, but they're less expressive.

**Use cases:**
- S5 modal logic (prime example)
- Gödel logics
- Some intermediate logics

---

## Conclusions for Your Project

### What Display Calculus Handles Well

1. **Classical/Intuitionistic Linear Logic** - ✅ Full support
2. **First-Order extensions** - ✅ Quantifiers work
3. **Multimodal extensions** - ✅ This is display's strength
4. **Ownership modalities** - ✅ Fits multi-type display calculus

### What Needs Extra Work

1. **Semiring-graded quantities** - No direct display calculus exists yet
   - Workaround: Use Granule-style sequent calculus + display methodology

2. **QTT-style dependent types** - Display is for logic, QTT is for types
   - Workaround: Curry-Howard correspondence

### Recommended Architecture

```
┌─────────────────────────────────────────────────────────┐
│ Multi-Type Display Calculus                             │
│ (modalities for owners, structural rules for linearity) │
├─────────────────────────────────────────────────────────┤
│ + Semiring-graded !_r modality (à la mGL/Granule)       │
├─────────────────────────────────────────────────────────┤
│ + First-order quantifiers (as modal operators)          │
├─────────────────────────────────────────────────────────┤
│ = Foundation for quantitative multimodal linear logic   │
└─────────────────────────────────────────────────────────┘
```

### Research Gap

**No existing system combines:**
1. Display calculus formalism
2. Semiring-graded modalities
3. Multi-type/multimodal structure
4. First-order quantification

This is a potential **research contribution**.

---

## Sources

### Display Calculus Foundations
- [Belnap: Display Logic (1982)](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/display-logic/29A4BB22D89CF1E9D8EFA98B26E4D49F)
- [Restall: A Display Calculus for Classical Linear Logic (1991)](https://greg.restall.net//papers/dcll.html)

### Linear Logic
- [Greco & Palmigiano: Linear Logic Properly Displayed (ACM TOCL)](https://dl.acm.org/doi/10.1145/3570919)
- [Clouston et al.: Annotation-Free Sequent Calculi for FILL](https://arxiv.org/abs/1307.0289)
- [Dawson & Clouston: From Display Calculi to Deep Nested Sequent Calculi](https://link.springer.com/chapter/10.1007/978-3-662-44602-7_20)

### Multimodal & Multi-Type
- [Frittella et al.: Multi-type display calculus for dynamic epistemic logic](https://academic.oup.com/logcom/article-abstract/26/6/2017/2743523)
- [Academia.edu: Multi-type display calculus for PDL](https://www.academia.edu/35092418/Multi_type_display_calculus_for_Propositional_Dynamic_Logic)

### Graded/Quantitative
- [Orchard et al.: Quantitative Program Reasoning with Graded Modal Types (ICFP 2019)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- [Atkey: Syntax and Semantics of Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.html)
- [Moon et al.: Graded Modal Dependent Type Theory](https://link.springer.com/chapter/10.1007/978-3-030-72019-3_17)
- [A Mixed Linear and Graded Logic (CSL 2025)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2025.32)

### First-Order
- [First Order Logic Properly Displayed](https://www.researchgate.net/publication/351624115_First_order_logic_properly_displayed)

### Hypersequents
- [Wikipedia: Hypersequent](https://en.wikipedia.org/wiki/Hypersequent)
- [Ciabattoni et al.: Hypersequent and Display Calculi](https://link.springer.com/article/10.1007/s11225-014-9566-z)

---

*Last updated: 2026-01-25*
