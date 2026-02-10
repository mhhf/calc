---
title: "Proof Calculi Foundations: Deep Research"
created: 2026-02-10
modified: 2026-02-10
summary: Fundamental questions about proof calculi, Curry-Howard correspondence, hierarchy of proof systems from natural deduction to deep inference and cyclic proofs.
tags: [proof-theory, Curry-Howard, foundations, sequent-calculus, proof-systems]
---

# Proof Calculi Foundations: Deep Research

This document addresses fundamental questions about proof calculi, the Curry-Howard correspondence, and why certain proof formalisms work better for certain logics.

> **See also:** [[display-calculus]] for Belnap's conditions, [[residuation]] for Galois connections, [[logics-overview]] for expressibility survey, [[adjunctions-and-adjoint-logic]] for categorical perspective.

---

## Table of Contents

1. [Logic vs Type Theory: What's the Difference?](#logic-vs-type-theory-whats-the-difference)
2. [The Curry-Howard Correspondence](#the-curry-howard-correspondence)
3. [Why is Sequent Calculus "Good"?](#why-is-sequent-calculus-good)
4. [Why is Display Calculus Harder than Sequent Calculus?](#why-is-display-calculus-harder-than-sequent-calculus)
5. [Why Don't Graded Modalities Have Display Calculi Yet?](#why-dont-graded-modalities-have-display-calculi-yet)
6. [Why Do Some Logics Lack Sequent Calculi?](#why-do-some-logics-lack-sequent-calculi)
7. [The Hierarchy of Proof Systems](#the-hierarchy-of-proof-systems)
8. [Sources](#sources)

---

## Meta-Goal: Why Do Gentzen-Style Sequent Calculi Feel Significant?

**The question:** Beyond linear logic specifically, why does the Gentzen-style sequent calculus itself feel like "hidden knowledge"? What is it about this formalism that seems so fundamental?

**Possible reasons to investigate:**

1. **Symmetry and Duality**
   - Sequents make duality explicit: `Γ ⊢ Δ` shows both sides
   - Classical logic's symmetry becomes visible
   - Cut elimination reveals computational content on both sides

2. **Composition and Modularity**
   - Cut rule = composition of proofs
   - Proofs become first-class objects that can be combined
   - This is essentially the "API" of logical reasoning

3. **Resource Awareness Built-In**
   - The context management (what's on left/right) naturally tracks usage
   - Substructural logics fall out by restricting structural rules
   - This might be why it maps so well to computation and economics

4. **Proof Search = Computation**
   - Bottom-up proof search is a form of goal-directed computation
   - Focusing disciplines this into deterministic phases
   - This connects logic to programming in a deep way

5. **Universal Interface**
   - Many different logics can be expressed as sequent calculi
   - The "shape" of sequents is invariant; only rules change
   - Suggests sequents capture something fundamental about inference itself

**Questions to explore:**
- Is there a category-theoretic explanation for why sequents are "right"?
- How do sequent calculi relate to game semantics?
- Why did it take until Gentzen (1935) to discover this representation?
- What would a "more fundamental" representation look like, if one exists?

**Reading to pursue:**
- Girard's "Proofs and Types" — philosophical perspective
- Wadler's "Propositions as Sessions" — sequents and concurrency
- Game semantics literature — sequents as dialogue games

---

## Logic vs Type Theory: What's the Difference?

You're absolutely right that via Curry-Howard, "propositions as types, proofs as terms" means they're dual views of the same thing. So why do we distinguish them?

### The Short Answer

**They ARE the same thing mathematically, but they differ in:**
1. **Presentation style** (syntax)
2. **Primary focus** (what questions we ask)
3. **Operational interpretation** (what we do with them)

### The Longer Answer

| Aspect | Logic | Type Theory |
|--------|-------|-------------|
| **Primary objects** | Propositions, proofs | Types, terms (programs) |
| **Presentation** | Sequent calculus, natural deduction, Hilbert systems | Typing rules (natural deduction style) |
| **Key question** | "Is φ provable?" | "Does term t have type A?" |
| **Operational meaning** | Proof normalization | Computation (β-reduction) |
| **Structural rules** | Explicit (weakening, contraction, exchange) | Usually implicit in context |
| **Cut/substitution** | Cut rule | Substitution lemma |
| **Focus** | Proof existence & structure | Program typing & behavior |

### Why the Distinction Matters Practically

**Logic perspective:**
```
Γ ⊢ A ⊸ B    Δ ⊢ A
─────────────────────  (cut / modus ponens)
      Γ, Δ ⊢ B
```
We care: Can we eliminate the cut? What's the proof structure?

**Type theory perspective:**
```
Γ ⊢ f : A → B    Δ ⊢ a : A
────────────────────────────  (application)
      Γ, Δ ⊢ f a : B
```
We care: Does `f a` compute? What's the runtime behavior?

### The Deep Unity (Curry-Howard-Lambek)

The full correspondence is actually a **three-way isomorphism**:

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│     LOGIC       │     │  TYPE THEORY    │     │    CATEGORY     │
├─────────────────┤     ├─────────────────┤     ├─────────────────┤
│ Proposition     │ ↔   │ Type            │ ↔   │ Object          │
│ Proof           │ ↔   │ Term/Program    │ ↔   │ Morphism        │
│ Implication A→B │ ↔   │ Function type   │ ↔   │ Exponential B^A │
│ Conjunction A∧B │ ↔   │ Product type    │ ↔   │ Product A×B     │
│ Disjunction A∨B │ ↔   │ Sum type        │ ↔   │ Coproduct A+B   │
│ True            │ ↔   │ Unit type       │ ↔   │ Terminal object │
│ False           │ ↔   │ Empty type      │ ↔   │ Initial object  │
│ Cut elimination │ ↔   │ Computation     │ ↔   │ Composition     │
└─────────────────┘     └─────────────────┘     └─────────────────┘
```

### So Why Can't QTT Be "Displayed"?

**It CAN be, in principle!** The question is whether anyone has done the work:

1. **QTT is presented in natural deduction style** (typing rules)
2. **To make a display calculus**, you need to:
   - Translate to sequent calculus style
   - Add structural connectives for each logical connective
   - Define display postulates (residuation)
   - Verify Belnap's 8 conditions

**Why hasn't this been done for QTT?**
- QTT is relatively new (2016-2018)
- The community focuses on implementation (Idris 2) not proof theory
- Dependent types + semiring grading = complex interaction
- No one has needed it yet (the typing rules work fine for their purposes)

**Could you do it?** Yes! This would be a research contribution.

---

## The Curry-Howard Correspondence

### The Three Levels of Correspondence

**Level 1: Syntax**
```
Propositions ↔ Types
Proofs       ↔ Terms
```

**Level 2: Structure**
```
Proof rules      ↔ Typing rules
Proof tree       ↔ Derivation tree
Assumptions      ↔ Free variables
Discharged hyp.  ↔ Bound variables
```

**Level 3: Dynamics**
```
Cut elimination   ↔ β-reduction (computation)
Normal proofs     ↔ Normal forms (values)
Proof search      ↔ Type inhabitation
```

### Why Constructive Logic?

Curry-Howard works perfectly for **intuitionistic/constructive** logic because:
- A proof of `A → B` is a *method* to transform proofs of A into proofs of B
- This is exactly what a function `A → B` is!

For **classical logic**, it's trickier:
- Classical logic has `A ∨ ¬A` (excluded middle)
- This would mean: for any type, either it's inhabited or its negation is
- Computationally, this corresponds to **control operators** (call/cc, continuations)

### Linear Logic and Curry-Howard

Linear logic has a particularly clean Curry-Howard correspondence:

| Linear Logic | Linear Type Theory |
|--------------|-------------------|
| `A ⊗ B` | Tensor product (pair where both must be used) |
| `A ⊸ B` | Linear function (uses argument exactly once) |
| `A & B` | With (lazy pair, choose one) |
| `A ⊕ B` | Plus (tagged union) |
| `!A` | Of course (unlimited use, like `Box A`) |

This is why linear logic is so relevant to resource-aware programming!

### What Curry-Howard Doesn't Tell You

Curry-Howard gives an **isomorphism**, but it doesn't tell you:
1. Which **presentation** is best (sequent vs natural deduction vs Hilbert)
2. How to do **proof search** efficiently
3. How to handle **extensions** (modalities, quantifiers, etc.)

This is why we still care about proof theory separately from type theory!

---

## Why is Sequent Calculus "Good"?

### It's Not Just Cut Elimination!

Cut elimination and subformula property are consequences, not causes. The deeper reasons are:

### 1. Symmetric Treatment of Hypotheses and Conclusions

**Natural deduction:**
```
   [A]¹
    ⋮
    B
  ────── →I, 1
  A → B
```
Asymmetric: we "assume" A on top, "conclude" A → B on bottom.

**Sequent calculus:**
```
  Γ, A ⊢ B
  ──────────── →R
  Γ ⊢ A → B
```
Symmetric: both sides of ⊢ are explicit. We see the full context.

### 2. All Rules Are "Introduction Rules"

In sequent calculus, every rule **introduces** a connective on one side:
- Right rules introduce on the right (conclusion)
- Left rules introduce on the left (hypothesis)

In natural deduction, you have **introduction** AND **elimination** rules:
- Introduction: build up connectives
- Elimination: break down connectives

This asymmetry causes problems for proof search.

### 3. Uniform Bottom-Up Reading

**Natural deduction** has bi-directional information flow:
- Elimination rules flow information DOWN (deconstruction)
- Introduction rules flow information UP (construction)

**Sequent calculus** has uniform BOTTOM-UP reading:
- Every rule, read bottom-to-top, breaks the problem into subproblems
- This is exactly what proof search needs!

### 4. Structural Rules Are Explicit

In sequent calculus, structural rules (weakening, contraction, exchange) are explicit:

```
  Γ ⊢ Δ
  ─────────── weakening
  Γ, A ⊢ Δ

  Γ, A, A ⊢ Δ
  ─────────── contraction
  Γ, A ⊢ Δ
```

This explicitness is crucial for:
- Substructural logics (linear logic restricts these rules)
- Understanding proof complexity
- Analyzing cut elimination

### 5. Cut Elimination = Composition is Admissible

The cut rule:
```
  Γ ⊢ A    A, Δ ⊢ C
  ──────────────────── cut
       Γ, Δ ⊢ C
```

Says: "If I can prove A, and I can use A to prove C, then I can prove C directly."

Cut elimination says: **You don't need this rule.** Any proof using cut can be transformed into a cut-free proof.

**Why this matters:**
1. **Subformula property**: Cut-free proofs only contain subformulas of the goal
2. **Proof search terminates**: The search space is bounded
3. **Consistency**: If you can prove `⊥`, cut-free, then... you can't (there's no rule for it)

### 6. The Price: Proof Identity

The downside of sequent calculus is that different proofs can represent the "same" mathematical proof:

```
  A ⊢ A    B ⊢ B           B ⊢ B    A ⊢ A
  ───────────────── ∧R     ───────────────── ∧R
    A, B ⊢ A ∧ B             B, A ⊢ A ∧ B
```

These are "different" sequent proofs but "the same" proof mathematically. This is the "bureaucracy" problem that proof nets solve.

---

## Why is Display Calculus Harder than Sequent Calculus?

### Display Calculus Has Additional Requirements

| Requirement | Sequent Calculus | Display Calculus |
|-------------|------------------|------------------|
| Antecedent/succedent structure | Multisets or lists | **Structured terms** with structural connectives |
| Logical rules | L/R rules for each connective | L/R rules **plus** structural counterparts |
| Structural rules | Weakening, contraction, exchange | **Display postulates** (residuation rules) |
| Cut elimination | Prove per-logic | **Generic** if C1-C8 satisfied |
| Formula accessibility | Direct (multiset access) | Must **display** formula first |

### The Display Property

The key requirement is the **display property**:

> Any substructure can be "displayed" as the entire antecedent or succedent using only structural rules.

**Example:** Given `(A, B), C ⊢ D`, we can display `B`:
```
(A, B), C ⊢ D
───────────── associativity
A, (B, C) ⊢ D
───────────── residuation
B, C ⊢ A > D
───────────── associativity
B ⊢ C > (A > D)
```

Now `B` is "displayed" as the entire antecedent.

### Why This Is Harder

**1. You need structural connectives:**

For every logical connective, you need a structural counterpart:

| Logical | Structural | Meaning |
|---------|------------|---------|
| A ⊗ B | X , Y | Both resources together |
| A ⊸ B | X > Y | If X then Y (hypothetical) |
| A ⅋ B | X ; Y | Par structure |
| 1 | I | Empty resource |

**2. You need residuation (Galois connection):**

Connectives must come in **residuated pairs**:
```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C   iff   B ⊢ C ○─ A
```

This is a strong constraint! Not all connectives have residuals.

**3. Belnap's 8 conditions must be satisfied:**

| Condition | What It Requires |
|-----------|-----------------|
| C1 | Formulas in premises are subformulas of conclusion |
| C2 | Congruent parameters are shape-alike |
| C3 | Each parameter maps to ≤1 thing in conclusion |
| C4 | Parameters preserve antecedent/succedent position |
| C5 | Principal formula is displayable |
| C6 | Rules are closed under substitution |
| C7 | Matching principals can be cut-reduced |
| C8 | Cut reduction preserves structure |

**4. Exponentials are problematic:**

The exponentials `!` and `?` are NOT residuated in the usual sense. From "Linear Logic Properly Displayed":

> "If structural counterparts for exponentials were allowed... the resulting calculus would lose the display property... Belnap is forced to give up on the full enforcement of design principles."

This is why it took until 2023 to get a **proper** display calculus for linear logic with exponentials!

### The Payoff

If you satisfy all these requirements, you get:

1. **Generic cut elimination**: One proof works for all proper display calculi
2. **Modularity**: Add new connectives without breaking cut elimination
3. **Uniformity**: Same framework for many different logics

---

## Why Don't Graded Modalities Have Display Calculi Yet?

### The Specific Challenges

**1. The exponential problem, squared:**

Graded modalities `!_r` generalize the exponential `!`:
- `!` = "unlimited use"
- `!_r` = "use r times" (where r is from a semiring)

The exponential already causes problems for display calculus. Adding semiring indexing adds:
- Infinitely many modalities (one for each semiring element)
- Algebraic constraints (r + s, r × s must make sense)
- Context operations scaled by grades

**2. Residuation for graded modalities:**

What is the residual of `!_r`?

For plain `!`, there's a complex dance with `?`. For `!_r`, you'd need:
- A graded dual `?_r`
- Residuation laws that respect the semiring structure
- Display postulates that work with grades

**3. No one has needed it yet:**

The Granule team focuses on:
- Type checking (not proof search)
- Natural deduction style (typing rules)
- Implementation (the Granule language)

Display calculus is about **proof search** and **cut elimination**. If you're just type-checking programs, you don't need it.

**4. It's probably possible:**

The methodology exists:
- "Linear Logic Properly Displayed" shows how to handle exponentials properly
- Multi-type display calculus shows how to handle indexed families
- Someone just needs to combine them

**This could be your research contribution!**

---

## Why Do Some Logics Lack Sequent Calculi?

### Not All Logics Fit the Sequent Mold

**Matching Logic** is a good example. It has a Hilbert-style proof system but:

> "Using a Hilbert-style system for interactive reasoning is challenging—even more so in ML, which lacks a general deduction theorem."

They recently developed a sequent calculus for it, but it wasn't obvious how.

### Reasons a Logic Might Lack a (Good) Sequent Calculus

**1. No clear left/right decomposition:**

Sequent calculus relies on breaking down the goal into subgoals via left/right rules. Some connectives don't decompose nicely.

**2. Non-determinism in cut elimination:**

> "Cut-elimination for classical sequent calculus is known to have non-deterministic behaviour."

Some logics have so much non-determinism that cut elimination doesn't give a unique normal form.

**3. Contraction causes explosion:**

> "In his essay 'Don't Eliminate Cut!' George Boolos demonstrated that there was a derivation that could be completed in a page using cut, but whose analytic proof could not be completed in the lifespan of the universe."

If cut elimination causes super-exponential blowup, the sequent calculus is impractical.

**4. Context-sensitivity:**

Some logics have rules that depend on the **entire context**, not just the principal formula. These don't fit the sequent calculus pattern well.

**5. Fixpoints and recursion:**

Logics with fixpoints (like μ-calculus) require special techniques:
- Infinitary proof systems
- Cyclic proofs
- Annotations for termination

### Examples

| Logic | Sequent Calculus Status |
|-------|------------------------|
| Classical propositional | ✅ Yes (multiple variants) |
| Intuitionistic propositional | ✅ Yes |
| Classical first-order | ✅ Yes |
| Linear logic | ✅ Yes |
| S5 modal logic | ⚠️ Needs hypersequents |
| Temporal logic (LTL, CTL) | ⚠️ Needs extensions |
| Matching logic | ⚠️ Recently developed, non-trivial |
| Higher-order logic | ⚠️ Complex, needs care |
| μ-calculus | ⚠️ Needs cyclic proofs or annotations |

---

## The Hierarchy of Proof Systems

### Expressiveness Hierarchy

```
Hilbert systems
      ↓ (more structure)
Natural deduction
      ↓ (explicit contexts)
Sequent calculus
      ↓ (multiple sequents)
Hypersequent calculus
      ↓ (nested structure)
Nested sequent calculus
      ↓ (display property)
Display calculus ≈ Labelled sequent calculus
      ↓ (beyond tree-structured proofs)
Deep Inference / Cyclic Proofs / Proof Nets
```

### What Each Level Adds

| System | Key Feature | Good For |
|--------|-------------|----------|
| **Hilbert** | Minimal axioms + modus ponens | Metatheory, independence proofs |
| **Natural deduction** | Assumptions, intro/elim rules | Human reasoning, type theory |
| **Sequent calculus** | Explicit contexts, cut rule | Proof search, subformula property |
| **Hypersequent** | Multiple sequents | S5, Gödel logics |
| **Nested sequent** | Sequents inside sequents | Modal logics, tense logics |
| **Display** | Structural connectives, display property | Modal logics, substructural logics |
| **Labelled** | Explicit worlds/labels | Most general, any Kripke semantics |
| **Deep inference** | Rules apply anywhere in formula | Symmetry, fine-grained analysis |
| **Cyclic proofs** | Non-wellfounded graphs | μ-calculus, induction, fixpoints |
| **Proof nets** | Geometric/graph representation | Linear logic, proof identity |

### Trade-offs

| System | Proof Search | Cut Elimination | Expressiveness | Complexity |
|--------|--------------|-----------------|----------------|------------|
| Hilbert | Bad | N/A | Low | Low |
| Natural deduction | Medium | Normalization | Medium | Medium |
| Sequent | Good | Yes (per-logic) | Medium | Medium |
| Hypersequent | Good | Yes | High | High |
| Display | Medium* | Generic! | Very High | High |
| Deep inference | Hard** | Yes (dual to identity) | Very High | High |
| Cyclic proofs | Specialized | Global trace condition | Highest (fixpoints) | Very High |
| Proof nets | N/A*** | Local rewrites | High | Medium |

*Display calculus proof search can be inefficient due to display postulates.
**Deep inference: rules can apply anywhere, making search space larger.
***Proof nets are representations, not proof search systems.

---

## Beyond Display/Labelled: Advanced Proof Systems

The top of the hierarchy contains three orthogonal approaches that solve different problems:

### Deep Inference

**What it is:** Rules apply at any depth inside a formula, not just at the root.

**Key insight:** In sequent calculus, rules only apply to the "main connective" of a formula. Deep inference removes this restriction.

```
Standard sequent:     A ⊗ B ⊢ C   (can only decompose ⊗ at top level)
Deep inference:       ... (A ⊗ B) ... ⊢ ... (can apply inside any context)
```

**Why it's more expressive:**
- Cut and identity become perfectly dual (symmetric)
- Some logics easier to express (certain modal logics)
- Finer-grained proof analysis

**Challenges:**
- Proof search harder to control (rules apply everywhere)
- Cut elimination proofs more involved
- Less mature tooling

**Relevance for CALC:** LOW-MEDIUM. Deep inference doesn't add expressiveness we specifically need for authorization/ownership modalities. The multimodal work we care about uses other approaches.

**Sources:**
- [Guglielmi: Deep Inference](http://alessio.guglielmi.name/res/cos/)
- [Proof Theory Blog: Non-sequent systems](https://prooftheory.blog/2021/08/23/new-results-about-logics-using-proof-systems-other-than-sequent-calculus/)

---

### Cyclic Proofs

**What it is:** Non-wellfounded proofs represented as finite graphs instead of trees.

**Key insight:** Standard proofs are trees (finite, well-founded). Cyclic proofs allow "back-edges" that create cycles, with a **global trace condition** ensuring soundness.

```
Tree proof:           Linear structure, finite depth
Cyclic proof:         Graph structure, may have cycles (but finite nodes)
```

**Why it's more expressive:**
- Essential for **fixpoints** and **inductive definitions**
- μ-calculus (least/greatest fixpoints) requires cyclic proofs
- Berardi & Tatsuta proved: cyclic and inductive proof systems **do not prove the same theorems** — cyclic can prove more

**What needs cyclic proofs:**
- μ-calculus (modal logic with fixpoints)
- Inductive predicates in verification
- Recursive data types
- "Valid blockchain state" as inductive definition

**Relevance for CALC:** MEDIUM-HIGH (for future). If we model:
- Recursive smart contracts
- Transaction histories as inductive structures
- "Eventually consistent" properties
Then cyclic proofs become relevant.

For our **current goals** (ownership modalities, authorization), cyclic proofs are not needed. Keep on radar for Phase 2.

**Sources:**
- [Cyclic Proofs for First-Order μ-Calculus](https://academic.oup.com/jigpal/article/32/1/1/6653082)
- [Looping for Good: Cyclic Proofs for Security Protocols](https://zenodo.org/records/16992323) — Tamarin Prover integration
- [Cyclic Proofs for Arithmetical Inductive Definitions](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2023.27)

---

### Proof Nets

**What it is:** Geometric/graph representation of proofs that eliminates "bureaucracy" — irrelevant syntactical differences between equivalent proofs.

**Key insight:** Two sequent proofs differing only in rule order become the **same** proof net. Proof nets capture **proof identity**.

```
Sequent proof 1:      Apply ∧R then ⊗L     ]
                                           ] Same proof net
Sequent proof 2:      Apply ⊗L then ∧R     ]
```

**Connection to Geometry of Interaction:**
Proof nets lead to Girard's "Geometry of Interaction" — a dynamic semantics where proof normalization becomes token-passing in graphs. This connects to optimal λ-calculus reduction.

**The multimodal problem:**
> "Proof nets are hard for multimodalities."

Proof nets work beautifully for **pure linear logic** (MALL, MELL), but extending them to modal/multimodal logics is problematic:
- Correctness criteria become complex
- Multiple modalities require additional structure
- No consensus on "right" approach

**Relevance for CALC:** LOW. We need multimodal logics for ownership/authorization. Proof nets are not the right tool.

**Sources:**
- [nLab: proof net](https://ncatlab.org/nlab/show/proof+net)
- [Wikipedia: Proof net](https://en.wikipedia.org/wiki/Proof_net)
- [Wikipedia: Geometry of interaction](https://en.wikipedia.org/wiki/Geometry_of_interaction)

---

### Summary: Which Advanced System for CALC?

| System | Our Need | Relevance | When to Use |
|--------|----------|-----------|-------------|
| **Deep Inference** | Structural flexibility | LOW | Not needed for our goals |
| **Cyclic Proofs** | Fixpoints, recursion | MEDIUM (future) | If modeling recursive contracts |
| **Proof Nets** | Proof identity | LOW | Bad for multimodal logics |
| **Multi-Type DC** | Ownership, authorization | HIGH | Primary approach |
| **Labelled Sequents** | Complex mode relations | MEDIUM | Backup if MTDC insufficient |

**Recommendation:** Stick with Multi-Type Display Calculus for multimodal authorization logic. Consider cyclic proofs later if we need inductive definitions.

---

## Key Insights Summary

### 1. Logic vs Type Theory

**Same mathematical content, different presentations.**
- Logic: focuses on provability, proof structure, proof search
- Type theory: focuses on typing programs, computation, implementation

### 2. Why Sequent Calculus is Good

**Uniform bottom-up reading + explicit structural rules + cut elimination.**
- Makes proof search systematic
- Subformula property bounds search space
- Structural rules explicit → easy to control (for substructural logics)

### 3. Why Display Calculus is Harder

**Requires structural connectives + residuation + display property + 8 conditions.**
- More machinery to set up
- But payoff is generic cut elimination
- Exponentials are particularly tricky

### 4. Why Graded Modalities Lack Display Calculi

**Exponentials are already hard; grading adds semiring structure.**
- No one has needed it (focus is on type checking, not proof search)
- The methodology exists; someone needs to do the work
- Potential research contribution!

### 5. Why Some Logics Lack Sequent Calculi

**Not all connectives decompose into left/right rules nicely.**
- Context-sensitivity
- Fixpoints require special techniques
- Non-determinism in cut elimination
- Proof size explosion

---

## Sources

### Curry-Howard
- [Curry-Howard correspondence - Wikipedia](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
- [Wadler: Propositions as Types](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)
- [Curry-Howard-Lambek - HaskellWiki](https://wiki.haskell.org/Curry-Howard-Lambek_correspondence)
- [nLab: propositions as types](https://ncatlab.org/nlab/show/propositions+as+types)

### Sequent Calculus
- [Sequent calculus - Wikipedia](https://en.wikipedia.org/wiki/Sequent_calculus)
- [Pfenning: Sequent Calculus (CMU)](https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf)
- [nLab: sequent calculus](https://ncatlab.org/nlab/show/sequent+calculus)
- [Fiveable: Comparison of natural deduction and sequent calculus](https://fiveable.me/proof-theory/unit-4/comparison-natural-deduction-sequent-calculus/study-guide/AoRA6mqmIJ7ar3Hk)

### Display Calculus
- [Belnap: Display Logic (1982)](https://link.springer.com/article/10.1007/BF00284976)
- [nLab: display logic](https://ncatlab.org/nlab/show/display+logic)
- [Restall: Display Logic and Gaggle Theory](https://consequently.org/papers/dggl.pdf)
- [Ciabattoni: Hypersequent and Display Calculi](https://link.springer.com/article/10.1007/s11225-014-9566-z)
- [Greco & Palmigiano: Linear Logic Properly Displayed](https://dl.acm.org/doi/10.1145/3570919)

### Cut Elimination
- [Cut-elimination theorem - Wikipedia](https://en.wikipedia.org/wiki/Cut-elimination_theorem)
- [Pfenning: Cut Elimination (CMU)](https://www.cs.cmu.edu/~fp/courses/15317-f09/lectures/10-cutelim.pdf)
- [The Proof Theory Blog: Simple proofs of cut-elimination](https://prooftheory.blog/2020/05/07/simpler-proofs-of-cut-elimination-i-classical-logic/)

### Type Theory
- [nLab: type theory](https://ncatlab.org/nlab/show/type+theory)
- [Stanford Encyclopedia: Type Theory](https://plato.stanford.edu/entries/type-theory/)
- [Stanford Encyclopedia: Intuitionistic Type Theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/)

### Matching Logic
- [Matching Logic Official Site](http://www.matching-logic.org/)
- [Chen, Lucanu, Roșu: Matching Logic Explained](https://www.sciencedirect.com/science/article/pii/S2352220821000018)
- [Interactive Matching Logic Proofs in Coq](https://link.springer.com/chapter/10.1007/978-3-031-47963-2_10)

---

*Last updated: 2026-01-25*
