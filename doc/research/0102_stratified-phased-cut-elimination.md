---
title: "Stratified and Phased Cut Elimination — Literature Survey"
created: 2026-04-01
modified: 2026-04-01
summary: "Survey of all known work related to 'stratified cut elimination' — cut elimination that proceeds level-by-level, mode-by-mode, or stage-by-stage based on a classification of the cut formula. Covers SELL, adjoint logic, staged computation (Davies-Pfenning, temporal logic), light logics, NbE, and proof assistants. Assesses novelty of the general theorem."
tags: [cut-elimination, proof-theory, staging, sequent-calculus, subexponentials, SELL, adjoint-logic, modal-logic, Curry-Howard, normalization-by-evaluation, linear-logic, complexity, light-logic, stratification]
category: "Proof Theory"
---

# Stratified and Phased Cut Elimination — Literature Survey

**The central question:** Has anyone explicitly stated "cut elimination stratified by formula grade" as a formal theorem — where cuts are classified and eliminated level-by-level based on some preorder on the cut formula?

The answer: **not as a single unified theorem**. There are several bodies of work that each capture a fragment of this idea, but they are framed differently and no paper unifies them under the heading "phased cut elimination" or "stratified cut elimination."

---

## 1. Standard Cut Elimination: The Complexity Measure

Every proof of cut elimination uses a measure on the cut formula (degree, grade, complexity). In Gentzen's original proof for LK/LJ:

- The **degree** of a proof is the maximum degree of any cut formula, where degree(A) = number of connectives in A.
- The proof proceeds by: reduce the degree of the topmost (highest-degree) cut first, using key cases where the cut formula is **principal** in both premises.
- Inner cuts created during principal cut reduction have strictly smaller degree.

This is an implicit stratification by formula degree. But it is not presented as "level-by-level elimination" — it is an induction used to prove termination. The cut-elimination procedure is not required to run all degree-k cuts before degree-(k+1) cuts; the induction just shows the procedure terminates regardless of order.

**Pfenning's structural cut elimination** (1994, CMU-CS-94-212; Inf. & Comp. 2000) is particularly relevant: for linear logic with exponentials, the induction is on the **structure of A** (the cut formula), with sub-inductions on derivation heights. Exponential cuts (`!A`) are structurally larger than the sub-formula `A`, so they are reduced after cuts on `A`. This is an implicit stratification: exponential cuts are "outer," non-exponential cuts are "inner." But Pfenning does not name this stratification or present it as a theorem about phases.

**Key reference:** Pfenning, "Structural Cut Elimination in Linear Logic," CMU-CS-94-212 (1994); published in Inf. & Comp. 157 (2000).
URL: https://www.cs.cmu.edu/~fp/papers/ic00.pdf

---

## 2. Light Logics: Explicit Stratification by Level

This is the closest body of work to "stratified cut elimination" as an explicit theorem.

### Girard's Light Linear Logic (1998)

Girard introduced **Light Linear Logic** (LLL) and **Light Affine Logic** (LAL) where proof stratification — assigning each formula a **depth** or **level** — is a first-class structural constraint. The *paragraph* modality `§` marks a "level change." Rules are constrained so that no cut can collapse levels.

The key result: **cut elimination in LAL runs in polynomial time** in the size of the proof. This is a stratification theorem: cuts at each level can only interact with cuts at the same or lower levels, preventing the exponential blowup that occurs in standard linear logic.

### Baillot and Mazza: Linear Logic by Levels (arXiv:0801.1253, TCS 2010)

Baillot and Mazza generalize Girard's stratification. Instead of depth in proof nets, they use an explicit **level index** on formulas and sequents. Their main theorem:

> Cut elimination is sound for level-indexed proofs, and the cut-elimination procedure respects the level structure: a cut at level k is reduced by cases that only introduce cuts at level ≤ k.

This is an **explicit stratification theorem for cut elimination**, with the stratification being the level index. However, it is motivated by complexity (polynomial-time cut elimination = polytime computation), not by staged computation or phased normalization. The levels are about resource depth, not computation stages.

**"An Abstract Approach to Stratification in Linear Logic"** (Baillot, Mazza; arXiv:1206.6504, IC 2015): generalizes the level-indexed approach to an abstract modality that subsumes both Girard's `§` (LLL) and Lafont's soft exponential (SLL). They give a general theorem: any logic satisfying certain abstract stratification conditions admits polynomial-time cut elimination.

**This is the most explicit statement of "stratified cut elimination" in the literature.** The levels are a complexity measure, not a staging mechanism.

**Key references:**
- Baillot, Mazza, "Linear Logic by Levels and Bounded Time Complexity," TCS 408(1) (2009). arXiv:0801.1253.
- Baillot, Mazza, "An Abstract Approach to Stratification in Linear Logic," IC 239 (2015). arXiv:1206.6504.

---

## 3. SELL (Subexponential Linear Logic): Stratum-by-Stratum?

SELL (Danos-Joinet-Schellinx 1993; Nigam-Miller PPDP 2009) replaces `!` with a family `!_a` indexed by a preorder `⟨I, ≤, W, C⟩`. The preorder imposes constraints on the promotion rule: `!_a A` can only be formed when all hypotheses are at levels `≤ a`.

**Does SELL cut elimination proceed stratum-by-stratum?**

The SELL cut elimination proof (Nigam-Miller, PPDP 2009; also Kanovich-Kuznetsov-Nigam-Scedrov, MSCS 2019) does use the preorder on labels as a structural constraint in the proof. Specifically:

- The promotion rule's side condition (`all hypotheses ≤ a`) is preserved through cut reduction.
- Cuts on `!_a A` reduce to cuts on `A` (at level a) and cuts on formulas passed through the promotion rule (at levels ≤ a).

However, the SELL cut elimination paper does **not** state a theorem of the form "cuts at level a are eliminated before cuts at level b > a." The proof proceeds by simultaneous structural induction, not phase-by-phase. The stratification is implicit in the structure of the induction, not an explicit theorem about reduction order.

**No paper states "SELL cut elimination proceeds stratum-by-stratum" as an explicit theorem.**

**Key reference:**
- Nigam, Miller, "Algorithmic Specifications in Linear Logic with Subexponentials," PPDP 2009. DOI: 10.1145/1599410.1599427.

---

## 4. Adjoint Logic: Mode-by-Mode?

Adjoint logic (Pruiksma-Chargin-Pfenning-Reed, 2018 tech report; Pruiksma PhD thesis CMU-CS-24-103, 2024) is parameterized by a preorder of modes, each with structural properties.

Cut elimination in adjoint logic is proved by Pruiksma using **admissibility of multicut**, following Gentzen's "Mischung" style. The proof proceeds by nested induction on the proposition and derivation structure.

**Does it proceed mode-by-mode?** The available evidence says: **no, it is interleaved**. The proof uses simultaneous structural induction. The mode preorder appears as a side condition in the promotion/shift rules (a proof of `A` at mode `m` can only depend on hypotheses at modes `≤ m`), and this is preserved inductively, but there is no explicit "eliminate all cuts at mode m before mode m'" phase structure.

Pruiksma's 2024 thesis does not describe a mode-ordered cut elimination procedure; the result is that cut is admissible (can be eliminated), full stop.

**Key reference:**
- Pruiksma, "Adjoint Logic with Applications," PhD thesis CMU-CS-24-103 (2024). URL: https://csd.cs.cmu.edu/sites/default/files/phd-thesis/CMU-CS-24-103.pdf

---

## 5. Davies-Pfenning Modal Logic S4 and Staged Computation

Davies and Pfenning, "A Modal Analysis of Staged Computation," JACM 2001 (POPL 1996 preliminary) is the canonical reference for staging via modal logic S4.

Their system uses `□A` (box A) for compile-time code and `◇A` / `A` for runtime code. The Curry-Howard reading: `□A` is a compile-time program of type `A`, and a closed term of type `□A` can be "run" at compile time.

**Cut elimination for this system** (analyzed by Goubault-Larrecq, "On Computational Interpretations of S4, Part I: Cut Elimination," INRIA RR-2934, 1996) shows that the cut-elimination procedure corresponds to β-reduction in the staged lambda calculus. Goubault-Larrecq analyzes the principal cuts involving `□`:

- A principal cut on `□A` (box elimination applied to a box introduction) reduces to a substitution, where the substituted term is a compile-time program.
- This corresponds to **evaluating the compile-time computation at compile time**.

However, Goubault-Larrecq does **not** state a theorem of the form "cuts on `□A` are eliminated before cuts on non-modal formulas." The proof proceeds by simultaneous induction. The staging correspondence is in the semantics (via Curry-Howard), not in the reduction order of cut elimination.

Davies and Pfenning themselves state that reductions in their λ-calculus can be done "in an order corresponding to stages" but this is an observation about the semantics (stage-0 reductions are compile-time), not a proof-theoretic cut elimination theorem.

**What Davies 1996 (temporal logic, LICS 1996) explicitly states:**
Rowan Davies, "A Temporal Logic Approach to Binding-Time Analysis," LICS 1996 (later JACM 2017), introduces the "next" operator `○A` from linear-time temporal logic as the type of stage-n+1 code. He states explicitly: "Normalization in λ° can be done in an order corresponding to the times in the logic." This is the clearest statement of **phased normalization by stage order** in the lambda calculus (= cut elimination) literature. But it is stated as a property of the normalization procedure, not as a named theorem about "phases."

**Key references:**
- Davies, Pfenning, "A Modal Analysis of Staged Computation," JACM 48(3) (2001). URL: https://www.cs.cmu.edu/~fp/papers/jacm00.pdf
- Davies, "A Temporal Logic Approach to Binding-Time Analysis," LICS 1996 / JACM 64(1) (2017). URL: https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf
- Goubault-Larrecq, "On Computational Interpretations of the Modal Logic S4, I: Cut Elimination," INRIA RR-2934 (1996). Semantic Scholar: https://www.semanticscholar.org/paper/On-computational-interpretations-of-the-modal-logic-Goubault-Larrecq/cf79f343cd76da7022a1dadcb68e49470d0843c0

---

## 6. Normalization by Evaluation (NbE): Two Phases

NbE (Berger-Schwichtenberg 1991; Dybjer, Abel, and many others) normalizes terms by:

1. **Evaluation (reflection):** Map syntax to a semantic domain `⟦-⟧` (this runs all eliminable cuts).
2. **Reification:** Extract a canonical syntactic normal form from the semantic value.

This is an implicit two-phase procedure: all reductions happen in phase 1 (the semantic evaluation), and phase 2 is pure extraction. From the proof-theoretic angle, this corresponds to:

1. Phase 1: eliminate all cuts by semantic evaluation (all β-reductions happen here).
2. Phase 2: read back a cut-free normal form.

However, the "two-phase" structure of NbE is **the normalization procedure itself**, not a theorem about which cuts are eliminated first. Specifically, all cuts are eliminated simultaneously in the semantic evaluation — there is no ordering by formula grade.

NbE for **modal dependent type theory** (Kavvos, Abel; JFP 2020) extends NbE to systems with `□` modality. The modal NbE has the property that `□`-computations are computed in the semantic domain before non-modal computations are extracted. This is structurally similar to staged compilation. But again, this is not stated as "cuts are eliminated in modal-order."

Abel's habilitation thesis, "Normalization by Evaluation: Dependent Types and Impredicativity" (2013), surveys NbE for dependent type theory extensively. The connection to cut elimination is discussed (NbE correctness implies normalization = cut elimination), but stratification by formula grade is not a theme.

**Key references:**
- Abel, "Normalization by Evaluation: Dependent Types and Impredicativity," habilitation thesis, LMU Munich (2013). URL: https://www.cse.chalmers.se/~abela/habil.pdf
- Kavvos, Abel, "Normalization by Evaluation for Modal Dependent Type Theory," JFP 30 (2020).

---

## 7. Two-Level Type Theory (2LTT) and Staged Compilation

Kovács, "Staged Compilation with Two-Level Type Theory," POPL 2023 / PACMPL (2022). arXiv:2209.09729.

2LTT has two levels: a **meta level** (compile-time) and an **object level** (runtime). Staging-by-evaluation (analogous to NbE) is used: the meta-level is evaluated fully before object-level code is generated.

Kovács proves:
- **Soundness:** Meta-level computation is safe to run at compile time.
- **Conservativity:** The full 2LTT is conservative over the object-level type theory alone.

The staging algorithm ("staging-by-evaluation") proceeds in two phases corresponding exactly to the two levels. This is the cleanest **phased normalization theorem** in the recent literature: phase 1 = eliminate all meta-level cuts; phase 2 = the object-level program is already in normal form.

However, this is framed as a property of the **staging algorithm** (a specific normalization strategy), not as a general theorem about cut elimination in 2LTT. The paper does not state it as "cut elimination stratified by level."

**This is essentially the theorem being asked about**, but stated operationally (as a staging algorithm with soundness/conservativity) rather than proof-theoretically (as "cut elimination proceeds level-by-level").

**Key reference:**
- Kovács, "Staged Compilation with Two-Level Type Theory," POPL 2023. arXiv:2209.09729. URL: https://arxiv.org/abs/2209.09729

---

## 8. Bounded Linear Logic (BLL): Grade-Indexed Cut

BLL (Girard, Scedrov, Scott, TCS 1992) annotates the exponential with a natural number grade: `!_n A` means "A usable at most n times." Cut elimination in BLL has the property that cuts on `!_n A` reduce to at most n copies of cuts on `A`. The grade bounds the duplication during cut elimination, giving polynomial-time normalization.

BLL is the **earliest graded modality for linear logic** (1992). The grade is a bound on the exponential, and cut elimination respects the grade: eliminating a `!_n` cut produces sub-problems involving grades ≤ n. This is an implicit stratification by grade but not an explicit "grade-by-grade elimination" theorem.

**Key reference:**
- Girard, Scedrov, Scott, "Bounded Linear Logic: A Modular Approach to Polynomial Time Computability," TCS 97(1) (1992). DOI: 10.1016/0304-3975(92)90386-T.

---

## 9. Principal Cut Order and "Static Cuts First"

In standard cut elimination, the reduction from a non-principal cut to a principal cut is called a **rank reduction** (permuting the cut up through non-cut rules). Once the cut is principal (the cut formula is the main connective in both premises), it can be reduced to smaller cuts.

The question "can we eliminate static cuts first" is equivalent to: can we order cut reductions so that cuts on "static" (compile-time) formulas are reduced before "dynamic" (runtime) cuts?

For **confluent** cut elimination systems (where the order doesn't matter), this is trivially possible: any reduction order reaches the same normal form. For non-confluent systems (e.g., classical logic), the order matters.

For ILL: cut elimination is confluent (the normal form is unique up to formula equivalence). Therefore, one can always choose to eliminate "static" cuts first — but this is not a theorem, it is a scheduling choice enabled by confluence.

**No paper in the proof theory literature states "eliminate static/grade-0 cuts first" as a theorem with a name.**

---

## 10. Definitional Equality in Proof Assistants (Coq/Agda)

In Coq (CIC) and Agda (MLTT), definitional equality is closed under beta-reduction. From the proof-theoretic perspective, type checking applies beta-reduction (= cut elimination) during unification.

The "compile-time vs. runtime" cut distinction corresponds informally to:
- **Type-level reductions:** beta-reductions that occur during type checking (these are always compile-time).
- **Extraction-time reductions:** beta-reductions that occur during program extraction (Coq's `Extraction` tactic).
- **Runtime reductions:** beta-reductions during execution of the extracted program.

There is **no formal account** in the Coq or Agda literature of "which cuts are type-level vs. computation-level" as a stratified cut elimination theorem. The distinction exists operationally (type-checker vs. extracted code), but is not presented as a named proof-theoretic result.

The closest work is Atkey's "Polynomial Time and Dependent Types" (POPL 2023/2024, arXiv:2307.09145), which uses QTT to ensure type-level computation is unrestricted while term-level computation is polynomial-time bounded — effectively a two-stratum cut elimination (type level = unrestricted, term level = bounded). But this is presented as a type-theoretic result, not a proof-theoretic one.

---

## 11. Summary: What Exists vs. What Is Novel

### What exists (named theorems or explicit procedures)

| Work | What it says | Framing |
|---|---|---|
| Baillot-Mazza (2009, 2015) | Cut elimination respects level indices; polynomial-time if levels are bounded | Complexity theorem for light logics |
| Davies (1996) | Normalization can be done in stage order (temporal logic approach) | Observation about normalization order |
| Kovács 2LTT (2022) | Staging algorithm: eliminate meta-level first, then object-level (soundness + conservativity) | Staging algorithm correctness |
| Girard BLL (1992) | Cuts on `!_n A` produce ≤ n copies; grade-bounded cut elimination | Complexity bound (polytime) |
| Pfenning (1994/2000) | Exponential cuts structurally larger than sub-formulas; induction terminates | Termination of cut elimination in ILL |
| SELL (Nigam-Miller 2009) | Promotion respects preorder; cut elimination preserves it | Admissibility theorem (not ordered) |
| Adjoint logic (Pruiksma 2024) | Cut admissible for all modes simultaneously | Admissibility theorem (not ordered) |
| NbE modal (Kavvos-Abel 2020) | □-computations evaluated in semantic phase before reification | Normalization procedure (not cut theorem) |

### What does NOT exist (the novel claim)

**No paper states the following as a named theorem:**

> **Stratified Cut Elimination Theorem:** Let the cut formulas be classified by a preorder (grade, level, stratum, mode). Then cut elimination can be performed phase-by-phase: for each level l in increasing order, all cuts on formulas at level l are eliminated before cuts at level l' > l. The resulting intermediate proofs are cut-free at levels < l at each phase boundary.

This is novel because:

1. The existing stratified results (Baillot-Mazza, light logics) use stratification to bound the **cost** of cut elimination, not to define a **phase structure** for the procedure.
2. The staging correspondence (Davies-Pfenning, Kovács 2LTT) establishes phased normalization for the **lambda calculus** (β-reduction), not for cut elimination in a sequent calculus as a named proof-theoretic theorem.
3. SELL and adjoint logic prove cut admissibility by simultaneous induction; the preorder is a constraint on proofs, not a phase structure for the elimination procedure.
4. NbE's two phases (evaluate/reify) correspond to "all cuts at once" (semantic evaluation) + "read back," not to stratified cuts at different levels.

### The closest existing statement

Davies 1996 ("Normalization in λ° can be done in an order corresponding to the times in the logic") is the closest but:
- Is about lambda calculus (β-reduction), not sequent calculus (cut elimination)
- Is stated as an observation, not a named theorem
- Only covers two levels (stages), not an arbitrary preorder

Kovács 2LTT is the closest **algorithmic** result (two-phase staging = two-level normalization), but is framed as a staging algorithm with soundness/conservativity, not as a proof-theoretic cut elimination theorem.

---

## 12. The Proof-Theoretic Analog: What the Theorem Would Say

For CALC's purposes, the theorem would take the following form for SELL or adjoint logic:

**Theorem (Stratified Cut Elimination for SELL):**
Let Σ = ⟨I, ≤, W, C⟩ be a subexponential signature. A SELL proof with cuts can be reduced to a cut-free proof by the following procedure:
1. For each level a ∈ I in increasing order (starting from the minimum):
   a. Eliminate all cuts on formulas `!_a A` first (principal cuts at level a).
   b. After eliminating level-a exponential cuts, apply rank reductions to expose principal cuts on sub-formulas at levels < a.
2. Finally, eliminate all non-exponential (multiplicative/additive) cuts.

The invariant maintained at each step: the proof is cut-free for all `!_b` formulas with b > a (already processed at lower levels in the ordering).

This would be a genuine stratified cut elimination theorem. As far as the literature shows, **it has not been stated or proved in this form.**

---

## 13. References

### Light logics and stratification
- Girard (1998). "Light Linear Logic." Information and Computation 143(2):175-204.
- Girard, Scedrov, Scott (1992). "Bounded Linear Logic." TCS 97(1):1-66. DOI: 10.1016/0304-3975(92)90386-T.
- Baillot, Mazza (2010). "Linear Logic by Levels and Bounded Time Complexity." TCS 408(1). arXiv:0801.1253.
- Baillot, Mazza (2015). "An Abstract Approach to Stratification in Linear Logic." IC 239. arXiv:1206.6504.

### Staged computation and modal logic
- Davies, Pfenning (2001). "A Modal Analysis of Staged Computation." JACM 48(3):555-604. URL: https://www.cs.cmu.edu/~fp/papers/jacm00.pdf
- Davies (1996/2017). "A Temporal Logic Approach to Binding-Time Analysis." LICS 1996 / JACM 64(1). URL: https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf
- Goubault-Larrecq (1996). "On Computational Interpretations of Modal Logic S4, I: Cut Elimination." INRIA RR-2934.
- Kovács (2022/2023). "Staged Compilation with Two-Level Type Theory." POPL 2023. arXiv:2209.09729.

### SELL and adjoint logic
- Nigam, Miller (2009). "Algorithmic Specifications in Linear Logic with Subexponentials." PPDP 2009. DOI: 10.1145/1599410.1599427.
- Kanovich, Kuznetsov, Nigam, Scedrov (2019). "Subexponentials in Non-Commutative Linear Logic." MSCS 29(8). arXiv:1709.03607.
- Pruiksma (2024). "Adjoint Logic with Applications." PhD thesis, CMU-CS-24-103.

### Standard cut elimination
- Pfenning (1994/2000). "Structural Cut Elimination in Linear Logic." CMU-CS-94-212; Inf. & Comp. 157. URL: https://www.cs.cmu.edu/~fp/papers/ic00.pdf

### NbE
- Abel (2013). "Normalization by Evaluation: Dependent Types and Impredicativity." Habilitation, LMU Munich. URL: https://www.cse.chalmers.se/~abela/habil.pdf
- Kavvos, Abel (2020). "Normalization by Evaluation for Modal Dependent Type Theory." JFP 30.

### Proof assistants
- Atkey (2023/2024). "Polynomial Time and Dependent Types." POPL 2023/2024. arXiv:2307.09145.

### Cross-references
- RES_0097: Subexponentials and scoped persistence
- RES_0098: ILL/SELL/LNL precise recovery relationships
- RES_0099: Compile-time cut elimination for CALC
- RES_0101: QTT, SELL, graded modalities, Petri nets
