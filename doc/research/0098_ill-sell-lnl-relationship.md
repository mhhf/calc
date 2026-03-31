---
title: "ILL, SELL, and LNL: Precise Recovery Relationships"
created: 2026-03-31
modified: 2026-03-31
summary: "Exact technical characterization of how ILL is recovered from SELL (one label, not two), how LNL relates to SELL and adjoint logic, and what Chaudhuri 2010 says about minimum label sets"
tags: [linear-logic, exponentials, adjoint-logic, proof-theory, focusing, sequent-calculus]
category: "Proof Theory"
---

# ILL, SELL, and LNL: Precise Recovery Relationships

This document answers four precise technical questions about the relationship between standard ILL, SELL (Subexponential Linear Logic), and Benton's LNL (Linear/Non-Linear) logic, using primary source quotes.

## 1. How Nigam & Miller 2009 Recover ILL from SELL

**Question:** When they say "linear logic is recovered as a special case," do they mean |I|=1 (one label with W+C) or |I|=2 (lin + pers)?

**Answer: |I|=1. One label ∞ with both W and C.**

The PPDP09 paper does not use the phrase "linear logic is recovered as a special case" in those words. What it says instead (Section 3, defining the signature):

> "we shall assume that the pre-ordered set ⟨I, ⪯⟩ has a maximal element, written ∞, which is unbounded."

And regarding Andreoli's focused system (Section 4):

> "In Andreoli's focused system for linear logic, the index set contains just ∞ and K[∞] contains the set of unbounded formulas."

**This is the exact characterization:** standard ILL (Andreoli's focused system) uses `I = {∞}`, with ∞ ∈ W and ∞ ∈ C (∞ is the single unbounded label). There is no separate "linear" label in the standard ILL special case. The bounded/linear resources in ILL are simply the formulas NOT under any `!` — they live in the ordinary linear context Γ, not under any subexponential zone.

Nigam-Miller do **not** give a named instance called "ILL" or characterize it as a two-label system. The passage is descriptive: Andreoli's system has one index ∞ for unbounded formulas, and that is how SELL degenerates to standard linear logic.

**Additional context:** Nigam-Miller restrict their paper to signatures where `W = C` (either both or neither), and require a maximal unbounded element ∞. The simplest non-trivial SELL signature with locations has the form `h{∞, l}, {l ⪯ ∞}, {∞}, {∞}i` — one unbounded label ∞ plus one bounded (linear) location label l. This is already two labels, but the bounded label `l` is NOT a standard linear context in the ILL sense — it is a named storage zone for forward-chaining algorithms.

## 2. Chaudhuri 2010: Recovering Familiar Logics from SELL

Chaudhuri (CSL 2010, "Classical and Intuitionistic Subexponential Logics Are Equally Expressive", arXiv:1006.3134) uses a slightly different signature format `Σ = ⟨Z, ≤, l, U⟩` where:
- Z = set of zones
- l ∈ Z = "working zone" (the linear zone for active formulas)
- U ⊆ Z = unrestricted zones (admit W+C); Z \ U = restricted zones (linear)

**Fact 7 (Chaudhuri, exact quote):**

> "Polarised classical linear logic (CLL) is determined by `ll = ⟨{l, u}, l ≤ u, l, {u}⟩`. In addition to the injections of mall, we also have the exponentials `! = !_u` and `? = ?_u`."

So for CLL: **two zones** — `l` (restricted/linear, working zone) and `u` (unrestricted/exponential). `|Z| = 2`.

For MALL (no exponentials): `mall = ⟨{l}, ·, l, ∅⟩`. **One zone**, with no unrestricted zones. This gives MALL without any exponentials.

For classical logic: `l = ⟨{l}, ·, l, {l}⟩`. **One zone**, but unrestricted.

**Key observation:** In Chaudhuri's formulation, CLL (which contains the standard `!`) already requires TWO zones — one restricted working zone `l` and one unrestricted zone `u`. This is because the restricted zone `l` plays the role of "the linear context" and `u` plays the role of "the exponential context." The standard `!` in CLL is `!_u`.

Chaudhuri does not separately name the intuitionistic restriction of CLL as "ILL" in Fact 7, but states: "The intuitionistic restrictions of the familiar instances from defn. 7 simply use the same subexponential signatures." So ILL in Chaudhuri's formulation also uses `ll = ⟨{l, u}, l ≤ u, l, {u}⟩` — TWO zones.

**This means:** Chaudhuri's formulation and Nigam-Miller's formulation give DIFFERENT answers to the question of how many labels ILL needs:

| Formulation | Linear zone | Exponential (!) | Total labels |
|-------------|-------------|-----------------|--------------|
| Nigam-Miller (PPDP09) | Γ context (not a subexp zone) | ∞ (one unbounded subexp) | 1 subexp label |
| Chaudhuri (CSL10) | l zone (restricted, the working zone) | u zone (unrestricted) | 2 zones |

The difference is **representational**: in Nigam-Miller's setup, the linear context Γ is not a subexponential zone — it is the ordinary sequent context. In Chaudhuri's two-sided setup, everything goes into a zone, so the linear material goes into zone `l` (restricted).

Both agree on the essential point: the standard `!` of ILL corresponds to a single unbounded/unrestricted subexponential label (called ∞ by Nigam-Miller, `u` by Chaudhuri). The number of total subexponential labels differs only because Chaudhuri explicitly zones the linear context itself.

## 3. Does LNL Already Have "Two Subexponential Levels"?

**The linear/persistent split in sequent calculus (Γ ; Δ ⊢ C) is the standard sequent structure, not a subexponential construction.**

In SELL as formulated by Nigam-Miller, the sequent has the form `K : Γ ⊢ C` where:
- K is an **indexed context** mapping subexponential labels to formula multisets (the `?_l`-stored formulas)
- Γ is the **ordinary linear context** (formulas without any subexponential annotation)

The Γ context is NOT a subexponential zone — it is the base linear multiset that all SELL systems inherit from standard linear logic. When you add one subexponential ∞ (the standard `!`), you get standard ILL. The "linear/persistent" distinction in ILL comes from having Γ (linear) and K[∞] (persistent), which is exactly the Nigam-Miller picture with one subexponential.

**In CALC's terms:** CALC has `{ linear: FactSet, persistent: FactSet }`. The `linear` facts correspond to Γ in Nigam-Miller's notation; the `persistent` facts correspond to K[∞]. So CALC implements SELL with `|I| = 1` — the single subexponential ∞ for persistent facts, plus the base linear context. This is not "two subexponential levels" in the SELL sense; it is standard ILL.

### The Adjoint Logic View

Pruiksma & Pfenning (2018 tech report, CMU) recover ILL using **two modes** in adjoint logic:

> "We obtain intuitionistic linear logic [Barber 1996; Girard 1987] by using two modes, U (for structural) and L (for linear) with U > L. Moreover, σ(U) = {W, C} and σ(L) = {}."

And they distinguish LNL from ILL:

> "We obtain LNL [Benton 1994] just like linear logic with two modes U > L, but we populate the unrestricted layer with additional propositions [i.e., add → and × to mode U]."

So in adjoint logic:
- ILL uses two modes (U and L), but mode U's propositions are **only the shifted propositions** (just the shift `↑^U_L A`). Girard's `!A = ↓^U_L ↑^U_L A`.
- LNL uses the same two modes (U > L), but adds full cartesian connectives (→, ×, 1_U) to mode U.
- The difference is what you put in the unrestricted layer.

Pruiksma-Pfenning also state: "Girard's approach can be seen as a special case of Benton's." That is, ILL is a special case of LNL where the unrestricted layer only contains the exponential modality, not the full cartesian structure.

## 4. Benton's LNL and Its Relationship to SELL

**Benton 1994:** "A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models." CSL 1994 / Technical Report UCAM-CL-TR-352.

LNL has two distinct zones/judgments:
- **Non-linear zone**: full cartesian closed category (→, ×, 1)
- **Linear zone**: symmetric monoidal closed category (⊸, ⊗, I)
- Two shift operators: `F : non-linear → linear` (downshift ↓) and `G : linear → non-linear` (upshift ↑)
- The ! modality decomposes: `!A = GFA` — go up to non-linear then back down

**Is LNL equivalent to SELL with two labels?**

This is NOT directly stated in any of the primary papers. The closest characterization comes from the adjoint logic framework:

From Pruiksma-Pfenning (2018, Theorem 2.3):

> "If we let τ embed propositions of LNL into the instance of adjoint logic described above, then: (a) Θ ⊢ C^X in LNL iff τ(Θ) ⊢ τ(X) in adjoint logic. (b) Θ; Γ ⊢^L A in LNL iff τ(Θ), τ(Γ) ⊢ τ(A) in adjoint logic."

LNL embeds faithfully into adjoint logic with two modes U > L where U has the full cartesian connectives.

Now, adjoint logic is more general than SELL (SELL is a fragment of adjoint logic, as Pruiksma-Pfenning note). The adjoint logic encoding of LNL uses two modes with the preorder U > L — this structurally resembles SELL with two zones. But:

1. LNL has **full non-linear types** (→, ×) at mode U, while SELL's "unrestricted" subexponential only has the `!`/`?` exponential operators — it does NOT have a full cartesian layer with its own types and terms.

2. LNL's distinction is a **type-theoretic** distinction (two different type theories connected by adjoint functors), while SELL's two-zone picture (l ≤ u) is just a sequent-level distinction (formulas annotated with zone labels).

3. Chaudhuri's CLL signature `⟨{l, u}, l ≤ u, l, {u}⟩` gives you exactly two zones — but zone `u` only supports `!_u` and `?_u`, not full cartesian types. This is much weaker than LNL's non-linear zone.

**Conclusion:** LNL is strictly richer than "SELL with two labels." LNL = SELL-with-two-labels + full non-linear type theory at mode U + Curry-Howard interpretation. SELL with two labels gives you the substructural restrictions (linear vs. persistent formulas) but not the full non-linear type theory.

## 5. Summary Table

| System | Linear context representation | How ILL's ! arises | Labels/modes |
|--------|------------------------------|---------------------|--------------|
| ILL (standard sequent) | Multiset Γ | Promotion rule w/ empty Γ | n/a |
| SELL (Nigam-Miller) | Γ (base) + indexed K | K[∞] = unbounded zone | 1 subexp (∞) for persistent |
| SELL (Chaudhuri) | Zone l (restricted, working) | Zone u (unrestricted) | 2 zones (l, u) |
| Adjoint Logic (ILL instance) | Mode L propositions | !A = ↓^U_L ↑^U_L A | 2 modes (L, U) |
| LNL (Benton) | Linear layer (⊸, ⊗, I) | !A = GFA, G=↑, F=↓ | 2 layers (L, U with full types) |
| CALC current | `linear: FactSet` | `persistent: FactSet` | = ILL = 1 subexp (∞) |

**Key precision:** When Nigam-Miller say "Andreoli's focused system for linear logic, the index set contains just ∞," they mean the recovery of ILL uses one subexponential label. When Chaudhuri (or Pruiksma-Pfenning) use two zones/modes, they are making the linear working zone explicit as a first-class zone — the substance is the same.

## 6. Chaudhuri 2010: Main Theorem and Minimum Labels

Chaudhuri's main theorems (Theorems 12 and 17) establish **focal adequacy** (bijection on focused derivations) between:
- Classical SELL encoded in its own intuitionistic restriction (Theorem 12)
- Intuitionistic SELL encoded in a classically-extended signature (Theorem 17, signature splitting)

The signature splitting construction (Definition 14-15) is key: to encode intuitionistic SELL Σ in classical SELL, you need to split each zone z into two zones (z, l) and (z, r) — doubling the number of zones. This means encoding the intuitionistic restriction of CLL (= ILL) in classical CLL requires going from `⟨{l, u}, l ≤ u, l, {u}⟩` to a signature with 4 zones `⟨{(l,l),(l,r),(u,l),(u,r)}, ..., (l,l), {(u,l),(u,r)}⟩`. So the minimum label set for ILL within Chaudhuri's classical formulation is 2 zones (l and u), but to encode ILL adequately in classical SELL you need 4 zones.

Chaudhuri does not explicitly state "the minimum label set for ILL is 2" — he derives this from instantiating his general construction.

## 7. References

- Nigam & Miller (2009). *Algorithmic Specifications in Linear Logic with Subexponentials.* PPDP 2009. (ppdp09.pdf)
- Chaudhuri (2010). *Classical and Intuitionistic Subexponential Logics Are Equally Expressive.* CSL 2010. arXiv:1006.3134.
- Pruiksma, Chargin, Pfenning & Reed (2018). *Adjoint Logic.* CMU Tech report. (adjoint18.pdf)
- Benton (1994). *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models.* CSL 1994. UCAM-CL-TR-352.
- Danos, Joinet & Schellinx (1993). *The structure of exponentials: uncovering the dynamics of linear logic proofs.* (original SELL precursor)
