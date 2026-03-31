---
title: "Subexponentials in Linear Logic — Scoped Persistence for Rule Set Control"
created: 2026-03-30
modified: 2026-03-30
summary: "SELL (Subexponential Linear Logic) stratifies ! into a family of indexed exponentials with a label preorder, enabling scoped persistence — the theoretical foundation for module-scoped forward rule sets in CALC"
tags: [linear-logic, exponentials, forward-chaining, lax-monad, adjoint-logic, Ceptre, clf, focusing]
category: "Forward Chaining"
---

# Subexponentials in Linear Logic — Scoped Persistence for Rule Set Control

## 1. SELL: Stratified Exponentials (Nigam & Miller 2009)

Subexponential Linear Logic (Nigam & Miller, PPDP 2009, building on Danos, Joinet & Schellinx 1993) replaces the single `!` with a family indexed by labels from a preorder. The system is parameterized by a **subexponential signature**:

```
Σ = ⟨I, ⪯, W, C⟩
```

where:
- `I` — finite set of subexponential labels
- `⪯` — preorder on `I`
- `W ⊆ I` — labels for which weakening holds (`?_a` can be discarded)
- `C ⊆ I` — labels for which contraction holds (`?_a` can be duplicated)

This gives a family of exponentials `!_a A` and `?_a A` for each `a ∈ I`. Standard ILL corresponds to `|I| = 1` with the single subexponential in both W and C (so both weakening and contraction hold). The Nigam-Miller papers note that "Andreoli's focused system for linear logic, the index set contains a single subexponential" — this is the standard `!` of ILL.

A two-label framing (sometimes called `lin` and `pers`) is a natural informal description but is not the canonical special case in the papers: the exact recovery of ILL uses one subexponential with both structural rules enabled.

### Promotion and dereliction in SELL

The structural rules are parameterized by the label. The key rule is promotion:

```
Γ_≤a; ⊢ A
────────────────── (!_a R)    side condition: all formulas in Γ are at levels ⪯ a
Γ; ⊢ !_a A
```

The promotion rule requires ALL hypotheses in the sequent to be at levels `⪯ a`. This prevents "capturing" higher-level resources inside a lower-level bang. Dereliction and the structural rules (weakening, contraction) are gated by membership in W and C respectively.

This matches the adjoint logic constraint: "a proof of A at mode a may only depend on hypotheses at modes b where b ⪯ a" (Pruiksma & Pfenning 2018).

## 2. Connection to CLF and the Lax Monad

CLF (Concurrent Logical Framework, Watkins, Cervesato, Pfenning & Walker 2002/2003) is a conservative extension of LLF with the synchronous connectives (`⊗`, `1`, `!`, `∃`) **encapsulated in a lax monad**. The underlying type theory is described as "a novel combination of lax logic and dual intuitionistic linear logic."

The monad `{A}` in CLF represents "computations that produce A" — it is a single, unindexed lax monad. The monad boundary (eliminator) introduces the monad result into the continuation; it does **not** discharge a persistent context in the SELL sense. CLF's monad isolates synchronous from asynchronous connectives; it is not parameterized by a label or preorder.

An **indexed monad `{A}_a`** — parameterized by a subexponential label `a` to mean "forward-execute with rules at levels ≤ a, discharge level-a rules at the boundary" — is **not a construct that appears in the published SELL or CLF papers**. It is a natural theoretical synthesis (combining SELL labels with CLF's monad) but no published paper establishes this construction under that name. The claim in some contexts that "the monad boundary discharges the level-specific persistent context" is a proposed design, not an established theorem in the literature.

## 3. Connection to Adjoint Logic (Pruiksma & Pfenning 2018)

Adjoint logic parameterizes the logic by a preorder `(M, ≥)` of modes, each with structural properties `σ(m) ⊆ {W, C}`. Shift operators `↑^k_m` (upshift) and `↓^n_m` (downshift) move between modes.

ILL is recovered with exactly **two modes** `U` (unrestricted: σ(U) = {W, C}) and `L` (linear: σ(L) = ∅), with `U > L`. The Pruiksma-Pfenning paper states this explicitly: "We obtain intuitionistic linear logic by using two modes, U (for structural) and L (for linear) with U > L." The lax monad arises as `○A_U = ↑^x_u ↓^u_x A_U` — a strong monad — instantiated with mode `X` between `U` and `L`.

The formal relationship: **ISELL (intuitionistic SELL) can be encoded as a fragment of adjoint logic** — subexponential labels of zones correspond to modes, and the preorder between labels is preserved as the preorder between modes. Adjoint logic is strictly more general (it also supports things like intuitionistic S4, lax logic, LNL).

## 4. Ceptre Stages (Martens 2015)

Ceptre (Martens, AIIDE 2015, PhD thesis CMU 2015) uses **stages** as a programming-with-quiescence mechanism over forward-chaining linear logic. A stage:

- Groups a set of rules into a named block: `stage S = { rule₁, rule₂, ... }`
- Runs to **quiescence**: fires rules until no rule in the stage can fire
- Uses a special `qui` predicate/resource to detect quiescence
- Outer-level rules of the form `qui * stage S -o stage T` transition between stages

Each stage has its own disjoint rule set — rules from stage S do not fire during stage T. This is a **hard partition** of rules, implemented operationally rather than type-theoretically.

Ceptre's thesis does **not** connect stages to SELL or subexponentials in the text. CLF receives a single citation reference in the introduction without technical discussion. There is no indexed monad `{A}_a` in Ceptre. Stages are justified operationally/pragmatically, not as subexponential modalities.

The connection between Ceptre stages and SELL is a reasonable theoretical interpretation (stages as subexponential labels) but it is **not established by Martens** in the published work.

## 5. Operational Soundness of Restricted Rule Sets

Nigam-Miller show that focused proof search in SELL can be used to specify algorithms. Restricting the rule set by subexponential label is operationally sound in the following sense:

- SELLF (focused SELL) is a **generalization of Andreoli's original focused system** for ILL
- Focusing restricts when rules apply (only during the appropriate phase) without losing completeness — any proof in the unfocused system has a corresponding focused proof
- Restricting to rules at levels ≤ a (the subexponential constraint) is analogous: it restricts which rules are available without producing invalid derivations

However, the analogy is imprecise. Andreoli focusing is a **completeness theorem**: every valid sequent has a focused proof. The SELL restriction of "use only level ≤ a rules" is a **soundness property**: any derivation found is valid. These are different kinds of claims. The operational refinement claim is sound but the "analogous to Andreoli focusing" framing elides this distinction.

## 6. Summary: Claim Accuracy Assessment

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| SELL replaces ! with family `!_a` indexed by preorder (I, ≤) | Yes | Confirmed. Signature is ⟨I, ⪯, W, C⟩ |
| Each label may admit W and/or C | Yes | Confirmed. W, C ⊆ I |
| Standard ILL is the 2-label case with lin and pers | Partially | ILL = 1 label with W+C. The "lin/pers" framing is an informal synthesis, not the canonical paper statement |
| Indexed monad `{A}_a` means "forward-execute at levels ≤ a, discharge level-a rules at boundary" | Not established | This is a proposed design combining SELL + CLF, not a published construct |
| Monad boundary discharges level-specific persistent context | Not established | CLF's monad boundary does not do this; the indexed variant is not in the literature |
| Restricting rule set is analogous to Andreoli focusing — operationally sound | Partially | Sound restriction: yes. Andreoli analogy: imprecise (focusing is a completeness theorem, not just soundness) |
| Connection to adjoint logic modes | Yes | ISELL is a fragment of adjoint logic; label preorder = mode preorder |

## 7. References

- Nigam & Miller (2009). *Algorithmic Specifications in Linear Logic with Subexponentials.* PPDP 2009.
- Danos, Joinet & Schellinx (1993). *The structure of exponentials: uncovering the dynamics of linear logic proofs.*
- Nigam, Olarte & Pimentel (2014/2015). *On subexponentials, focusing and modalities in concurrent systems.* TCS.
- Pruiksma, Chargin, Pfenning & Reed (2018). *Adjoint Logic.* Tech report CMU.
- Watkins, Cervesato, Pfenning & Walker (2002/2003). *A Concurrent Logical Framework: The Propositional Fragment.*
- Martens (2015). *Programming Interactive Worlds with Linear Logic.* PhD thesis, CMU.
