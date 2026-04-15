---
title: "The Indexed Lax Monad: Combining SELL Labels with CLF's Monadic Boundary"
created: 2026-03-31
modified: 2026-03-31
summary: "Synthesis of SELL's indexed exponentials !_a with CLF's lax monad {A} into an indexed monad {A}_a that scopes forward execution to subexponential strata — a construct not found in the published literature"
tags: [linear-logic, exponentials, forward-chaining, lax-monad, adjoint-logic, clf, subexponentials]
category: "Forward Chaining"
unique_contribution: "The indexed lax monad {A}_a — combining SELL's subexponential promotion condition with CLF's monadic forward execution boundary — is not found in any published paper. This document identifies the structural analogy between CLF's {S}I rule and SELL's !_a R rule, and proposes the indexed monad as their unification."
references:
  - "Nigam & Miller (2009). Algorithmic Specifications in Linear Logic with Subexponentials. PPDP."
  - "Watkins, Cervesato, Pfenning & Walker (2003). A Concurrent Logical Framework. TYPES."
  - "Pruiksma & Pfenning (2018). Adjoint Logic. CMU tech report."
  - "Martens (2015). Programming Interactive Worlds with Linear Logic. PhD thesis, CMU."
---

# The Indexed Lax Monad: Combining SELL Labels with CLF's Monadic Boundary

## 1. The Gap

Two independently-developed extensions of linear logic address different aspects of persistent-context management:

**SELL** (Nigam & Miller 2009) stratifies the exponential `!` into a family `!_a` indexed by labels from a preorder `(I, ≤)`. Each label governs which structural rules (weakening, contraction) apply and which hypotheses are visible during promotion. SELL is purely proof-theoretic — it has no operational semantics for "entering" or "leaving" a subexponential stratum.

**CLF** (Watkins et al. 2003) extends linear logic with a lax monad `{A}` that marks the boundary between asynchronous (backward) and synchronous (forward) computation. The monad intro rule `{A}I` transitions from backward proof search to forward multiset rewriting until quiescence. CLF's monad is unindexed — there is a single boundary with no label parameter.

No published work combines these into an indexed monad `{A}_a`.

## 2. The Structural Analogy

The key observation is that CLF's monad introduction and SELL's promotion share a **structural parallel** — both impose a context restriction on their premise, at different levels of generality:

```
SELL promotion (!_a R):
  Γ_≤a ; · ⊢ A
  ─────────────── all hypotheses at levels ≤ a
  Γ ; · ⊢ !_a A

CLF monad introduction ({A}I):
  · ; Δ ⊢ S             (S is a synchronous formula)
  ──────────────── linear context Δ consumed by forward execution
  Γ ; · ⊢ {S}
```

Both rules impose a **context restriction** on the premise: SELL requires hypotheses at levels ≤ a; CLF requires the persistent context to be exactly what was available before the monad boundary (forward execution cannot introduce new persistent hypotheses beyond those already present).

CLF's `{S}I` is the special case where `a = ∞` (the single ILL subexponential) with an **operational interpretation** — the engine forwards-executes using the available persistent rules until quiescence. SELL's `!_a R` is the generalization to arbitrary labels but **without** the operational forward-execution semantics.

## 3. The Indexed Monad `{A}_a`

We define the indexed lax monad as the synthesis of these two constructs:

```
Γ_≤a ; Δ ⊢ A     (forward-execute with persistent rules at levels ≤ a)
────────────────── ({A}_a intro)
Γ ; · ⊢ {A}_a     (level-a rules discharged at the boundary)
```

The operational semantics:
1. Enter the monad at level `a`: load persistent rules from strata ≤ a
2. Forward-execute (committed-choice multiset rewriting) until quiescence
3. Exit the monad: discharge level-a persistent rules from the context

This generalizes both parent constructs:
- When `|I| = 1` (a = ∞), this is CLF's `{A}` — all persistent rules available
- When forward execution is trivial (identity), this degenerates to SELL's `!_a`

### Sequencing with different rule sets

The monadic let rule enables multi-phase staged execution:

```
Γ ; Δ₁ ⊢ {A}_a     Γ, x:A ; Δ₂ ⊢ {B}_b
────────────────────────────────────────── (monadic let)
Γ ; Δ₁, Δ₂ ⊢ let {x} = M in N : {B}_b
```

Phase 1 uses level-a rules. Phase 2 uses level-b rules. The base Γ (shared across all strata) persists. Level-specific rules do not accumulate across phases.

## 4. Relationship to Adjoint Logic

In adjoint logic (Pruiksma & Pfenning 2018), the indexed monad decomposes into shift operators:

```
{A}_a  ≅  ↑_base^a (↓_a^base A)
```

where:
- `↓_a^base` enters mode `a` (gaining access to level-a hypotheses)
- Forward execution occurs at mode `a`
- `↑_base^a` exits mode `a` (releasing level-a hypotheses)

This decomposition exists in adjoint logic's type system but no published work gives it the specific operational semantics of "forward execute at mode a to quiescence." The contribution is the **operational interpretation**, not the type structure.

## 5. Relationship to Ceptre Stages

Ceptre (Martens 2015) implements staged forward execution via named rule blocks that run to quiescence. Stages are operationally a special case of the indexed monad where:

- Each stage name is a subexponential label
- The label preorder is the stage transition graph
- Quiescence detection (`qui` predicate) is the monad boundary

Martens does not make this connection in the published work. The indexed monad provides a proof-theoretic account of what stages accomplish operationally.

## 6. Soundness of Operational Approximation

Even without implementing the full indexed monad type system, restricting the rule set passed to `forward.run()` is a **sound operational refinement**:

- Any derivation found under restricted rules is valid in the unrestricted logic
- Restriction can only miss derivations, never produce invalid ones
- For committed-choice execution: only one derivation is selected anyway
- For exhaustive exploration: restriction is the desired behavior (search space pruning)

This is a **soundness** property, not a completeness property. It is analogous in spirit (not in formal statement) to Andreoli focusing: both are operational refinements that restrict the search space without invalidating found proofs. The difference: focusing preserves completeness (every provable sequent has a focused proof); rule restriction does not (some derivations may become unreachable).

## 7. Implementation Status in CALC

CALC implements the indexed monad in three tiers:

- **Tier 1** (operational): Label-based rule filtering at the `exec`/`explore` boundary. Forward rules tagged with source labels; `(rules: [label])` syntax restricts which participate.
- **Tier 2** (algebraic): Named modules with set algebra (union, intersection, subtraction) over rule sets. Provides composable rule set construction.
- **Tier 3** (type-theoretic): Full indexed monad `{A}_a` with Pi types for label parameters. Requires dependent types (TODO_0011).

Tiers 1-2 are sound operational approximations of Tier 3. They implement the rule restriction without the type-level label tracking. Tier 3 would make the label a first-class type, enabling the full adjoint logic decomposition.

## 8. References

- Nigam & Miller (2009). *Algorithmic Specifications in Linear Logic with Subexponentials.* PPDP.
- Watkins, Cervesato, Pfenning & Walker (2003). *A Concurrent Logical Framework: The Propositional Fragment.* TYPES.
- Pruiksma & Pfenning (2018). *Adjoint Logic.* CMU tech report.
- Martens (2015). *Programming Interactive Worlds with Linear Logic.* PhD thesis, CMU.
- Chaudhuri (2010). *Classical and Intuitionistic Subexponential Logics Are Equally Expressive.* CSL.
- RES_0130 — Subexponentials in Linear Logic (survey of SELL)
- RES_0131 — ILL, SELL, and LNL recovery relationships
