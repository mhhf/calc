---
title: "CALC Motivation and Vision"
created: 2026-02-21
modified: 2026-02-21
summary: "The central question driving CALC: can we design a proof calculus where resources are tracked exactly, ownership is explicit, quantities matter, and financial primitives have natural representations?"
tags: [linear-logic, accounting, ownership, financial-primitives, vision]
category: "Foundations"
unique_contribution: "Identifies double-entry bookkeeping as applied linear logic, proposes three orthogonal dimensions of resource control (structural, epistemic, quantitative), and frames the technical challenge as display calculus + multi-type methodology."
references:
  - "Pacioli, 'Summa de Arithmetica', 1494"
  - "Girard, 'Linear Logic', TCS, 1987"
  - "Greco & Palmigiano, 'Multi-Type Display Calculus', 2016"
  - "Benton, 'A Mixed Linear and Non-Linear Logic', 1995"
---

# CALC Motivation and Vision

**CALC** (Calculus for Accountable Linear Computations) explores the intersection of proof theory, linear logic, authorization, and financial modeling.

## The Central Question

> Can we design a proof calculus where resources are tracked exactly, ownership is explicit, quantities matter, and financial primitives have natural representations?

**Key Discovery:** Double-entry bookkeeping (Pacioli, 1494) is applied linear logic. Accountants have been doing resource-sensitive reasoning for 500+ years. CALC makes this connection formal.

## Three Orthogonal Dimensions of Resource Control

| Dimension | Concern | Mechanism |
|-----------|---------|-----------|
| **Structural** | Use pattern | Linear, affine, exponential |
| **Epistemic** | Who owns it? | `[Alice] A`, `[Bob] A` |
| **Quantitative** | How much? | `[]_r A` (graded modalities) |

**The Technical Challenge:** Display calculus elegantly handles structural modalities, but exponentials (!) lack residuals. Multi-type methodology (Greco & Palmigiano) offers a solution.

## What We Aim to Explore

1. **Resource-sensitive financial primitives** — options as additive choice, futures as deferred obligations, swaps as iterated exchanges
2. **Ownership modalities** — `[Alice] []_r token` with transfer, split, merge, atomic swap
3. **Symbolic execution of linear programs** — exhaustive exploration of all execution paths, building execution trees that are themselves proof objects
4. **Display calculus for linear logic** — elegant proof theory with cut elimination guarantees
5. **Multi-type framework** — multiple formula types with adjunctions (Benton's LNL decomposition for exponentials)
6. **Authorization and consensus** — Garg's says-modality, multi-party consent, threshold modalities
7. **Categorical semantics** — ownership as fibration, Pacioli group as grading semiring

## Novel Research Contributions

1. **Pacioli group as grading semiring** — accounting + graded types unification
2. **Ownership as fibration** — principals form base category, resources are fibers, transfer = reindexing
3. **Debt as channel** — unification of linear negation (obligations) and session type duality
4. **Coherence = consensus achievability** — compile-time guarantee of multi-party agreement
5. **Three-level structure** — structural x epistemic x quantitative modalities as orthogonal concerns
6. **Exhaustive forward chaining** — don't-know nondeterminism over CLF's lax monad with additives and guarded continuations

## Unexplored Directions

- Comparative analysis: CALC vs Move vs Nomos
- Formal verification of CALC itself in Lean/Agda
- Hardware acceleration for proof search
- Linear BDI: agent execution with linear intentions
- Temporal modalities for financial derivatives
- μMALL fixed points for induction/coinduction over execution trees
