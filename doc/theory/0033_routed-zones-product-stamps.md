---
title: "Routed Zones and the Product-Stamp Scheduler"
created: 2026-09-04
modified: 2026-09-04
summary: "Aux consumable zones are wrapper-routed views of one threaded pool (the routed-column equivalence makes N-zone sequent calculi run on the two-zone search machinery unchanged), and the time×dist product stamp schedules committed runs by the lexicographic total order while the Pareto frontier of completions lives in the exploration layer; per-axis translation is the only lawful action (the cocycle argument against the t+d matched pair)."
tags: [linear-logic, proof-theory, adjoint-logic, structural-rule, lnl, graded-types, scheduling, timed, architecture]
category: "Proof Theory"
unique_contribution: "Three results not in the literature or prior CALC docs: (1) the routed-column equivalence — for zones whose membership is decided by a wrapper connective (hash-disjoint columns), the N-zone sequent calculus is equivalent to the one-pool calculus with routing at construction boundaries, so resource management (leftover threading, kernel pool accounting) needs no per-zone generalization; (2) the lex/Pareto factorization of multi-objective settle — committed runs use the lexicographic completion of the product order (all total-order scheduler invariants survive verbatim), the Pareto frontier is exactly the exploration layer's job (dominance derived from the join: a ⊑ b iff a ⊔ b = b); (3) the recorded cocycle argument for why transport-takes-time must be a rule, never a grade coercion."
references:
  - "Licata, Shulman & Riley (2017). A Fibrational Framework for Substructural and Modal Logics. FSCD 2017."
  - "Benton (1994). A Mixed Linear and Non-Linear Logic. CSL 1994."
  - "Petricek, Orchard & Mycroft (2014). Coeffects: a calculus of context-dependent computation. ICFP 2014."
  - "THY_0018 (delay-graded lax monad), THY_0019 (timed matching/settle), THY_0022 (fenced grade algebras), THY_0032 (mode preorders — superseded disposition), doc/paper/settle-optimality.md (T2)."
  - "TODO_0285 (implementation: P4 zones-as-data, P5 sill/located, P6 product stamps)."
---

# Routed Zones and the Product-Stamp Scheduler

**Scope.** The theory behind TODO_0285: the zones-as-data generalization
(P4), the located modality's zone (P5), and the time×dist product
scheduler (P6). Supersedes THY_0032's disposition — the fence is
relaxed, and this document records why the relaxation is cheap.

## 1. The routed-column equivalence

A calculus may declare consumable zones beyond the primary one
(`deriveContextStructure`: the first no-contraction zone in position
order is primary; the rest are AUX). An aux zone's membership is decided
by its **wrapper connective** — the constructor whose `@category` names
the zone (sill: `loc`/`located`). Two consequences:

- **Hash-disjointness.** A wrapper-tagged formula never legally inhabits
  the primary column and vice versa, so the union of the consumable
  columns is a multiset in which zone membership is recoverable by a tag
  lookup (`Seq.routeZone`).
- **Equivalence.** Let S_N be the N-zone sequent calculus (zone columns,
  per-zone linearity) and S_1 the calculus over the union pool with
  columns rebuilt by routing at every sequent-construction boundary.
  Every S_N derivation maps to an S_1 derivation by forgetting columns,
  and every S_1 derivation maps back by routing — the maps are inverse
  because routing is deterministic and total on wrapper-disjoint pools.
  Hence provability, per-zone linearity, and kernel resource accounting
  coincide.

Operationally this means the prover's leftover-threading discipline
(`Context` deltas), the kernel's pool accounting, focusing, and the
affine boundary discharge all run **unchanged** on the union pool
(`Seq.consumablePool`); zone columns are materialized views — the mode
discipline made visible, not a second resource manager. This is why the
acceptance criterion "adding a third declared zone requires no kernel
edits" holds in its honest reading: the union-pool plumbing was a
ONE-TIME, zone-count-agnostic change; each further zone is data
(position mode + structural rules + wrapper), and the engine is routing.

Boundaries that route: sequent parsing, rule-interpreter premise
construction, `addDelta`, the copy axiom, `stripToken`, the bridge
(`sequentToState` feeds ALL consumable zones into the forward linear
pool — wrapped facts are ordinary linear facts in their own tag group,
so the forward engine needs no third FactSet; per-fiber linearity of
`A @@ L` is automatic because the place is part of the fact identity).

**Which β are admitted.** Aux zones must be linear-policy (no
contraction, no weakening) — a policy the engine would not honor is a
loud load error, not a silent annotation. Weakening-only (affine) zones
remain future work; the rule-level `@affine` discharge (THY_0027) is the
existing mechanism for affine behavior.

## 2. The product stamp: lex-committed, Pareto-explored

sill's scheduler axis is the product (time, dist) — one stamp value
carrying both, componentwise tropical (⊗ adds per axis, ⊔ joins per
axis: a conclusion waits for the last input in time AND carries the
dearest accumulated cost). The product order is partial; the scheduler
needs decisions. The factorization:

- **Committed settle runs on the LEXICOGRAPHIC completion** (time
  primary, dist tie-break) — a total order, so every scheduler invariant
  that assumed totality (min-activation heap, the B&B prune contract
  `cmp ≥ 0`, the FIFO invariant pair, Zeno frontier progress, tied-set
  formation) survives verbatim. The committed run realizes the lex-least
  completion; T2's side conditions (contention-freedom, H-termination,
  S) apply per-axis because ⊗ and ⊔ act componentwise and the lex order
  refines the product order.
- **The Pareto frontier lives in the exploration layer.**
  `settleFrontier` = `settleExplore` (all chooser worlds) + the
  dominance filter, with dominance DERIVED FROM THE JOIN: a ⊑ b iff
  a ⊔ b = b. No new algebra slot, and for a total order the frontier
  degenerates to the unique least completion — the scalar case is the
  degenerate instance, not a special case. A leaf's cost is ⊔ over its
  final facts' stamps (the completion vector).

The two lemmas of the settle-optimality paper that break under a raw
product order (L1 per-firing optimality needs comparability for the
prune; L2's `aMin` is undefined on incomparable activations) are exactly
the two the lex completion repairs — and the price is explicit: the
committed run picks ONE Pareto point (the lex-least); the others are
exploration results, never silently discarded facts (mass conservation
is the measure class's concern, not the order class's).

Zeno note: lex progress includes dist-only progress at a fixed instant,
so a zero-time dist-accumulating loop advances the frontier and evades
`maxInstantSteps`; `maxSteps` is the bound that catches it. Orbit
acceleration and rebase are deliberately unavailable (the algebra omits
`scale`/`floorDiv`/`floor` — per-axis shift degrees are unresolved
design; loud absence beats silently wrong mass math).

**Certification stays clause-only.** The stamp judgments over pair
terms (lex `le`/`lt`, componentwise `qsub`) are prelude clauses; the
activation join — which under a product order may equal NO single input
— is re-derived through a declared join predicate (`fire` config
`join`, sill's `sjoin`). The scalar join clauses use the checked-`qsub`
monus trick (`sjoin A B A ⟸ qsub A B H`): on pairs, `qsub` succeeds
only under componentwise dominance, so the comparable-case clauses are
pair-safe and incomparable pairs fall through to the componentwise
clauses. All derivations agree on the value (joins are unique), so
clause overlap is harmless.

## 3. The cocycle argument: transport is a rule

"Transport takes time" couples the axes. The lawful coupling is the
rule shape

    transport: (A @@ L) * road L L' * !dist L L' T D
      -o { (A @@ L') }@(T ~ D).

— the edge's cost enters ONCE per hop, into the product grade. The
tempting alternative, a matched-pair type coercion κ(d, t) = t + d
("a distance IS a delay"), is illegal: the action laws (THY_0018 §2 —
`t ⊳ 0 = t`, `(t ⊳ d) ⊳ e = t ⊳ (d + e)`, distributivity over max)
must hold PER AXIS for the product, and a cross-axis additive coercion
double-counts d over chained hops: two hops of distance d each would
contribute 2d to the time axis at the first coercion point and again at
the second — κ is not a cocycle for the chained composite. Per-axis
translation `(t, δ) ⊳ (T, D) = (t + T, δ + D)` satisfies all three laws
on each axis; a dilation κ(d, t) = c(d)·t satisfies law 1 only when
c ≡ 1. Hence: coupling by COERCION is confined to the trivial one, and
the non-trivial coupling is program structure — a rule, firing once per
edge, whose cost data are ordinary persistent facts.
