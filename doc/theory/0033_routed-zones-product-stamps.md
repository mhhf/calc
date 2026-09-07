---
title: "Routed Zones and the Product-Stamp Scheduler"
created: 2026-09-04
modified: 2026-09-08
summary: "Aux consumable zones are wrapper-routed views of one threaded pool (the routed-column equivalence, proved at referee grain: U/R inverse bijections on derivations under the zone-correctness invariant), and the time×dist product stamp schedules committed runs by the lexicographic total order — the scalar theory transfers along the C4 split (C4a upper-bound survives, C4b selectivity fails, whole-bind excluded by an executable witness) while the Pareto frontier of completions lives in the exploration layer; transport is a rule, never a cross-axis grade coercion (the axis-confounding argument)."
tags: [linear-logic, proof-theory, adjoint-logic, structural-rule, lnl, graded-types, scheduling, timed, architecture]
category: "Proof Theory"
paper: "SPLIT disposition (2026-09-04). §2 (product scheduler) is compiled into doc/paper/settle-optimality.md §8.4 — the C4 split, lex transfer lemma, T1×/T2× with the whole-bind exclusion, materialized frontier, frontier adequacy; that paper discharges its former ⟨open⟩ P1 obligation with it. §1 (routed-column equivalence) is COMPILED (2026-09-08) into doc/paper/toolbox/toolbox.md §4 — the toolbox paper's formal centerpiece and now the single source of truth for the proofs; §1 here is a pointer stub with the summary-grain statement. Standalone workshop note was considered and declined (2026-09-04). §3 (axis-confounding) is positioning material, summarized in §8.4's transport paragraph."
unique_contribution: "Three results not in the literature or prior CALC docs: (1) the routed-column equivalence — for zones whose membership is decided by a wrapper connective (hash-disjoint columns), the N-zone sequent calculus is equivalent to the one-pool calculus with routing at construction boundaries (proved: U/R inverse bijections on derivations, with zone-correctness as the discharged invariant), so resource management needs no per-zone generalization; (2) the lex/Pareto factorization of multi-objective settle via the C4 split — merge-as-upper-bound (C4a) carries L1/L2/T1/T2 to the lex order, merge-selectivity (C4b) fails and takes exactly the whole-bind rescue and coalesce-safety with it (executable witness), while the Pareto frontier is the exploration layer's job (dominance derived from the join: a ⊑ b iff a ⊔ b = b) and the contention-free fragment materializes the per-fact frontier in one committed run; (3) the axis-confounding argument for why transport-takes-time must be a rule, never a grade coercion — cross-axis coercions are algebraically lawful monoid homomorphisms; the refutation is semantic (they collapse the product's two objectives)."
references:
  - "Licata, Shulman & Riley (2017). A Fibrational Framework for Substructural and Modal Logics. FSCD 2017."
  - "Benton (1994). A Mixed Linear and Non-Linear Logic. CSL 1994."
  - "Pruiksma & Pfenning (2018+). Adjoint Logic (message-passing interpretation; Reed ~2009 manuscript is the mode-preorder origin)."
  - "Despeyroux & Chaudhuri (2013/2019). A Hybrid Linear Logic for Constrained Transition Systems (HyLL). TYPES 2013 / MSCS 2019."
  - "Nigam & Miller (2011). Subexponential Linear Logic (SELL). PPDP 2011."
  - "Orchard, Liepelt & Eades (2019). Quantitative Program Reasoning with Graded Modal Types (Granule). ICFP 2019."
  - "Fujii, Katsumata & Melliès (2016). Towards a Formal Theory of Graded Monads. FoSSaCS 2016."
  - "Bouyer, Brinksma & Larsen. Multi-priced timed automata and Pareto reachability (various; CSL 2025 approximation results)."
  - "Petricek, Orchard & Mycroft (2014). Coeffects: a calculus of context-dependent computation. ICFP 2014."
  - "THY_0018 (delay-graded lax monad), THY_0019 (timed matching/settle), THY_0022 (fenced grade algebras), THY_0032 (mode preorders — the original no-generalization disposition is superseded by P4; its site map remains the routing inventory), doc/paper/settle-optimality.md (T2; §8.4 is the referee-grain home of this document's §2 — C4 split, lex transfer, materialized frontier, frontier adequacy)."
  - "Gurney & Griffin (2007). Lexicographic Products in Metarouting. ICNP 2007 — strict primary isotonicity for lex products, the transfer lemma's hypothesis in its native habitat."
  - "TODO_0285 (implementation: P4 zones-as-data, P5 sill/located, P6 product stamps)."
---

# Routed Zones and the Product-Stamp Scheduler

**Scope.** The theory behind TODO_0285: the zones-as-data generalization
(P4), the located modality's zone (P5), and the time×dist product
scheduler (P6). Supersedes THY_0032's disposition — the fence is
relaxed, and this document records why the relaxation is cheap.

## 1. The routed-column equivalence

**COMPILED (2026-09-08): the referee-grain content of this section —
Definitions 1–3 (routed zone structure, U/R, zone-correctness), Lemmas
A/B, the equivalence theorem, and the implementation corollary — now
lives in `doc/paper/toolbox/toolbox.md` §4, which is the single source
of truth for the proofs.** Statement, for this document's
self-containedness:

For a zone-correct calculus whose aux consumable zones are decided by
hash-disjoint wrapper connectives (routing r is a total tag lookup),
U (forget columns) and R (rebuild columns by routing) are inverse
bijections between N-zone derivations of routed endsequents and
one-pool derivations — same rule instances, same positions; provability
and per-zone linearity coincide with the pooled reading. Corollary: the
engine threads ONE union pool and materializes zone columns as
router-views at construction boundaries; the pool plumbing is one-time
and zone-count-agnostic, so DECLARING a zone is calculus data. sill's
`loc` (`Γ;Δ;Λ ⊢ C`) is the instance; aux zones are fenced to
linear-policy (affine zones = future work, rule-level `@affine` is the
existing mechanism).

## 2. The product stamp: lex-committed, Pareto-explored

sill's scheduler axis is the product (time, dist) — one stamp value
carrying both, componentwise tropical (⊗ adds per axis, ⊔ joins per
axis: a conclusion waits for the last input in time AND carries the
dearest accumulated cost). The product order is partial; the scheduler
needs decisions. The factorization:

- **Committed settle runs on the LEXICOGRAPHIC completion** (time
  primary, dist tie-break) — a total order, so the scheduler invariants
  that assumed totality (min-activation heap, the B&B prune contract
  `cmp ≥ 0`, the FIFO invariant pair, Zeno frontier progress, tied-set
  formation) survive — with ONE exception, located exactly. The
  referee-grain analysis (settle-optimality §8.4) is the **C4 split**:
  the scalar contract's C4 (merge = the order max) factors into C4a
  (merge is an ⊑ₗ-upper bound — all the core lemmas need; HOLDS, since
  the componentwise join dominates per axis and lex refines the product
  order) and C4b (merge is selective; FAILS — `(3,5)⊔(4,2) = (4,5)`).
  The one C4b-dependent step is L2's whole-bind rescue: choice-freedom
  no longer excuses `!_W`, and the failure is executable (a choice-free
  product program whose forced join drops below the fired frontier —
  the L2× witness, sill-product.test.js). So T1×/T2× carry
  whole-bind-freedom as a hypothesis; everything else survives, and
  C4b is exactly coalesce-safety (the engine's function-valued-merge
  fence). The committed run realizes the lex-least completion.
- **The Pareto frontier lives in the exploration layer.**
  `settleFrontier` = `settleExplore` (all chooser worlds) + the
  dominance filter, with dominance DERIVED FROM THE JOIN: a ⊑ b iff
  a ⊔ b = b. No new algebra slot, and for a total order the frontier
  degenerates to the unique least completion — the scalar case is the
  degenerate instance, not a special case. A leaf's cost is ⊔ over its
  final facts' stamps (the completion vector). This is the frontier *of
  the committed worlds*, and that qualification is load-bearing: an
  unfocused derivation can strictly `⊑ₚ`-dominate every committed leaf
  (witness W-gap, kernel-certified — choice-free, contended at distinct
  activations, disjoint frontiers), and the committed frontier is the
  true frontier exactly under *tied-contention* (every dependent
  relaxation pair co-activated) — the adequacy proposition, paper §8.4.

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

## 3. The axis-confounding argument: transport is a rule

"Transport takes time" couples the axes. The lawful coupling is the
rule shape

    transport: (A @@ L) * road L L' * !dist L L' T D
      -o { (A @@ L') }@(T ~ D).

— the edge's cost enters ONCE per hop, each component into its own
axis of the product grade. The tempting alternative is a TYPE-LEVEL
coercion "a distance IS a delay" — embedding the dist grade into the
time axis. The objection is SEMANTIC, not algebraic. Algebraically the
embedding `d ↦ d : (dist, +, 0) → (time, +, 0)` is a monoid
homomorphism, and coercions between grade axes are exactly the graded-
monad morphisms of Fujii–Katsumata–Melliès — plentiful and lawful; no
action law (THY_0018 §2) refutes it. What the coercion does is
confound the axes: a hop of cost (T, D) coerced contributes T + D to
the time axis while D still rides the dist axis, so after two hops the
"time" component reads t + T₁ + D₁ + T₂ + D₂ — the availability time
of nothing — and lex scheduling over it no longer realizes physical
availability. The two objectives the product exists to keep apart
(when is it ready / what did it cost) collapse into one, and the
Pareto frontier degenerates to a line. Which morphisms preserve the
MODEL is a semantic question, and for (time, dist) only the per-axis
translation `(t, δ) ⊳ (T, D) = (t + T, δ + D)` does. Hence the
non-trivial coupling is program structure — a rule, firing once per
edge, whose cost data are ordinary persistent facts.

## 4. Related work (positioning)

The N-zone structure itself is Reed-style adjoint logic
(Licata–Shulman–Riley 2017; Pruiksma–Pfenning 2018) — prior art, not a
contribution; those systems carry per-formula mode annotations, and
Celf/CLF implementations keep N separate multisets. The routed-column
equivalence (§1) — zone membership from the head connective, N zones ≃
one union pool, invertible maps — is, to our knowledge, not previously
stated. sill's `A @@ L` is NOT HyLL's `A @ w` (Despeyroux–Chaudhuri):
HyLL's @ is a modal connective with real introduction/elimination
rules; sill's loc has no sequent rules — location is resource
identity, enforced by zone accounting and per-fiber linearity, closest
in spirit to a linear (non-exponential, rule-free) reading of SELL's
indexed `!^l` (Nigam–Miller). Product grade algebras are standard
(Granule, Katsumata); multi-priced timed automata compute Pareto
curves directly (Bouyer–Brinksma–Larsen). The lex/Pareto factorization
of §2 — commit under the lexicographic completion so every total-order
scheduler invariant survives, recover the frontier in the exploration
layer with dominance derived from the join — appears in neither body
of work.
