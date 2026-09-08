---
title: "The Parametric Forward-Chaining Judgment ⊢_fwd"
created: 2026-09-08
modified: 2026-09-08
summary: "The forward engine's execution-tree judgment Σ; Φ ⊢_fwd T : Δ ⇒ Δ' restated PARAMETRICALLY over a structural-family record 𝔉 = (CS, P, D, X) with four axioms — persistent-proving soundness, structural (copySource/promotion) discipline, the forced-or-deferred existential discipline, and the monad boundary contract — plus completeness conditions on the match relation. The axioms are discharged TWICE: for LNL (all four components live) and for SAX (all four null — the generic baseline), which upgrades 'the four family hooks are the LNL-shaped part of the protocol' from an empirical P1 finding to a theorem-level statement: nulling 𝔉's components specializes the judgment, and each axiom's load-bearing/vacuous status is decided by the instance. Axiom A3 was FALSIFIED by a real engine bug (TODO_0307 witness capture) before being restored — the axioms carve the actual soundness surface, not a post-hoc rationalization. Subsumes TODO_0045's core; TODO_0042 (explore soundness/completeness) builds on this judgment."
tags: [linear-logic, forward-chaining, multiset-rewriting, engine-metatheory, structural-families, sax, existentials, modes, certificates]
category: "Engine metatheory"
unique_contribution: "Three things not in prior CALC docs or the literature's forward-chaining accounts (CLF/Ollibot/Ceptre state their judgments for ONE fixed context discipline): (1) the judgment is parametric over an axiomatized family record whose code-side twin is the cc port (cc.family.engine + derived contextStructure), and the parametricity is NON-VACUOUS because two structurally different families discharge it — LNL with all components live, SAX with all components null; (2) the specialization theorem: the generic engine baseline IS the judgment at 𝔉 = (CS_single, null, null, null), making 'which axioms a calculus pays for' an instance property — A2 is vacuous exactly when copySource is null, A3 exactly on the binder-free fragment; (3) the falsifiability record: axiom A3's forced-or-deferred discipline names 'witness capture' as a violation class, and the engine VIOLATED it for five months (TODO_0307: wildcard state lookup answering unforced goals — 31 worlds collapsed to 2 unsound ones) — the axiom set is exactly strong enough that its violation produced observable unsoundness, and its restoration (eager eigenvariable introduction) is the axiom's operational content."
references:
  - "TODO_0309 P3 (this deliverable); P1's interface-extension list (the empirical measure of the old judgment's LNL-shape — each P0 fix generalizes a rule here, none adds a sax case)"
  - "TODO_0045 (subsumed: the typed tree constructors are this judgment's term language)"
  - "TODO_0042 (follow-on: explore() soundness/completeness against ⊢_fwd via the QCHR ω^{∃∀} game-tree correspondence; the per-rule match enumeration gap is the known deficit)"
  - "TODO_0307 (the A3 falsification episode: forced-or-deferred, eigenvariables-at-introduction, witness capture; the mode discipline is standard theory — Mercury modes, Curry residuation — deliberately cited, not claimed)"
  - "THY_0032 (contextStructure derived from @position_modes/@structural — CS's provenance), THY_0033 (zone-count-agnostic pool routing — why CS needs no per-zone engine axioms)"
  - "THY_0036 (the confluence certificate is a derived property of ⊢_fwd trees), TODO_0294/0295 (A4's checker: elaborated @fire trees, SLD certificates)"
  - "RES_0143 F1 (the cc port schema — the code-side signature of 𝔉)"
  - "Watkins et al. CLF (TR 2002) / Simmons–Pfenning Ollibot / Martens Ceptre — the fixed-discipline forward judgments this parametrizes"
---

# The Parametric Forward-Chaining Judgment ⊢_fwd

## 1. Why parametric

TODO_0045 planned the execution-tree judgment with LNL's two zones baked
into the statement — proving it as written would have recreated at
theorem level the hardcoding TODO_0086/0285 removed at code level. A
parametric statement is only honest if a SECOND instance discharges it:
that instance is SAX (TODO_0309 P1), whose family record is maximally
degenerate — all four engine components null, `copySource: null`. The
two instances bracket the design space: everything live vs. everything
null, with the six shipped calculi between them.

## 2. The parameter 𝔉 = (CS, P, D, X)

A structural family supplies:

- **CS** — the context structure: zone list, consumable zones,
  `copySource` (the contraction+weakening zone feeding persistent
  proving, or null), per-zone structural admissibilities. DERIVED from
  the family's `@position_modes` + `@structural` declarations
  (THY_0032); the engine threads one union pool with router-materialized
  zone views (THY_0033), so CS induces no per-zone engine axioms.
- **P** — the persistent prover: a partial function from (persistent
  context Φ, goal g) to derivations.
- **D** — the dynamic-rule component: recognizing state-resident rule
  facts (match) and their saturation (drain).
- **X** — the existential resolver for ∃-consequents.

P, D, X are nullable. The CODE twin of this signature is exactly
`cc.family.engine` + the derived `contextStructure` — one row of the cc
port schema (RES_0143 F1). Nothing else in the engine is
family-dependent; that claim is enforced, not aspirational
(layer-dag: the engine imports no family module; the hooks arrive as
data).

## 3. The judgment and its term language

    Σ; Φ ⊢_fwd T : Δ ⇒ 𝔏

Σ = compiled rules, Φ = the copySource-zone content (plus derived
facts), Δ = the linear multiset, T = an execution tree, 𝔏 = its leaf
multiset-set. The constructors (TODO_0045's term language, as built by
`explore()` and consumed by the serializers):

- `leaf(Δ)` — quiescence: no rule instance is enabled. Sound only
  relative to MATCH COMPLETENESS (§4, C1–C3): a leaf claims an
  exhaustiveness fact.
- `step(r, θ, π⃗, T')` — one committed firing: consume r's linear
  patterns under θ from the consumable zones, discharge each
  persistent premise with a P-derivation π, resolve ∃-slots via X,
  produce into Δ and Φ. The step's semantic anchor is A4: it
  elaborates to a kernel-checked @fire derivation.
- `fork(T₁…Tₙ)` — internal choice: one child per ⊕ alternative of the
  fired rule.
- `branch(T₁…Tₙ)` — rule-choice nondeterminism: one child per enabled
  candidate the search explores.
- `cycle / memo / bound / dead` — back-edge, revisit, depth bound,
  constraint-pruned (dead is sound only if the pruner is: the solver
  may cut a branch only when its guards are jointly unsatisfiable).

## 4. The axioms

**A1 (persistent proving).** P is sound — P(Φ, g) defined implies
Φ ⊨ g in the ambient clause/theory semantics — and MONOTONE: Φ ⊆ Φ'
preserves provability (goals are positive; theories and FFI are pure).
Monotonicity is what lets produced persistent facts never retract an
enabled step (used by THY_0036's diamond).

**A2 (structural discipline).** Facts in copySource admit contraction
and weakening — P consumes nothing; consumable-zone facts are consumed
exactly once per match; produced banged facts promote into copySource.
When copySource is null, A2 is VACUOUS: no promotion target exists and
the loader must fence banged production (sax does).

**A3 (existential discipline — forced or deferred).** X introduces
each ∃-witness as an EIGENVARIABLE at its introduction point — an
existential is never an open pattern hole. Determination (computing
the witness now) is admissible only when FORCED: the goal's declared
mode is functional and its input positions are ground. Anything else
DEFERS: the goal persists as a constraint fact over the fresh
eigenvariable, and branching happens where it belongs (⊕ guards).
The named violation class is WITNESS CAPTURE: answering an unforced
goal from an arbitrary matching fact — choice disguised as
computation. On the forced prefix, resolution is confluent (same θ
regardless of goal order and computing tier). The mode discipline
itself is standard (Mercury modes; Curry residuation) — cited, not
claimed; what this axiom fixes is its position in ⊢_fwd's soundness
surface.

**A4 (monad boundary).** Forward steps live under the graded lax
modality: the backward/forward boundary admits a step only as an
elaborated, kernel-checked @fire derivation (TODO_0294), with
clause-derived persistent premises carrying SLD certificates
(TODO_0295). The judgment's `step` constructor and the checker's
re-derivation are the same object seen from both sides — ⊢_fwd is
checkable, not merely definable.

**C1–C3 (match completeness — conditions, not axioms).** `leaf` and
`branch` are only as honest as the match relation: (C1) committed
per-pattern matching must be completed by backtracking join search on
non-functional joins; (C2) no candidate index may hide a match the
matcher would find (the D13 contract); (C3) mutation-carried indexes
must be invalidated across search. These are exactly TODO_0309 P0's
findings 1–3 — the empirical content of writing this section is that
each was a LATENT VIOLATION found by the second family, fixed
generically.

## 5. Discharge: LNL (everything live)

- **P** = state lookup → memo cache → SLD clause resolution
  (family/lnl/lib/persistent.js). Lookup is Φ-membership; SLD is
  sound w.r.t. Φ's clause set; the FFI tier is opt-layer and
  ADVISORY — clause fallback preserves A1, and the noFFI arms are the
  standing empirical discharge of FFI≡clause.
- **D** = loli match/drain: a dynamic rule is a state-resident linear
  implication; firing it consumes the loli fact — an ordinary `step`
  whose rule came from Δ. Drain saturates persistent-triggered lolis.
- **X** = existential.js. A3 holds POST-TODO_0307: eager eigenvariable
  introduction + evar rigidity. It did NOT hold before — the per-goal
  loop left failed goals' outputs as blank pattern slots, and wildcard
  state lookup captured witnesses (31 feasible worlds → 2 unsound
  ones, undetected for five months because every observed
  configuration took the sound path). The axiom is falsifiable, was
  falsified, and its restoration is the S0 fix. That episode is the
  strongest evidence this axiom set carves the real soundness surface.
- **CS**: two zones, copySource = cartesian; promotion = producePers.

## 6. Discharge: SAX (everything null) and the specialization theorem

With 𝔉 = (CS_single, null, null, null) the judgment SPECIALIZES to
the generic engine baseline:

- **P = null** ⇒ persistent premises are discharged by Φ-membership
  alone. A1 is immediate (membership is entailment for atomic facts;
  monotone by persistence). Write-once cells make every membership
  stable — the same fact THY_0036 leans on.
- **D = null** ⇒ no dynamic rules; the forward fragment contains no
  state-resident implications (fenced at load).
- **X = null** ⇒ the binder-free fragment: SNAX projection addressing
  keeps continuations first-order, so ∃-consequents never arise and A3
  is vacuous by fragment, not by luck.
- **copySource = null** ⇒ A2 vacuous; banged production fenced.
- **A4** is family-independent and unchanged.

This upgrades P1's empirical finding — "the four hooks are the
LNL-shaped part of the protocol" — to a statement OF the judgment:
each axiom's load-bearing/vacuous status is decided by the instance,
and the all-null instance is not a degenerate afterthought but a real
calculus with a real machine and a checked confluence certificate.

## 7. What the parametricity is measured by

The P1 interface-extension list is the audit trail: every place the
implicit old judgment was LNL-shaped surfaced as a REQUIRED extension
when sax arrived (exact axioms with companions, explicit cut,
null-copySource guards, C1–C3), and every fix generalized a rule of
⊢_fwd rather than adding a sax case. The residual gaps recorded there
(per-rule match enumeration; exact-hash companions; persistent-witness
commitment under tier-2) are ⊢_fwd's known completeness deficits and
TODO_0042's opening position. THY_0036's confluence certificate is a
derived property of ⊢_fwd trees: under its discipline, `branch` nodes
are semantically redundant — which is precisely why explore may
collapse them under a certificate.
