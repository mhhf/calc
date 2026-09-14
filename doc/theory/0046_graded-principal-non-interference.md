---
title: "Graded Principal Non-Interference: Isolation and Zero-Stake Erasure for [K](!_w A)"
created: 2026-09-14
modified: 2026-09-14
summary: "The security companion to THY_0045's cut theorem (TODO_0276 'prove fresh (b)'). Non-interference for the combined principal × weight modality, proved as an induction over CUT-FREE derivations — the analytic structure THY_0045 cut admissibility supplies. Three parts, orthogonal by construction: (NI-1) PRINCIPAL ISOLATION — in any cut-free derivation of Γ;Δ ⊢ [K]C, no hypothesis held by a principal K'≠K (without an active delegation K'⪰K) is ever principal in a rule above the [K]R promotion, so K's conclusions depend only on K's own zone plus objective/ambient facts; the [K]R restriction ·|_K is the whole engine, exactly Garg–Pfenning's 'k0's conclusions depend only on Γ|_k0 + objective facts unless k0 delegates' now carried by a grade. (NI-2) ZERO-STAKE ERASURE — a !_0 A hypothesis can only fire the weakening rule (dereliction needs w=1, split needs a positive residual), so it is never resource-contributing and is erasable everywhere; the weight-axis instance of the same projection, matching GraD's grade-0 irrelevance (Choudhury POPL 2021). (NI-3) ORTHOGONAL COMPOSITION — NI-1 and NI-2 project along disjoint grade positions (Lemma O, THY_0045 §4), so the combined statement is their composite with no cross term: a holding [K'](!_w A) with K'≠K or w=0 contributes nothing to a K-observable positive-weight goal. Delegation (speaks-for K'⪰K) is the single audited leak, and it is exactly the rule that moves a hypothesis across the ·|_K boundary."
tags: [linear-logic, proof-theory, graded-types, graded-modality, authorization, ownership, principals, cut-elimination, soundness, governance, modal-logic]
category: "Proof theory"
unique_contribution: "The first non-interference theorem for a modality combining a principal index with a quantitative grade, and the observation that the two isolations (across principals, across zero stake) are the SAME projection principle applied to the two orthogonal grade axes — so principal non-interference (Garg–Pfenning, ungraded) and grade-0 irrelevance (GraD, single-axis) compose with no new proof burden by the THY_0045 orthogonality lemma. Two specific results not in the literature: (1) principal isolation carried by a GRADE (the [K]R restriction ·|_K) rather than a bespoke says-modality, unifying it with the weight-erasure argument; (2) the identification of delegation/speaks-for as exactly the rule that crosses the ·|_K boundary — the unique, syntactically localized exception to isolation, making 'the audited leak' a proof-theoretic object. Rests on THY_0045: non-interference is an induction over cut-free derivations, enabled by the subformula property that cut admissibility delivers."
references:
  - "THY_0045 — Principal-Graded Possession: Cut Admissibility for [K](!_w A) (the cut theorem this consumes; Cor 9 subformula property; §3 the calculus; §4 Lemma O orthogonality)"
  - "THY_0022 — Fenced Grade Algebras; THY_0023 — till Metatheory (the parametric graded-cut core and the count-fence measure)"
  - "THY_0015 — Grade-0 Staging ({A}_{q·a}; §3 orthogonality; the grade-0-as-irrelevance neighbour)"
  - "THY_0013 — The Indexed Lax Monad {A}_a (the SELL promotion restriction Γ_≤a that becomes ·|_K)"
  - "TODO_0276 — Governance Layer ('prove fresh (b): non-interference for the graded extension'; the four-judgment says/knows/has table; delegation = speaks-for, open question 3); RES_0003 — Authorization Logic (Garg BL non-interference; speaks-for)"
  - "Garg & Pfenning (2011). Stateful Authorization Logic (BL non-interference: authorization conclusions depend only on the principal's own view + objective facts)"
  - "Garg, Bauer, Bowers & Pfenning (2006). A Linear Logic of Authorization and Knowledge. ESORICS (says/knows; the non-interference SHAPE this grades)"
  - "Choudhury, Eades, Eisenberg & Weirich (2021). A Graded Dependent Type System with a Usage-Aware Semantics (GraD). POPL (Lemma 6.2: grade-0 heap entries irrelevant — the weight-axis analogue of NI-2)"
  - "Abadi, Burrows, Lampson & Plotkin (1993). A Calculus for Access Control in Distributed Systems (speaks-for; A ⪰ B delegation)"
---

# Graded Principal Non-Interference for [K](!_w A)

**Status.** On-paper, in the standing of THY_0045 (hand-checked; the modalities
are governance P1/P2, unbuilt — the proof is judgmental over the calculus
specified in THY_0045 §3). This discharges TODO_0276's second parked obligation,
**"prove fresh (b): non-interference for the graded extension."**

Non-interference is the *security* companion to cut admissibility (THY_0045 was
the *soundness* companion). Where cut says "composing governance operations adds
no theorems," non-interference says "a principal's conclusions cannot be swayed
by holdings it cannot see." The proof is an induction over **cut-free**
derivations — which is available only because THY_0045 makes every derivation
cut-free with the subformula property (Cor 9). So (b) genuinely rests on (a).

## 1. What non-interference means here

In an authorization logic, non-interference (Garg–Pfenning 2011; RES_0003) is the
statement that *principal `k₀`'s authorization conclusions depend only on
`Γ|_{k₀}` plus objective facts, unless `k₀` explicitly delegates.* In the
governance calculus the principal is a **grade** (THY_0045 §2), the ownership
datum is `[K](!_w A)`, and the guarantee splits along the two orthogonal grade
axes:

- **across principals** — K's conclusions are isolated from K'≠K's private
  holdings;
- **across weight** — a zero stake `!_0 A` is inert (holding 0% of something
  grants no capability).

The whole theorem is these two isolations plus the fact (Lemma O) that they
**compose without interacting**. The single controlled exception is
**delegation** (speaks-for), which is exactly — and only — the rule that moves a
hypothesis across the principal boundary.

## 2. Projections and the delegation rule

**Ownership label.** Every hypothesis `H ∈ Γ ∪ Δ` has an owner:
`owner(H) = K'` if `H` is `[K']B`-shaped (held by K', or in K''s says/knows
zone); `owner(H) = ⊥` (**objective/ambient**, grade-0 principal, `[0]B = B`,
visible to all — Fact P2 of THY_0045). Objective facts are the shared world
state (`current n T`, prices, block data); K-owned facts are K's private
resources and affirmations.

**K-projection.** `(Γ; Δ)|_K` keeps every ambient hypothesis and every hypothesis
owned by `K`, dropping those owned by `K'≠K`. This is the context restriction
`·|_K` that THY_0045 §3's `[K]R` already imposes on its premise (the SELL/THY_0013
promotion restriction `Γ_{≤a}`, instantiated at the principal algebra).

**Positive-weight projection.** `(Γ; Δ)|_{>0}` drops every `!_0 A` hypothesis
(zero stake).

**Delegation (speaks-for) — the sole boundary-crossing rule.** Extend the
calculus of THY_0045 §3 with the ABLP speaks-for axiom, guarded by an objective
delegation fact `K' ⪰ K` ("K' speaks for K"):

```
Γ; Δ, [K] A ⊢ J     ! (K' ⪰ K)
────────────────────────────────  [⪰]  (delegation / speaks-for)
Γ; Δ, [K'] A ⊢ J
```

`[⪰]` retags a `K'`-held hypothesis into `K`'s zone when `K' ⪰ K` is an
objective fact — the ONE way a hypothesis crosses the `·|_K` boundary. (Its
transitivity `K'' ⪰ K' ⪰ K ⟹ K'' ⪰ K` is a property of the `⪰` fact base, not a
new rule; revocation is deleting the `!(K'⪰K)` fact — a state operation, TODO_0276
open question 3. Delegation is cut-compatible: `[⪰]` is a left rule with an
objective side condition, so it permutes exactly as THY_0045 §5's commutative
cases — it does not disturb the cut proof.)

## 3. The theorem

**Theorem NI.** Let `𝒟` be a cut-free derivation of `Γ; Δ ⊢ [K] C` (a
*K-observable* goal: succedent in K's name, or ambient). Then:

**(NI-1) Principal isolation.** Every hypothesis that is *principal* in some rule
of `𝒟` is ambient, or owned by `K`, or owned by some `K'` with an active
delegation `K' ⪰ K` used at a `[⪰]` step. No `K'`-owned hypothesis (`K'≠K`,
undelegated) is ever principal in `𝒟`.

**(NI-2) Zero-stake erasure.** Every `!_0 A ∈ Δ` is erasable: `Γ; Δ ⊢ [K]C` iff
`Γ; Δ ∖ {!_0 A} ⊢ [K]C`, height-non-increasing.

**(NI-3) Orthogonal composition.** NI-1 and NI-2 hold simultaneously and
independently: a holding `[K'](!_w A)` with `K'≠K` (undelegated) **or** `w = 0`
contributes to no rule producing a K-observable positive-weight conclusion. The
combined projection `(Γ;Δ)|_K|_{>0}` is well-defined (the two projections
commute) and `Γ;Δ ⊢ [K]C` iff its projection does, modulo delegated resources.

*Proof.*

**(NI-1)** Induction on `𝒟`, downward from the root. The succedent `[K]C` is
introduced by `[K]R` (the only right rule concluding `[K]·`; by cut-freeness and
the subformula property, THY_0045 Cor 9, no cut manufactures it otherwise). Its
premise is restricted to `Γ|_K; Δ|_K ⊢ C` — ambient + K-owned only. So it
suffices to show no undelegated `K'`-owned hypothesis becomes principal *below*
the root either. Such a hypothesis `[K']A` can be acted on only by:

- `[K']L` (dereliction), exposing its body `A` into the general linear context.
  For `A` to reach the `[K]R` premise it must survive the `·|_K` restriction; but
  `A` carries owner `K'` (its provenance is not erased — it entered via a
  `K'`-modality), so `·|_K` drops it unless a `[⪰]` step with `K' ⪰ K` retagged
  it into K's zone first. Absent delegation, `A` is stranded below `[K]R`: if
  `[K']A` is persistent/objective-derived it is weakened (Lemma 7a of THY_0023,
  contributing nothing); if linear it cannot be discharged toward `[K]C` (linear
  leftovers forbid silent weakening — THY_0023 Lemma 7d), so `𝒟` with that
  hypothesis *present and principal* does not exist. Either way it is not
  principal in a rule feeding `[K]C`.
- `[⪰]` (delegation), which retags it to `[K]`-owned under `!(K'⪰K)` — the
  admitted exception, recorded in the theorem.

No other rule inspects a `[K']` hypothesis. Hence every principal hypothesis is
ambient, K-owned, or delegated. This is precisely Garg–Pfenning's statement with
`Γ|_{k₀}` = `·|_K` and "objective facts" = the ambient (grade-0) zone; the novelty
is that `·|_K` is a **grade restriction** (THY_0045 §2), not a bespoke modal
side condition — so the identical argument covers the `says` (`monad(K,·)`) and
`knows` (`bang(K,·)`) variants, whose promotion premises carry the same `·|_K`.

**(NI-2)** A `!_0 A` hypothesis can be principal only in a `!_w`-left rule
(THY_0045 §3). But `!_w D` (dereliction) requires `w = 1`, and `!_w L(split)`
requires a residual `w₀ = w ⊖ w'` with `w', w₀ ≥ 0` summing to `w > 0` to expose
a usable share — both underivable at `w = 0` (the weight fence, THY_0045 §5.1
vacuity). The only applicable rule is `!_0 W` (weakening). So `!_0 A` is never
resource-contributing: permute its `!_0 W` down to a leaf and delete it,
height-non-increasing. This is GraD's grade-0 irrelevance (Choudhury et al. 2021,
Lemma 6.2) as a syntactic erasure on the weight axis — zero ownership is no
ownership.

**(NI-3)** By Lemma O (THY_0045 §4): the principal grade appears only on
`[K]`-nodes and the weight grade only on `!_w`-nodes, and no rule couples them.
The NI-1 argument inspects only principal positions and the `·|_K` restriction;
the NI-2 argument inspects only weight positions and the `!_w` rules. They range
over disjoint parts of every rule, so they neither block nor enable one another:
the projections commute, and their composite `|_K|_{>0}` is the combined
non-interference. In particular for the combined datum `[K'](!_w A)`: if `K'≠K`
(undelegated) NI-1 strands it; if `w=0` NI-2 erases the inner stake; the two
verdicts are independent. ∎

## 4. Corollaries (the governance security pack)

- **No cross-principal theft, sharpened.** THY_0045 §6 gave underivability
  (`[K₁]A ⊬ [K₂]A`); NI-1 gives the stronger *isolation*: even embedded in a
  large governance state, `K₁`'s private holdings never participate in deriving
  `K₂`'s conclusions. An attacker's resources are not merely insufficient — they
  are invisible to the victim's derivations.
- **Zero-stake grants nothing.** A principal holding `!_0 share` (or dust) has no
  more governance power than one holding none (NI-2): the tally/consensus a
  conclusion draws on ignores zero-weight ballots by construction, not by an
  explicit `w > 0` check. (The quantitative refinement — that a `!_w` holding's
  *influence is metered by w* — is a bilinearity property of the stake-weighted
  value `Σ share·vote`, TODO_0276 "sybil/split-invariance (f)"; NI-2 is its
  boundary case at `w = 0`.)
- **Delegation is the audited leak.** Every cross-principal influence is
  witnessed by a `[⪰]` step against an objective `!(K'⪰K)` fact (NI-1). Auditing
  "who could affect K's decision" = enumerating active delegations into K — a
  finite, on-chain-visible set. Liquid democracy (TODO_0276 open question 3) is
  thus non-interference *modulo the delegation graph*, and revocation
  (deleting `!(K'⪰K)`) restores full isolation immediately.
- **Objective/ambient facts are the only shared channel.** By NI-1 the sole
  medium through which principals co-reason is the grade-0 zone — the shared
  world state. This pins the attack surface for governance: integrity reduces to
  the integrity of the objective facts (`current n T`, prices, block data), which
  is versioning's job (TODO_0276 pillar 2), not authorization's.

## 5. Relation to prior work; status; mechanization

**Prior work.** Garg–Pfenning (2011) prove non-interference for BL (stateful
authorization) — ungraded, and with `says` a bespoke modality. GraD (Choudhury et
al. 2021) prove grade-0 heap irrelevance — single-axis, no principals. Neither
combines the two, and neither carries principal isolation *as a grade*. The
contribution here is (i) unifying principal isolation and stake erasure as one
projection principle on two orthogonal grade axes, (ii) obtaining the combined
theorem for free from THY_0045's orthogonality lemma, and (iii) localizing the
sole exception to a single boundary-crossing rule `[⪰]`.

**Scope / honest boundary.** On-paper, hand-checked, unmechanized (as THY_0045).
The `says`/`knows` variants are covered by the same `·|_K` argument (§3 NI-1
remark). NOT covered here: the quantitative *influence-metering* theorem
(bilinearity of stake-weighted value — a different, arithmetic statement, TODO_0276
(f)); a *probabilistic* non-interference if weight is read as probability rather
than share (the multiplicative weight instance — out of scope, cf. THY_0045 §5.1
judgment call). Delegation is treated as a single speaks-for level; transitive and
contextual (per-subterm) delegation with veto (TODO_0276 memhub heritage) refine
the `⪰` fact base but not the isolation argument.

**Mechanization.** The `dill` calculus (THY_0045 §7, `calculus/dill/`) realizes the
NI-1 core: `tests/engine/dill-possession.test.js` pins the isolation as a
*refutation* — `says k1 a ⊬ says k2 a` (K1≠K2) and the non-degeneracy
`says k a ⊬ a` are exactly "K's affirmation does not reach K'≠K and does not leak
to the objective zone." The `[⪰]` delegation rule, the `!(K'⪰K)` fact base, and
the full NI-2 zero-stake erasure on a first-class weight bang are the P1
additions the `dill` instance does not yet carry (its inner grade is gill's
`!!_d`, whose cost-0 dereliction `says k (!!_0 a) ⊢ says k a` is the NI-2 shadow
already tested). The differential NI-1 test (context-with vs context-without an
undelegated foreign holding) and the NI-2 equivalence (`Γ, !_0 A ⊢ G ⟺ Γ ⊢ G`)
are the next fuzz targets once the weight bang and delegation land.
