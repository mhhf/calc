---
title: "The Delay-Graded Lax Monad: Timed Forward Chaining over the Tropical Dioid"
created: 2026-08-18
modified: 2026-08-21
summary: "CLF's lax monad {A} graded by a delay from the tropical (max,+) dioid: availability stamps A@t on hypotheses combine by max (coeffect), delays {B}@d compose by + (effect), and firing stamps outputs at max(inputs)+d. Sequent rules, cut-elimination sketch, five metatheorems plus a trace≅term observation: ASAP scheduling computes principal grades; conflict-free programs are timed-confluent; fused rules are uninterruptible by construction (fission = the honest model of interruption); the timed trace is a graded CLF proof term, prunable to a Merkle accumulator; the settle bridge is a sound (not complete) oracle for the calculus."
tags: [linear-logic, lax-monad, clf, graded-types, forward-chaining, proof-theory, cut-elimination, time, tropical, till]
category: "Timed Rewriting"
paper: "FULLY compiled into doc/paper/till (calc c712242b, 2026-08-23) — the paper's spine: gap/contributions (paper §1), grade algebra (§2), judgments+rules+stamps/promotion (§3), metatheorems (§§4–6), related work (§10); the §8 cut-elim sketch enters via THY_0023's full proof."
unique_contribution: "Four claims not found in the literature (novelty audit 2026-08-18, see §10): (1) a lax/monadic modality graded by a delay, with sequent rules and a cut-elimination argument — graded exponentials !_r have sequent calculi with cut elim (BLL through CSL 2025), and Granule has a graded possibility ◇_r as a type system, but NO graded monadic modality has a sequent calculus or cut elimination anywhere (30+ papers, 3 adversarial searches); (2) activation-as-max-of-stamps presented as the tropical dioid acting inside a logic's promotion rule — timed MSR (Kanovich et al.) uses a global clock fact instead; (3) in-flight processes represented as let-nodes of the monadic proof term, making 'the job' a trace object rather than a state token, with atomicity of fused rules a THEOREM; (4) the timed trace = graded proof term isomorphism with prefix-pruning to a Merkle accumulator."
references:
  - "TODO_0265 — timed graded rewriting (the till calculus; this document is its Phase 0 THY-A)"
  - "THY_0013 — The Indexed Lax Monad {A}_a"
  - "THY_0015 — Grade-0 Staging and Stratified Cut Elimination ({A}_{q·a})"
  - "THY_0019 — Timed Matching and the Settle Scheduler (THY-B companion)"
  - "THY_0023 — till Metatheory (the full proofs of §8's sketch: cut admissibility, η, counted-bang completeness, work adequacy)"
  - "THY_0021 — Weighted Additive Disjunction (the orthogonal probability grade on this monad)"
  - "RES_0052 — CLF and the lax monad (monadic proof terms, concurrent equality)"
  - "RES_0135 — Dimensioned / group-graded linear logic (effect–coeffect duality, finance grades)"
  - "Fairtlough & Mendler (1997). Propositional Lax Logic. Information and Computation."
  - "Pfenning & Davies (2001). A Judgmental Reconstruction of Modal Logic. MSCS."
  - "Watkins, Cervesato, Pfenning & Walker (2002). A Concurrent Logical Framework I. CMU-CS-02-101."
  - "Katsumata (2014). Parametric Effect Monads and Semantics of Effect Systems. POPL."
  - "Gaboardi, Katsumata, Orchard, Breuvart & Uustalu (2016). Combining Effects and Coeffects via Grading. ICFP."
  - "Orchard, Liepelt & Eades (2019). Quantitative Program Reasoning with Graded Modal Types. ICFP (Granule — graded possibility ◇_r, the nearest neighbour)."
  - "Fujii, Katsumata & Melliès (2016). Towards a Formal Theory of Graded Monads. FoSSaCS."
  - "Hanukaev & Eades (2025). Combining Dependency, Grades and Adjoint Logic. CSL (graded !_r sequent calculus + cut elim — necessity side only)."
  - "Benton, Bierman & de Paiva (1998). Computational Types from a Logical Perspective. JFP."
  - "Nakano (2000). A Modality for Recursion. LICS."
  - "Kanovich, Kirigin, Nigam, Scedrov & Talcott (2016). Timed Multiset Rewriting... FORMATS."
  - "Das, Hoffmann & Pfenning (2018). Parallel Complexity Analysis with Temporal Session Types. ICFP."
  - "Jensen, Kristensen & Wells (2007). Coloured Petri Nets and CPN Tools... STTT."
  - "Baccelli, Cohen, Olsder & Quadrat (1992). Synchronization and Linearity. Wiley."
  - "Nielsen, Plotkin & Winskel (1981). Petri Nets, Event Structures and Domains. TCS."
---

# The Delay-Graded Lax Monad: Timed Forward Chaining over the Tropical Dioid

This is THY-A of TODO_0265: the proof theory under the `till` calculus (timed ILL). The
operational companion — matching, activation windows, the `settle` scheduler — is
THY_0019 (THY-B). Notation: `A@t` (availability stamp), `{S}@d` (delayed lax monad),
both postfix `@`, deliberately the same glyph: stamp and delay are the two readings of
one tropical algebra under the effect/coeffect duality (RES_0135 §2; Gaboardi et al. 2016).

## 1. The gap

CLF (Watkins et al. 2002) marks the boundary between backward proof search and forward
multiset rewriting with a lax monad `{A}`; the monad is UNGRADED — a derivation records
that forward chaining happened, but not *how long it took*. Graded modalities are well
studied on the EXPONENTIAL side (`!_r A`: BLL, coeffect calculi, QTT) where cut
elimination is settled; graded monads are standard in semantics (Katsumata 2014); and
Granule even types a graded possibility `◇_r` — but as a bidirectional type system,
with no sequent calculus and no cut-elimination theorem. No published system grades
the LAX modality of a sequent calculus by a delay, and timed multiset rewriting
(Kanovich et al. 2016) obtains time with a global `Time@T` fact and a `Tick` rule — a
design with no proof-theoretic reading of durations and no representation of in-flight
work. This document closes the square: time enters CLF-style forward chaining as a
GRADE, not as a clock fact.

## 2. The grade algebra: one tropical dioid, two roles

Fix the tropical dioid `𝕋 = (ℚ≥0, ⊕, ⊗)` with `⊕ = max` (unit 0, by convention the
absent/ambient stamp) and `⊗ = +` (unit 0). Its two fragments play the two roles:

- **Durations (effect)** `D = (ℚ≥0, +, 0, ≤)` — an ordered commutative monoid. Delays
  compose by `+` along a production chain (critical path).
- **Time points (coeffect)** `T = (ℚ≥0, max, 0, ≤)` — a join-semilattice. Availability
  stamps combine by `max` at a tensor of inputs (synchronise: wait for the last input).
- **The action** `⊳ : T × D → T`, `t ⊳ d = t + d` — a duration translates a time point.
  Laws: `t ⊳ 0 = t`, `(t ⊳ d) ⊳ e = t ⊳ (d + e)`, and the distributivity
  `max(t, t') ⊳ d = max(t ⊳ d, t' ⊳ d)`, which is exactly the semiring law
  "`+` distributes over `max`" of `𝕋`. On the PRODUCT stamp space
  (time × dist, TODO_0285) the componentwise translation
  `(t, δ) ⊳ (T, D) = (t + T, δ + D)` satisfies all three laws per axis.
  A cross-axis coercion "dist counts as delay" (embedding `D` into the
  time axis) is ALSO algebraically lawful — `d ↦ d` is a monoid
  homomorphism, no action law refutes it. The refutation is semantic:
  under the coercion each hop's `D` enters the time axis while still
  riding the dist axis, so the time component reads `t + Σ(Tᵢ + Dᵢ)` —
  the availability time of nothing — and the two objectives the product
  keeps apart collapse (THY_0033 §3). Hence transport-takes-time is a
  rule (each axis's cost enters once, as data), never a grade coercion.

Every proof and every theorem below uses ONLY these laws. Consequently the calculus is
parametric: any (ordered commutative monoid `D`, join-semilattice `T`, monotone
distributive action `⊳`) triple instantiates it (§9); the tropical instance is the timed
one. Points vs translations is deliberate — stamps are absolute, delays relative; the
dimension analysis of RES_0135 §4 applies unchanged.

Positioning against Gaboardi et al. (ICFP 2016): in their matched-pair format our
delay effect and availability coeffect are ORTHOGONAL — the pair is the trivial
`ι(r,e) = r, κ(r,e) = e`, and their distributive law σ is identity at the grade level.
The substantive interaction in till is NOT σ but the action `⊳` inside the promotion
rule (§5), whose distributivity over `max` is the tropical semiring law — structure
their framework does not need and does not supply. We instantiate their format; the
timed content is ours.

## 3. Judgments and syntax

Formulas: ILL (`⊗, ⊸, 1, &, ⊕, !, ∃, ∀`) extended with stamped atoms `A@t` (`t ∈ T`;
an unstamped atom abbreviates `A@0`) and the graded monad `{S}@d` (`d ∈ D`; bare `{S}`
abbreviates `{S}@0`), where `S` ranges over the synchronous/positive fragment as in CLF.
In the engine the monad is one binary node `monad(grade, body)`, dual to
`bang(grade, formula)` (TODO_0265 D6).

Judgments, as in lax logic (Fairtlough–Mendler 1997; Pfenning–Davies 2001), with the lax
judgment graded:

- `Γ; Δ ⊢ A true` — `A` holds of the persistent context `Γ` and linear context `Δ`.
- `Γ; Δ ⊢ S lax@d` — `S` is ACHIEVABLE from `Γ; Δ` within delay bound `d` of the
  context's availability. `d` bounds the effect; it is relative to the activation of the
  consumed resources, not absolute (stamps make it absolute in §5).

## 4. Rules (the graded fragment; ILL rules unchanged)

```
Γ; Δ ⊢ S true                    Γ; Δ ⊢ S lax@d
───────────────  lax             ─────────────────  {}R
Γ; Δ ⊢ S lax@0                   Γ; Δ ⊢ {S}@d true

Γ; Δ, S ⊢ C lax@e                Γ; Δ ⊢ S lax@d    d ≤ d'
───────────────────────────  {}L ─────────────────────────  sub
Γ; Δ, {S}@d ⊢ C lax@(d + e)      Γ; Δ ⊢ S lax@d'
```

- `lax` is the unit: what is true now is achievable with zero delay.
- `{}L` is CLF's STICKY left rule with grade composition: eliminating `{S}@d` inside a
  lax goal adds `d` to the bill. It can only fire when the conclusion is lax — grading
  rides the existing modal discipline, adding nothing to its shape.
- `sub` is subeffecting: a bound may be weakened. It is what makes the grade a BOUND and
  the operational stamp its LEAST solution (Theorem 1).
- Erasing all grades (map every `d` to the unit) yields exactly the JUDGMENTAL lax
  fragment — Pfenning–Davies' `○I`/`○E` with `lax` conclusions, equivalently
  Benton–Bierman–de Paiva's `3R`/`3L`, which is CLF's discipline: the calculus is a
  conservative decoration. (Fairtlough–Mendler's own Gentzen system formulates `○L`
  differently; we follow the judgmental/CLF formulation throughout.)

Derived rules (proofs are two-line compositions of the above):

```
graded μ:      {{S}@d}@e ⊢ {S}@(d + e)         (by {}L twice, {}R once)
functoriality: S ⊢ S'  ⟹  {S}@d ⊢ {S'}@d
unit η:        S ⊢ {S}@0
```

`μ` says delays along a chain of monadic binds ADD — the critical-path reading of `⊗` in
`𝕋`. In CLF terms: `let {p₁} = e₁ in let {p₂} = e₂ in …` accumulates the sum of the
step grades — the timed trace of Observation 6 is exactly this chain with its per-step
grades made explicit.

**Implementation encoding (single-level).** The implemented sequent calculus
(`calculus/till/till.rules`) uses a single-level encoding: the judgment `S lax@d`
is represented as the formula `{S}@d` in the `true` judgment, and the four
primitive rules collapse to two. `monad_r` fuses `lax + sub + {}R` — any
`{S}@E` with `E ≥ 0` is provable from `S` in one step (the guard `E ≥ 0` IS the
fused subeffecting). `monad_l` is `{}L` read bottom-up: from conclusion grade
`F` and principal grade `E` it derives the premise grade `H := F ⊖ E` by the
grade algebra's PARTIAL residual (THY_0022): `⊖` is undefined when `F < E`, so
the side condition is not stated anywhere — the rule is inapplicable because
the illegal grade cannot be constructed, which is what guards the critical-path
lower bound. The encoding is conservative both ways: a two-level derivation maps
to a single-level one by fusing each `{}R` with the `lax`/`sub` steps above it,
and a single-level derivation unfolds by reading each `monad_r` as
`lax; sub; {}R` and each `monad_l` as `{}L`.

## 5. Stamps and the timed promotion rule

Stamps are the coeffect side. Three stamp laws, with DIFFERENT standings — only
one is a sequent rule (this scoping is deliberate and implemented; conflating
them would make `A ⊢ A@t` derivable, which the calculus rejects):

```
retiming:   A@t ⊢ A@t'          (t ≤ t')      — delaying availability is free
```

- **Retiming** is the one SEQUENT RULE (the `at_l` axiom in the implementation).
  It is the coeffect mirror of `sub`; it is why cohorts may be USED late but
  never early.
- **Ambient** `A ≡ A@0` is a CANONICALIZATION CONVENTION at the state boundary,
  not a sequent rule: unstamped atoms enter the timed context as stamp-0 and
  zero stamps are stripped when a residual state is read back (the settle
  bridge canonicalizes both sides). Inside the calculus `a ⊬ a@t` for every
  `t` — an unstamped hypothesis is NOT retimable, because admitting
  `A ⊢ A@0` as a rule would compose with retiming into exactly that
  derivation. Stamps are born at the boundary, moved only by retiming.
- **Monoidal** `(A ⊗ B)@t ≡ A@t ⊗ B@t`, `1@t ≡ 1` is a META-LEVEL law about
  the state REPRESENTATION (a stamped cohort of a tensor is the pair of
  stamped cohorts): compound-stamped formulas are not syntactically valid in
  the calculus — `@` attaches to atoms only. Its sequent shadow is derivable
  pointwise: `a@t, b@t ⊢ a@t' ⊗ b@t'` (t ≤ t') by tensor rules + retiming.
  The law is what makes `S@u` in `@fire` below well-defined. The rule that ties stamps to grades — the operational firing rule, stated
proof-theoretically — is a promotion rule in the SELL/THY_0013 style (a global condition
on the context, not a local left rule):

```
Γ; A₁, …, Aₙ ⊢ S lax@d        a = max(t₁, …, tₙ, 0)
──────────────────────────────────────────────────────  @fire (timed promotion)
Γ; A₁@t₁, …, Aₙ@tₙ ⊢ S@(a ⊳ d) lax@0
```

where `S@u` stamps every atom of the positive formula `S` with `u` (well-defined by the
monoidal law). Reading: the rule body promises `S` within `d` of its inputs; the inputs
synchronise at `a` (coeffect `⊕ = max`); the outputs exist from `a + d` (action `⊳`);
and the conclusion's lax grade RESETS to 0 — the effect has been fully internalised
into stamps. Two boundary cases fix the intuition:

- `n = 0`: `Γ; · ⊢ S lax@d ⟹ Γ; · ⊢ S@d lax@0` — "the delay grade is the stamp of
  the future".
- `d = 0`, all `tᵢ = 0`: ordinary untimed firing, stamps invisible.

Activation windows (`after E`: strengthen `a` to `max(a, E)`; `before E`: side condition
`a < E`) are scheduling annotations on this rule, not connectives — their metatheory is
THY_0019 §windows. Persistent hypotheses carry no stamps (TODO_0265 D15): `!A@t` is
rejected; the grade-product interaction of `ω` with time is future work (TODO_0157).

**Theorem (bridge soundness; the @fire oracle).** The implementation realises
`@fire` as an ORACLE rule (`monad_r2`, the settle bridge): for a goal
`Γ; Δ ⊢ {S}@T` it runs `settle(|Δ|, T)` — a chain of `@fire` instances — and
then proves `S` against the residual timed multiset by the pure sequent
calculus (retiming + tensor decomposition + identity). If the bridge succeeds,
`Γ; Δ ⊢ {S}@T` is derivable — each settle step is an `@fire` instance and the
residual match is an ordinary derivation, so the oracle only ever asserts
derivable sequents. The CONVERSE IS FALSE and must not be claimed: the backward
calculus is strictly stronger than settle-reachability — `monad_r` derives
`a ⊢ {a}@d` for every `d ≥ 0` with no forward step at all (subeffecting), so
derivability does not imply that settle produces the goal state. The bridge is
a sound but incomplete proof procedure; refutation by the bridge is
underivability VIA THE BRIDGE, and a claimed refutation of the sequent itself
additionally requires that no pure-backward derivation exists (in the
implemented prover both are searched, so `prove` failure does refute). Kernel
checking of a bridge step is structural only — the settle run is trusted and
reported as `unverified: 'modeSwitch'` (round-15 F1).

**The adequacy rests on residual partiality, not on rule-set completeness.**
The positive direction — each settle step *is* a derivable `@fire`/`monad_l`
instance — needs the delay bookkeeping to never fabricate a sequent. The
critical point is `{}L`'s residual `H := F ⊖ E`: a step that composed delays
into a NEGATIVE residual grade would not correspond to any `@fire` instance.
That non-negativity is not a side condition at all but a property of the
operation: the theory exposes no signed subtraction — `{}L`'s premise
`!qsub F E H` is the partial monoid residual as a derivability statement
(no proof for `F < E` ⇒ rule inapplicable), so the illegal step is
unconstructible by ANY rule, present or future (Grade Preservation,
THY_0022; historically this was an explicit `F >= E` guard over a signed
`effect.sub` — TODO_0272 M1 — which TODO_0273 deleted in favour of the
stronger intrinsic form, first as the algebra's partial `⊖`, then as the
in-logic theory premise). With non-negativity intrinsic, the
settle→derivability map is compositional: `settle`'s activation recurrence
`u = max(inputs) + d` is exactly the `@fire` conclusion (a = max, ⊳ = +), and
every step's residual grade is defined-hence-valid by construction, so the
chain of `@fire` instances the bridge replays is a genuine derivation
regardless of which OTHER rules exist. This is what makes "bridge success ⇒
derivable" a theorem about `monad_l`/`@fire` alone rather than about the
completeness of the whole rule set — the prerequisite the paper write-up of
this adequacy direction needs before mechanisation (§8).

## 6. Operational semantics, in one paragraph

A till program is a set of rules `In ⊸ {Out}@d`; a state is a timed multiset (a
multiset of stamped atoms; equal-stamp copies merge into cohort multiplicity —
TODO_0265 D4/D5). A match `m` selects cohorts for the pattern atoms; its activation
`a(m)` is the `max` of the selected stamps and after-bounds; firing consumes the inputs
at `a(m)` and produces each output stamped `a(m) ⊳ d`; the scheduler fires enabled
matches in nondecreasing `a(m)`; `settle(state, T)` does so while `a(m) ≤ T`. Each
firing is literally one `@fire` instance, and the whole execution is one CLF monadic
let-chain (§8). The matching order, tie-breaking, chooser, and the composability law
`settle(settle(S,T₁),T₂) = settle(S,T₂)` are THY_0019's subject. The reference
implementation of exactly this section is `tools/till-oracle.mjs`.

## 7. Metatheorems

**Theorem 1 (ASAP = principal stamp; v1 exact form).** Let `Δ` be a timed
multiset, `T` a horizon, and `R = settle(Δ, T)` the residual of an
activation-ordered conflict-free execution. In the implemented v1 judgment
(ground grades, exact stamped-atom accounting):

1. *(Soundness)* `Γ; Δ ⊢ {⊗R}@T` is derivable — the execution IS a
   derivation.
2. *(Exactness of production claims)* for a token `b@u ∈ R` produced by the
   execution (`b` not in `Δ`), the claim `Γ; Δ ⊢ {b@u'}@T'` (with `T'` past
   the producing activation) is derivable **iff** `u' = u`. In particular the
   operational stamp is the least — and only — derivable production stamp.
3. *(Where weakening lives)* stamp weakening is hypothesis-side only:
   `b@t ⊢ b@t'` is derivable iff `t ≤ t'` (retiming, `at_l`); grade
   weakening is monad-side only: `S ⊢ {S}@E` for every `E ≥ 0` (`monad_r`'s
   fused subeffecting). Neither lifts a production claim's stamp: the v1
   calculus deliberately omits stamped-atom subeffecting (availability
   monotonicity is Stage 2 / THY-B).

*Proof.* (1) Induction on the length of the firing chain. Empty chain:
`R = Δ`, and `{⊗R}@T` follows by `monad_r` from `⊗R`, which follows from `Δ`
by `tensor_r` splits, retiming instances (`at_l`, each with `t ≤ t'`
trivially reflexive), and `id`. Inductive step: let `m` be the first firing,
with activation `a(m) = max(input stamps, after-bounds) ≤ T` and delay `d`.
By the timed promotion rule (§5), `m` is one `@fire` instance: a derivable
step consuming its inputs at `a(m)` and producing outputs stamped
`a(m) ⊳ d`. Composing it (graded `μ`) with the derivation of the remaining
chain — which exists by the induction hypothesis applied to the post-firing
state — requires exactly one `{}L` residual per composition, and each is
DEFINED: the activation recurrence gives `a(m) ≤ T` at every step
(activation order), so the budget always covers the spent delay. Since `⊖`
is the only way any rule constructs a decreasing grade and it is
defined-hence-valid here (THY_0022 Grade Preservation), the replayed chain
is a genuine derivation. No appeal to which other rules exist is needed —
this is the §5 compositionality argument.

(2, ⇐) is an instance of (1). (2, ⇒) Induction on cut-free derivations of
`Γ; Δ ⊢ {b@u'}@T'`. Since `b` does not occur in `Δ`, no derivation can end
in a pure-backward decomposition reaching `id` on `b@u'`: the backward
fragment has no rule that introduces a program atom (`at_l` requires a
stamped `b` hypothesis; the ILL rules only rearrange). So every derivation
routes through the bridge (`monad_r2`), whose settle chain is the
operational execution itself and whose residual match (`rightFocus`) is
EXACT on stamps: it matches `b@u' ` against `b@u ∈ R` only when `u' = u`.
The rule-by-rule check that no grade-touching step can lower a stamp along
the way: `monad_l` only spends budget (its residual is defined only when the
budget covers the principal's delay — a claimed stamp below the max-plus
critical path makes some `⊖` along the derivation undefined, hence the
derivation does not exist); `at_l` only raises hypothesis stamps
(`T1 ≤ T2`); `monad_r` touches the monad grade, never an atom stamp; the
bang peels and ILL rules are grade-neutral. (3) `at_l` and `monad_r` direct;
the omission of stamped-claim weakening is by inspection of the rule set —
no rule's conclusion has an atom stamp not already present in a premise or
hypothesis. ∎

Stamps are max-plus polynomial evaluations; the scheduler evaluates them, the
logic pins them exactly. **Mechanized witnesses**: curated —
`tests/till-adequacy.test.js` (soundness on executable-spec gates,
refutations, Thm 3/5 as (under)derivability); generative —
`tools/fuzz-till.js` §3 fuzzes all three clauses on random one-rule programs
with rational stamps/delays through the real prover: `b@u` derivable,
`b@(u/2)` and `b@(u+1)` underivable as production claims, `b@u ⊢ b@(u+1)`
derivable and its converse refuted. (The `b@(u+1)` refutation is not a
weakness but the v1 exactness discipline — an earlier sketch of this theorem
wrongly claimed production stamps admit weakening; the fuzzer found the
counterexample.)

**Definition (conflict-freedom).** An execution is conflict-free iff no two
enabled matches share a consumed cohort — equivalently, the consumed-resource
relation of enabled events assigns each cohort to at most one consumer. Read
arcs are exempt (they reserve without consuming — Theorem 4); operationally
this is the timed-event-graph subclass: every linear resource has at most one
consumer and at most one producer rule (Baccelli et al. 1992).

**Theorem 2 (timed confluence).** If the execution is conflict-free, the final
timed multiset of `settle(S, T)` is independent of the firing order among
activation-compatible orders. *Sketch.* Under conflict-freedom each token has a unique producing
event and each event a unique set of consumers, so the event DAG is unique; a token's
stamp is the max-plus path weight of its derivation DAG (Theorem 1), a function of the
DAG only. Firing orders are linearisations of the DAG; the multiset of (atom, stamp)
leaves is order-invariant. This is CLF's concurrent equality (permutation of independent
lets — Watkins et al. 2002) with the stamps as a permutation INVARIANT; the boundary of
the theorem is exactly where conflicts (and the chooser, THY_0019 §PRF) enter. ∎(sketch)

**Theorem 3 (Fission/Fusion).** Let `fused = In ⊸ {Out}@d` and let `fissioned` be the
pair `start = In ⊸ {J}@0`, `end = J ⊸ {Out}@d` for a fresh atom `J` occurring in no
other rule. Then fused and fissioned programs are observationally equivalent on J-free
observables, with identical stamps. *Sketch.* `start;end` composes by the graded `μ`:
`0 + d = d`; the intermediate `J@a` is produced and consumed at the same activation `a`
and is invisible to other rules by freshness. Fusion is cut elimination on `J` (the cut
composes the two lets into one; the `@d` grade is what remains of the cut — the exact
kinship of THY_0015's grade-0 composition, with grade `0+d` instead of erasure).
Per-output delays (CPN/TAPN-style arc delays) follow by fissioning with several `end`
rules. ∎(sketch)

**Theorem 4 (read-arc lemma).** In a conflict-free, activation-ordered execution,
re-emitting a `read` token with its ORIGINAL stamp is observationally equivalent to
re-emitting it stamped at the reading event's activation `a`. *Sketch.* The stamps
differ only for a later consumer whose OTHER inputs all have stamps `< a`; such a
consumer was enabled with activation `< a` before the read fired, so activation order
would have fired it first — contradiction. (Note the proof is a property of the
activation-ordered SCHEDULER — THY_0019's determinism discipline — not of the
sequent calculus alone; the lemma transfers to the logic through Theorem 1.) In conflicting programs the two conventions
can be distinguished by the chooser; till fixes ORIGINAL stamp, which also makes the
re-emission bit-identical (a state no-op — the engine's preserved/reserved path,
TODO_0265 E7.2/E3). ∎(sketch)

**Theorem 5 (in-flight atomicity).** In the fused form, no rule can consume OR read any
effect of a running job: for a firing at activation `a` with delay `d`, the inputs are
consumed at `a` and every output carries stamp `a + d`, so any match involving an output
— consuming or reading, since read stamps join the activation max — has activation
`≥ a + d`. The open interval `(a, a+d)` admits no interaction with the job.
*Corollary (interruption requires reification).* An interruptible process MUST be
fissioned: the mid-flight resource (`constructing(farm)`) is the honest model of a job
the world can touch. Observability never requires fission (Observation 6 makes the job
visible as a trace node); only interaction does. ∎

**Observation 6 (trace ≅ term).** The flat step log `p` (records `(rule, θ, a, d)`
in firing order) and the CLF monadic proof term `t` (the let-chain; each step one
`copy → loli_l → monad_l` node, as built by the engine's `guidedTerm`) are two
presentations of one object: `reify(p) = t`, `flatten(t) = p`, `p` is the canonical
(activation-ordered, policy-fixed) linearisation of `t`'s concurrency partial order, and
`t` modulo concurrent equality is the class of all linearisations — the stamps make the
partial order explicit (Theorem 2). This is stated as an OBSERVATION, not a
theorem: the identification itself is CLF's design (the guided term IS the proof
term); what is new here is only the per-node stamp annotation, and the
canonicality claim is inherited wholesale from THY_0019's determinism theorem —
it carries that document's proof obligations, not fresh ones.

*Corollary (Merkle accumulator; engineering).* Reassociating `t` as an event
snoc-list (old events deep) lets a running system prune the settled past into a
Merkle accumulator `H₀ = nil, Hₖ = hash(Hₖ₋₁, evₖ)`: the engine state =
in-flight nodes + `H_settled`, `O(1)` history storage that still
cryptographically commits to the full trace (audit/ZK replay verification
without archival storage; optional archive mode re-materialises). What pruning
preserves is exactly the COMMITMENT — a verifier can check a claimed replay
against `H_settled` because content addressing makes a subtree its hash — and
nothing else: pruned events are gone unless archived. An implementation
corollary (TODO_0265 Phase 7), not a logical result.

## 8. Cut elimination (sketch — discharged in THY_0023)

**Status (2026-08-21).** The sketch below is now a THEOREM: THY_0023 proves
cut admissibility in full (three cuts — linear, lax, persistent — Theorem 8
there), via the judgmental presentation and a cut-free-preserving
equivalence with the implemented single-level encoding (THY_0023 Theorem 4).
The sketch is kept as the readable overview; the case-by-case proof, the
measure (where the count fence ℕ is load-bearing and dense delays never
enter), and the vacuity of mismatched counted-bang cases by theory-premise
partiality are in THY_0023 §§2–6.

The graded cut for the lax judgment:

```
Γ; Δ ⊢ S lax@d      Γ; Δ', S ⊢ C lax@e
───────────────────────────────────────  cut_lax (admissible)
Γ; Δ, Δ' ⊢ C lax@(d + e)
```

*Argument.* (i) The principal case `{}R` vs `{}L` reduces a `true`-cut on `{S}@d` to
exactly `cut_lax` with grades composing as `d + e` — the same composition `{}L` already
performs, so no new grade arithmetic appears. (ii) All commutative cases permute cuts
past rules that either ignore grades (ILL rules) or adjust them monotonically (`sub`);
the needed facts are only that `+` is associative, commutative, monotone in `≤`, and has
unit 0 — the ordered-monoid laws of §2. (iii) `sub` above a cut premise absorbs into
`sub` below the conclusion (`d ≤ d' ⟹ d + e ≤ d' + e`). (iv) Erasing grades maps the
system onto PLL/CLF's lax fragment, whose cut elimination is standard
(Fairtlough–Mendler 1997; Watkins et al. 2002); by (i)–(iii) every reduction step of the
erased procedure lifts to the graded system with the stated grade bookkeeping, and the
resulting cut-free derivation's grade is ≤ the original (cut elimination never worsens
the bound). (v) Retiming (`at_l`, the zero-premise stamp axiom): a cut whose cut
formula `A@t'` is the conclusion of `at_l` from `A@t` (t ≤ t') reduces by
re-deriving — substitute the left subderivation of `A@t` and re-apply `at_l`;
transitivity of `≤` is the only fact used, and no grade arithmetic is
introduced. Two stacked retimings compose into one (t ≤ t' ≤ t''), so the
reduction terminates. (vi) The bridge oracle (`monad_r2` / `@fire`-as-oracle)
is EXCLUDED from the cut-elimination claim: it is an admissible extra-logical
rule whose soundness is the §5 bridge-soundness theorem — cut elimination is a
property of the pure syntactic calculus (id through `monad_r`, `at_l`, `copy`
and the ILL rules). (vii) In the single-level implementation encoding (§4), the
`sub` cases of (iii) appear as `monad_r`'s slack `E ≥ 0`; the same monotonicity
fact (`d ≤ d' ⟹ d + e ≤ d' + e`) discharges them. A full syntactic proof is
future work for the paper write-up; nothing in it is expected to exceed routine
verification of (i)–(vii). ∎(sketch)

Stamps: `@fire` behaves as a promotion rule; its cut cases follow the SELL pattern
(THY_0013 §2) with the side condition `a = max(tᵢ)` re-established from the premise
stamps — the distributivity law of §2 is what makes the recomputed max agree after
substitution.

**Mechanisation status (honest boundary).** The full ON-PAPER proof is
THY_0023 (all of (i)–(vii) checked by hand; notably case (iv)'s erasure lift
is no longer needed — the graded system is proved directly, and the erased
proof re-emerges as its shadow). None of it is MACHINE-checked: mechanisation
is deliberately deferred (TODO_0270; if ever needed it becomes its own todo,
and the mechanised rules must carry the theory-premise form `<- !qsub F E H`).
Case (vi) remains a *scoping* statement, not a proof: the `@fire`/`monad_r2`
oracle is excluded from the calculus whose cut is eliminated (it is
extra-logical; its soundness is §5, and §5 rests on the residual's intrinsic
partiality — THY_0022 — rather than on rule-set completeness).

## 9. Instances

One binary node `monad(grade, body)`, many effect algebras — the instances table this
document's calculus is parametric over:

| instance | grade algebra `D` | reading | where |
|---|---|---|---|
| ILL `{A}` | trivial (unit only) | CLF boundary, no measurement | today's calc |
| `{A}_a` | stratum preorder, join | which rule stratum may run | THY_0013 |
| `{A}_{q·a}` | staging × stratum | compile-time vs runtime phases | THY_0015 |
| `{S}@d` | `(ℚ≥0, +, 0, ≤)` + stamp action | duration / schedule | this document |
| `○A = {A}@1` | `(ℕ, +, 0)` | unit-tick temporal layer (μMALL + ○) | TODO_0203 bridge |
| `{A}_w` | `([0,1], ×, 1)` expectation | probability mass (analysis) | deferred (TODO_0265) |

The `○ = {}@1` row records that flat delay suffices for the FRP/temporal bridge — no
μ/ν machinery is required at this layer. With `d > 0` the monad is a GUARDEDNESS
witness: every recursion through `{·}@d` advances the schedule (Nakano's `•` modality,
LICS 2000 — later written `▷` by Appel et al./Birkedal et al.; the productivity lint of
THY_0019 §termination is this observation turned into a check).

## 10. Related work and the novelty ledger

Audited 2026-08-18 (TODO_0265 E7.4 + literature verification pass):

| ingredient | nearest neighbour | delta |
|---|---|---|
| lax modality, sequent rules, cut elim | Fairtlough–Mendler 1997; Pfenning–Davies 2001; CLF | ungraded — we add the grade and keep their shape |
| graded monads (semantics) | Katsumata POPL 2014; Fujii–Katsumata–Melliès FoSSaCS 2016 | categorical, no sequent calculus / lax connective |
| graded NECESSITY with sequent proof theory | BLL 1992; coeffect calculi; Moon–Eades–Orchard ESOP 2021; Hanukaev–Eades CSL 2025 | all grade the exponential side (`!_r`) — cut elimination exists there, never for a graded monad |
| graded POSSIBILITY (the nearest neighbour) | Granule (Orchard–Liepelt–Eades ICFP 2019): graded `◇_r` monad for I/O effects | bidirectional type system only — NO sequent calculus, NO cut-elimination theorem; the proof theory of `{S}@d` is precisely the missing piece (novelty audit 2026-08-18, 30+ papers, 3 adversarial searches, no counterexample) |
| effect–coeffect interaction | Gaboardi et al. ICFP 2016 | our grades form their TRIVIAL matched pair (§2) — the timed content is the `⊳` action in the promotion rule, which their framework does not supply |
| per-fact timestamps in MSR | Kanovich et al. FORMATS 2016 | global `Time@T` fact + Tick rule; no max-plus activation, no in-flight representation; their "progressing" condition ≈ our Zeno guard |
| `@+d` output delays, enabling = max | CPN Tools (Jensen et al. STTT 2007) | identical operational surface; no proof theory, no graded-monad reading |
| time in linear type systems | Das–Hoffmann–Pfenning ICFP 2018 (temporal session types; + Rast LMCS 2022) | discrete unit-tick ◯ annotations on CHANNEL types for work/parallel-complexity analysis — linear types + time, but no graded possibility/lax modality over resource multisets, no ℚ-graded delay, no tropical activation |
| (max,+) systems theory | Baccelli et al. 1992 | the algebra and the cycle-time/eigenvalue results we import for E6; not connected to logic |
| in-flight = proof-term node | event structures (Nielsen–Plotkin–Winskel 1981): state = frontier of a configuration | the identification of in-flight jobs with monadic LET-NODES, and atomicity-as-theorem, are ours |

Novel here (the `unique_contribution` claims): the delay-graded lax monad with sequent
rules and cut-elim sketch; max-plus activation as a promotion side condition; process
identity at the trace level with Theorems 3–5; the trace≅term/Merkle-GC packaging
(Observation 6 + its corollary — engineering-level, presented as such).

## 11. References

See frontmatter; plus, for the operational side and all scheduling metatheory,
THY_0019. The executable ground truth for §6–7 is `tools/till-oracle.mjs` with
`tests/engine/till-oracle.test.js` (the 10/10/10 oracle, composability, atomicity,
read-arc and productivity scenarios are each a test there).

Implementation (TODO_0265 Phase 6b): §4's rules are `calculus/till/till.rules`
(monad_l = {}L, monad_r = lax·sub·{}R fused; retiming = the at_l axiom), the
§5 `@fire` rule is realised by the settle bridge (`lib/prover/bridge.js`
timedSwitch — succedent grade = observation horizon), and Theorems 3/5 are
witnessed as (under)derivability in `tests/till-adequacy.test.js`; the graded
provability grid is `tests/till-prover.test.js`. See
`doc/documentation/till-sequent-calculus.md`.
