---
title: "The Probability-Graded Existential: Superposition, Collapse, and Observation in Graded ILL"
created: 2026-08-28
modified: 2026-08-28
summary: "One new primitive — a weight-graded existential ∃_ρ x:s. A whose right rule multiplies the derivation grade by ρ(c) for the chosen witness constructor c — turns graded ILL into a probabilistic generation calculus. Grades live in the UNNORMALIZED measure semiring (ℚ≥0,·,1); normalization is a meta-operation, so priors, biases, and evidence are all just weights and conditioning is multiplication (knowledge-monotone by construction). woplus (THY_0021) becomes the derived Boolean instance. Datasort refinements (THY_0020) are the events one conditions on; conditioning is a derived rule via inside-mass renormalization. Observation is intralogical: collapse IS the principal cut ∃_ρ-R vs ∃-L — sampling is a cut-reduction step, performed by the settle PRF; persistent knowledge conditions a superposition without collapsing it, linear consumption forces actuality. Four theorem statements (adequacy, a.s. groundness ⟺ subcriticality, importance-weighted sampler unbiasedness, compositional-conditioning boundary) give the sound-and-complete story; the WFC decimation loop for map generation is the operational reading."
tags: [linear-logic, proof-theory, graded-types, till, lax-monad, existential, exists, probabilistic, forward-chaining, cut-elimination, refinement-sorts, wfc, procedural-generation, superposition]
category: "Probabilistic Generation"
unique_contribution: "Four claims not found in the literature (novelty audit 2026-08-28): (1) an existential whose RIGHT RULE carries a semiring weight on the witness CHOICE — ∃ = semiring sum over witnesses is established denotationally (Droste–Gastin weighted MSO; Grädel–Tannen FO semiring provenance) but in no prior system is it a sequent rule that grades the derivation; graded type theories (QTT, Granule) grade binder USAGE, not witness choice; Das–Wang–Hoffmann's probabilistic session types weight a flat finite label set, not a quantifier over a (possibly recursive) constructor sort. (2) Sampling as cut elimination in ILL: collapse of a superposed existential IS the principal cut ∃_ρ-R/∃-L, so the operational PRF draw is a cut-reduction step — Yoshimizu et al. reduce quantum measurement to additive cuts in proof nets, but without grades and without an existential. (3) The observation boundary mapped onto the Term/Resource/Proposition discipline: persistent (knowledge) derivations condition a superposition monotonically WITHOUT collapse; linear (possession) consumption forces collapse — a resource-sensitive Copenhagen reading with a proof-theoretic justification. (4) The WFC/decimation loop derived as a theorem package: any sound pruning + importance weighting yields an UNBIASED sampler of the conditioned measure (greedy WFC bias becomes a variance statement), with compositional conditioning characterized exactly by decomposable dependency (= where belief propagation is exact)."
references:
  - "TODO_0292 — probabilistic collapse calculus (design + phases; this document is its theory core; implementation: calculus `will` extending `gill`)"
  - "Faggian, Galal & Paquet (2022). Curry and Howard Meet Borel. LICS (closest near-miss: proof normalization ≈ probabilistic computation — non-linear ND, normalized counting modality C^q, not a witness-graded ∃; cite and contrast)."
  - "Crubillé (2026). De Finetti's Theorem in Integrable Cones. LICS (exchangeability ↔ free exponential !; semantic only)."
  - "Bacci & Møgelberg (2026). Higher-Order Quantitative Logic for Probability. LICS (quantitative judgments/distances; no graded quantifier, no sampling-as-cut)."
  - "THY_0021 — Weighted Additive Disjunction (woplus; now the derived Boolean instance of ∃_ρ)"
  - "THY_0018 — The Delay-Graded Lax Monad (tropical grading; ∃_ρ adds the measure grading, product of semirings)"
  - "THY_0019 — Timed Matching and the Settle Scheduler (the PRF sampler; order-invariance ancestor)"
  - "THY_0020 — Refinement Sorts (datasorts; here: the events one conditions on)"
  - "THY_0024 — Graded Labelled States (wave table pattern; values-not-ids PRF invariant)"
  - "TODO_0283 — the {A}_w paper (this document extends its planned scope)"
  - "RES_0137 — general graded monad/comonad/mode calculus (hq; the measure semiring is a new instance row: within-derivation merge = ·, across-derivation aggregation = sum/sample — NOT an order prune)"
  - "TODO_0284 — pluggable graded-modal engine (hq; implementation host via its new laboratory calculus `gill` — graded ILL, algebras as data; the weight grade is the third co-driving instance, aggregation policy = (⊕, realization), task P1b/P3b)"
  - "Droste & Gastin (2007). Weighted Automata and Weighted Logics. TCS (∃ = semiring sum, denotational)."
  - "Grädel & Tannen (2017/2024). Semiring Provenance for First-Order Logic. arXiv:1712.01980, 2412.07986."
  - "Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS."
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS (usage-graded binders — orthogonal)."
  - "Das, Wang & Hoffmann (2023). Probabilistic Session Types. POPL (weighted flat label choice — closest typed system)."
  - "Lucas & Mio (2021). Cut Elimination for Modal Riesz Spaces. LMCS (only prior cut-elim in a probabilistic logic)."
  - "Yoshimizu, Hasuo, Faggian & Dal Lago (2014). Measurement as additive cut in quantum MALL proof nets. ESOP."
  - "Danos & Ehrhard (2011). Probabilistic Coherence Spaces. Inf. & Comp. (denotational LL model)."
  - "Sato (1995). A Statistical Learning Method for Logic Programs (distribution semantics; PRISM switches)."
  - "Staton (2017). Commutative Semantics for Probabilistic Programming. ESOP (normalization as meta-operation)."
  - "Murray, Lundén, Kudlicka, Broman & Schön (2018). Delayed Sampling and Automatic Rao-Blackwellization. AISTATS."
  - "Chi & Geman (1998). Estimation of Probabilistic Context-Free Grammars (subcriticality/consistency)."
  - "Freeman & Pfenning (1991). Refinement Types for ML (datasorts = regular tree sorts)."
  - "Gumin (2016/2022). WaveFunctionCollapse; MarkovJunior. github.com/mxgmn."
  - "Karth & Smith (2017). WaveFunctionCollapse is Constraint Solving in the Wild. FDG."
  - "Braunstein, Mézard & Zecchina (2005). Survey Propagation (decimation loop structure)."
---

# The Probability-Graded Existential

**Status.** Design + theorem statements with proof directions. Nothing here is
machine-checked or implemented; TODO_0292 carries the operational plan (P0–P3)
and §8 lists what a paper must discharge. One remaining novelty-audit lookup is
flagged in §7.

## 1. The gap

TODO_0292 asks for probabilistic generation: unbound existentials over a sort
are *superpositions* over its constructors; execution collapses them one at a
time (WFC-style decimation) until the state is ground. Two candidate foundations
were on the table — weighted `woplus` (THY_0021) and refinement-sort domains
(THY_0020) — and both are wrong *as foundations*:

- `woplus` alone weights *branches*, not *terms*; it has no story for domains,
  propagation, or conditioning. Generation needs mass on witnesses.
- Datasorts alone are a CSP — no measure, no sampling theorems; that
  formalization of WFC already exists (Karth & Smith).

The clean factorization puts probability at exactly one proof-theoretic point:
**the choice of a witness**.

## 2. The connective

Let `s` be a sort with constructors `c₁ … cₙ` and let `ρ : s → ℚ≥0` assign each
constructor a weight (the *prior*). The judgment carries a grade `⟨w⟩` from the
commutative semiring `(ℚ≥0, +, ·, 0, 1)` — the **unnormalized measure
semiring** — orthogonal to THY_0018's tropical delay grade (the judgment is
graded over the product of the two semirings; the weighted cut of THY_0021 §7
extends unchanged: delays add, weights multiply).

```
  Δ ⊢ A[c/x] ⟨w⟩        c a constructor of s
  ------------------------------------------ ∃_ρ-R(c)
  Δ ⊢ ∃_ρ x:s. A ⟨w · ρ(c)⟩

  Δ, A[a/x] ⊢ C ⟨w⟩     a fresh (eigenvariable)
  --------------------------------------------- ∃-L
  Δ, ∃_ρ x:s. A ⊢ C ⟨w⟩
```

The right rule is a PCFG production as a sequent rule: each derivation of
`∃_ρ x:s. A` chooses a witness and pays its mass. The left rule is the standard
existential left rule, weight-neutral — the consumer does not see the prior
(exactly as `woplus` has no left rule in THY_0021: weights are producer-side).

**woplus is derived.** `A +[q] B ≅ ∃_ρ x:bool. ((x = tt) ⊸ A) & ((x = ff) ⊸ B)`
with `ρ(tt) = q, ρ(ff) = 1−q` — THY_0021's two weighted right rules are the two
instances of ∃_ρ-R. This inverts THY_0021's architecture: the graded existential
is the primitive, weighted internal choice its Boolean shadow. All THY_0021
theorems (mass conservation, forest ≅ chain unfolding, PRF unbiasedness) are
inherited by the derived form and generalized by T1/T3 below.

**Normalization is meta, not logical.** Grades are unnormalized weights;
"probability" appears only in the metatheory as a mass ratio
`P(outcome) = mass(outcome) / mass(⊤otal)` (Staton's normalization-as-a-
meta-operation, in the discrete setting where no measure theory is needed).
This is the move that makes conditioning trivial: a prior is a weight, evidence
is a weight, conditioning is multiplication. Keeping normalized `[0,1]` inside
the logic breaks compositionality — likelihoods are not probabilities.
(THY_0021's `[0,1]` weight fence survives as the special case where the program
declares an already-normalized prior; the fence is per-sort advisory, not part
of the logic.)

## 3. Recursive sorts: the wave is a guarded fixpoint

For a recursive sort (`i, o : bin → bin`, `e : bin`) the superposition is not a
finite sum but a stochastic grammar — `∃_ρ x:bin` unfolds as the guarded
fixpoint `Wave(bin) = e +[ρe] (i Wave(bin) + o Wave(bin))`. Collapse is *lazy*:
one application of ∃_ρ-R grounds one head constructor and re-suspends the wave
at each recursive argument position. A ground term of arbitrary size
materializes incrementally (ancestral sampling from a branching process).

Termination is probabilistic and statically checkable: the process is
almost-surely finite iff subcritical, `Σ_c ρ̂(c) · arity(c) ≤ 1` (with ρ̂ the
normalized prior; Chi–Geman consistency) — see T2. This is the productivity
condition for generation, the exact sibling of till's Zeno/productivity lint.

## 4. Conditioning: datasorts are the events

The measure structure (∃_ρ) and the conditioning structure are two halves of
one probability theory:

- A **domain** for a superposed variable is a datasort refinement `S ⊑ s`
  (Freeman–Pfenning): for finite sorts a constructor subset, for recursive
  sorts a regular tree language ("at least 3 bits", "even"). Propagation =
  datasort intersection. This is THY_0020's machinery, not a parallel system.
- **Conditioning ∃_ρ on S is a derived rule**: cut against a sort-membership
  derivation, with weights renormalized by *inside mass* — for recursive sorts,
  the solution of the algebraic fixpoint system for `mass(S)` (the PCFG inside
  computation). Head-constructor marginals fall out of the same system.
- **Evidence under uncertainty**: persistent facts `!bias X c W` (`W ∈ ℚ≥0`),
  derived by backward rules guarded on state (CP-logic style), multiply into
  the grade: posterior ∝ prior · Π bias. Hard exclusion is `bias 0`.
  Monotonicity is free: persistent facts are never retracted and `(ℚ≥0, ·, 1)`
  is a commutative monoid — refinement under uncertainty is knowledge-monotone
  by construction, matching the persistent fragment's monotonicity discipline.

## 5. Observation: collapse is a principal cut

When does a superposition collapse? The intralogical answer:

**Collapse IS the principal cut ∃_ρ-R vs ∃-L.** A suspended (un-expanded)
∃_ρ-R is the wave — a producer that has not yet committed a witness. An ∃-L on
the consumer side is a demand for constructor structure. The cut-elimination
step that reduces this principal pair is exactly the moment a witness must be
chosen — operationally, the settle PRF draw (THY_0019) *is* this reduction
step. Sampling is cut elimination.

Consequences:

- **The observer is any linear consumer.** No new machinery: a rule whose
  antecedent pattern-matches the constructor structure of a superposed resource
  forces the cut, hence the collapse. WFC's "observe" phase becomes precise.
- **Knowledge does not collapse; possession does.** The Term/Resource/
  Proposition discipline maps onto the measurement boundary: *persistent*
  derivations about a superposed variable (marginals, biases, sort membership)
  condition the wave monotonically without forcing a witness — you can KNOW
  about a distribution freely; you cannot POSSESS a superposition — consuming
  it linearly forces actuality. Measurement is resource-sensitivity.
- **The monad is the phase boundary.** Superpositions live inside `{A}_w`
  (THY_0021's graded lax judgment); pure/backward reasoning manipulates them
  symbolically, forward/linear execution collapses them at bind — the same
  backward/forward boundary as bridge.js, now read as pure-vs-measurement.
- **The scheduler is policy only.** Which principal cut to reduce first
  (min-entropy = the WFC observe policy) is extra-logical, like till's chooser.
  T4 delimits when the resulting distribution is order-independent — the
  probabilistic analogue of THY_0019's horizon-splitting invariance.
- **Laziness is variance reduction.** Deferring collapse as long as possible is
  delayed sampling / automatic Rao-Blackwellization (Murray et al.): symbolic
  conditioning strictly reduces sampler variance. The lazy fixpoint reading of
  §3 is not an implementation trick; it is the statistically optimal policy.

## 6. Theorem statements

The reference semantics is Sato's distribution semantics lifted to derivation
forests: a program plus priors *denotes* a (sub)measure over ground quiescent
states (each complete derivation carries the product of its ∃_ρ-R weights; a
state's mass is the sum over derivations reaching it — the semiring-provenance
reading of ∃ as Σ, here obtained proof-theoretically).

- **T1 (Adequacy / completeness).** Exhaustive execution (`settleExplore` over
  the collapse tree) enumerates the derivation forest and computes the denoted
  measure exactly: every positive-mass normal form is reached, and leaf masses
  sum to total mass. Direction: extends THY_0021 §4 mass conservation from
  binary branch choice to witness choice; recursion via monotone convergence of
  the fixpoint masses.
- **T2 (Almost-sure groundness).** The decimation loop terminates with a fully
  ground state with probability 1 iff every recursive sort's normalized prior
  is subcritical/critical (`Σ ρ̂(c)·arity(c) ≤ 1`). Direction: reduction to
  extinction of multitype branching processes (Chi–Geman). Yields a load-time
  lint.
- **T3 (Sampler soundness).** The decimation loop with ANY sound pruning (never
  deletes a positive-mass witness) and importance weighting — track proposal
  weight vs. true weight along the path; the PRF machinery already computes
  both — is an unbiased sampler/estimator of the exact conditioned measure.
  Exact marginals are the zero-variance case; greedy-with-restarts (classic
  WFC) is the 0th-order approximation, so WFC's greedy bias becomes a variance
  statement, not a soundness caveat. Direction: standard importance-sampling
  identity over the forest measure; extends THY_0021 §6 unbiasedness.
- **T4 (Compositional conditioning — the hard one).** Weighted cut composes
  grades (delays add, weights multiply); conditioning commutes with cut exactly
  when the dependency structure between superposed variables is decomposable
  (tree-structured) — precisely the regime where belief propagation is exact.
  Direction: factor-graph reading of the shared-variable structure of the
  derivation forest; the failure mode (loopy double-counting) is the honest
  boundary of the theory and must be stated, not hidden.

## 7. Novelty audit (2026-08-28)

Established, to cite: ∃ = semiring sum denotationally (Droste–Gastin weighted
MSO `[[∃x.φ]] = ⊕ᵢ [[φ]][x↦i]`; Grädel–Tannen FO semiring provenance
`π[[∃x ψ]] = Σ_a π[[ψ(a)]]`; Green et al. via projection). Usage-graded binders
(Atkey QTT; Moon–Eades–Orchard; Granule) — same shape, different content:
usage, not choice. Probabilistic finite label choice in session types
(Das–Wang–Hoffmann POPL 2023) — genuine weight on choice, flat finite labels
only. Cut elimination in a probabilistic logic (Lucas–Mio hypersequents for
Riesz modal logic) — probability in the ◇ semantics, not a graded quantifier.
Measurement as principal (additive) cut in quantum MALL proof nets (Yoshimizu
et al. ESOP 2014) — no grades, no existential. Denotational LL probability
(Danos–Ehrhard PCoh). Delayed sampling as runtime mechanism (Murray et al.).

Apparently novel: the graded-witness-choice ∃-R in an ILL sequent calculus;
sampling as cut reduction in ILL; the knowledge/possession observation boundary
(§5); the T3/T4 package deriving WFC as theorems.

Markov-categories check RESOLVED (2026-08-28, dedicated sweep): the categorical
probability literature (Fritz; Cho–Jacobs; Stein–Staton exact conditioning;
Perrone; Crubillé's De Finetti ↔ free-! at LICS 2026) is purely semantic — no
internal sequent calculus, no quantifier rules, no sampling-as-normalization.
The closest near-miss overall, to cite and contrast explicitly: Faggian–Galal–
Paquet, "Curry and Howard Meet Borel" (LICS 2022) — proof normalization does
correspond to probabilistic computation there, but in a NON-linear natural
deduction whose counting quantifier `C^q` is a normalized-[0,1] modality over
random events, not a witness-choice existential; the probability is a meta-level
truth bound, not a grade multiplied at ∃-R, and there is no principal-cut
sampling. Graded-LL lines (Graded DiLL 2023; mixed linear+graded CSL 2025;
Granule) grade `!`, never ∃; model-theoretic semiring quantifiers count
witnesses in a structure with no proof theory. Novelty claims (a) graded
witness choice as a sequent rule and (b) sampling as principal cut both stand.

## 8. What a paper must discharge

1. Full proofs of T1–T4 (T4 is the research-grade contribution; T1–T3 are
   careful but standard-technique extensions of THY_0021 §§4–6).
2. Cut admissibility for the two-semiring graded judgment including ∃_ρ
   (extend THY_0023's till metatheory; the principal ∃_ρ case IS §5's collapse).
3. The lazy/recursive form: guarded-fixpoint waves, inside-mass existence and
   uniqueness (subcritical case), conditioning on regular tree sorts.
4. Positioning per §7, plus the Markov-categories check.
5. Operational adequacy against the implementation (TODO_0292 P0–P3: bitmask
   encoding, `@w` priors + min-entropy chooser + subcriticality lint, wave
   table + `substituteEvar` decimation driver, recursive sorts).
