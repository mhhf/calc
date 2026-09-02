---
title: "Grade Certificates: Single-Counting and the Syntactic Independence Discipline"
created: 2026-09-01
modified: 2026-09-02
summary: "T4-d(i) discharged: in will's bias discipline, evidence identity IS fact identity — value-only bias facts under-identify (two independent equal-likelihood observations collapse to one factor), so the correct encoding is SOURCE-TAGGED bias facts (arity ≥ 3; extra arguments enter the content-addressed identity, which the driver already supports). Under the linear-evidence discipline (observations consumed linearly, one bias conclusion per (wave, member) per rule), single-counting is a theorem: posterior factors are in bijection with consumed observations, each likelihood entering exactly once. Double-counting requires a syntactic marker ($ or ! on the observation) and is CERTIFICATE-VISIBLE, never numerically visible: the honest and smuggled programs produce identical posteriors, and only the run certificate's fire provenances (disjoint vs overlapping) tell them apart — independence is a structural property of the derivation, exhibited by the certificate, not a property of the number."
tags: [linear-logic, probabilistic, provenance, will, graded-types, conditioning, independence]
category: "Probabilistic Generation"
unique_contribution: "The syntactic independence discipline for a probabilistic forward-chaining calculus, with both directions made precise and executable: (1) the single-counting theorem — linearity of evidence tokens + per-rule bias-uniqueness implies the posterior is the correctly-factored Bayesian product with each observation contributing exactly once (the PSL/Lilac '⊗ = independence' reading as a theorem about ALL runs of an engine, not a program-logic judgment); (2) the certificate half — double-counting cannot be detected from the posterior (an explicit honest/smuggled program pair produces IDENTICAL totals) but is always exhibited by the run certificate's fire provenances, and its only syntactic entry points are the $/! markers on observation predicates. A third finding not in the T4-d sketch: content-addressed set semantics UNDER-identifies value-only evidence (independent equal-likelihood observations dedup to one factor) — the source-tag discipline (provenance as part of fact identity) is forced, and the existing arity-open bias reader already implements it."
references:
  - "THY_0026 §4/§6 T4-d/§9 item 1 — the conjecture this discharges (part (i); part (ii) discharged by THY_0029's dissolution, part (iii) remains)"
  - "THY_0027 — trace-judgment cut admissibility (the token discipline; no-promotion-through-a-draw is why observations under ! are the marked case)"
  - "TODO_0300 — the phase plan (task 1)"
  - "Barthe, Hsu & Liao (2020). A Probabilistic Separation Logic. POPL (∗ = independence — the reading Theorem 1 operationalizes; cite, don't claim)"
  - "Li, Ahmed & Holtzen (2023). Lilac. PLDI (CI = ∗ under the disintegration modality □_Z, standard SL frame rule — program-logic-level; ours is engine-level over all runs. Description corrected 2026-09-02, RES_0142: no standalone C-Indep judgment)"
  - "Bao, Docherty, Hsu & Silva (2021). DIBI. LICS (qualitative conditional-independence logic — Thm V.1 is the qualitative ancestor of the T4-d(iii) residual; author corrected Pym→Silva 2026-09-02, RES_0142)"
  - "Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS (provenance as the identity criterion — here at the FACT level, inside the posterior product)"
  - "Sato (1995). Distribution semantics (independent switch draws — the msw analogue of source tags)"
---

# Grade Certificates: Single-Counting and the Syntactic Independence Discipline

**Status.** Proved and pinned (2026-09-01). Discharges THY_0026 §9 item 1
part (i) — the grade-certificate theorem. Part (ii) (mass-splitting
graded contraction) closed by dissolution 2026-09-02 — §6's probe
resolved affirmatively in THY_0029. Part (iii) (quantitative
good-labelling for derivation forests) remains open. Executable pins:
`tests/engine/will-decimate.test.js` ("evidence discipline").

## 1. Setting

The bias discipline (THY_0026 §4, M8; implemented in
`lib/engine/decimate.js _posterior`): a wave `e` over classifier `s` has
posterior weights

```
w(e,c)  =  ρ(c) · Π { q  |  bias(e, c, q, …) a DISTINCT persistent fact }
```

where "distinct" is content-addressed identity — the same fact hash
counts once (set semantics; the monotone-conditioning guarantee). An
**observation** is a linear fact an evidence rule consumes; a **bias
rule** is a forward rule deriving persistent `bias` conclusions from
observations. The Bayesian reading demands
`posterior ∝ prior · Π_i P(obs_i | c)` with the product ranging over
*conditionally independent observations, each exactly once*.

The question T4-d(i) asks: what does the *syntax* guarantee about that
product?

## 2. Evidence identity is fact identity — and value-only facts under-identify

The driver's dedup criterion is the fact hash. This conflates two
situations the Bayesian reading must separate:

- **Same evidence, re-derived** (a rule refires, a clause re-proves):
  same fact, dedup is *correct* — conditioning is idempotent.
- **Distinct evidence, same likelihood**: two independent observations
  each supporting `c` with likelihood ½ derive `bias(e,c,½)` twice —
  same hash, ONE factor. The honest posterior wants ¼; the driver
  computes ½. **Value-only bias facts under-count independent
  evidence.** (Pinned: program A below, exact total 4 instead of 7/2.)

The repair is not a code change but a *discipline*: the bias fact must
carry its **source** — `bias(e, c, q, src)` — so that fact identity
coincides with evidence identity. The driver already supports this: the
posterior reader accepts arity ≥ 3, reads children 0/1/2 (wave, member,
weight), and ignores further arguments *for the value* while they
participate in the hash. Distinct sources multiply; the same source
re-derived dedups. (Pinned: program B, total 7/2 = 2·½·½ + 1 + 2.)
Programs declare `bias` with their own arities and sorts (the
closed-world bias discipline), so the source sort is program-owned.

Boundary: the *clause-derived* bias probe queries the 3-ary goal
`bias(e, m, Q)`, so clause-derived bias remains value-identified —
source tagging is the forward-derived discipline. (A 4-ary clause probe
is a straightforward extension if ever needed; forward derivation is
the intended evidence channel — bias rules need a linear trigger
anyway.)

## 3. The single-counting theorem

Fix a program P and a set O of predicates designated *observations*.
Say P satisfies the **linear-evidence discipline** for O when:

- **(S1) linear consumption.** Every rule antecedent mentioning an
  O-predicate is a plain linear pattern: not `$`-preserved, not under
  `!`, not whole-bound. (Observations may be *produced* freely.)
- **(S2) bias uniqueness per rule.** No rule's consequent contains two
  `bias` conclusions with the same (wave, member) argument pair.
- **(S3) source discipline.** Bias conclusions are source-tagged, with
  sources chosen per rule (distinct rules use distinct source tags, as
  in §2).

**Theorem 1 (single-counting).** Under S1–S3, in every run of the
driver and for every wave `e` and member `c`: the bias factors
multiplied into `w(e,c)` are in bijection with a set of *pairwise
distinct consumed observation tokens*, via the fire that consumed the
observation and produced the fact. Consequently

```
w(e,c) = ρ(c) · Π_{o ∈ O_used(e,c)} ℓ_o(c)
```

with each observation contributing at most one factor — the
correctly-factored product under the independence reading.

*Proof.* The state is a multiset and firing is multiset rewriting: by
S1 each observation token is consumed by exactly one fire (the Arena's
consume is a multiset subtraction; reads and whole-binds, which would
let a token enable several fires, are excluded). Assign to each
persistent bias fact the fire that produced it; by S2 one fire
contributes at most one factor per (e,c); by S3 facts produced by
different fires have different hashes (different sources), so the
set-semantics dedup never merges factors from distinct fires, while
facts re-derived by the *same* rule from the same source dedup to one
(idempotence — pinned: program D, two copies of the same observation
under one rule still yield one factor... note this last case consumes
two tokens for one fact: single-counting is "at most once per
observation", and re-derivation *discards* the surplus token's factor
by S3's same-source dedup, which is the conservative direction). The
bijection follows: factors ↔ producing fires ↔ consumed observations,
injectively in both legs. ∎

Two remarks. (a) The theorem is engine-level: it quantifies over all
runs (sample, exact, stepwise), not over a program logic's judgments —
this is the PSL/Lilac "⊗ = independence" reading as an operational
theorem. (b) S1–S3 are *statically checkable* (pattern shapes and
consequent shapes), lint-shaped like D16/C1–C3.

## 4. The certificate theorem: violations are structural, not numeric

Relax S1: mark an observation `$`-preserved (or promote it). Then one
token can trigger several bias fires, and the posterior carries
`ℓ_o(c)²` — the double-count. Two facts make this a *certificate*
story rather than a *detection* story:

**Fact (numeric invisibility).** The honest and the smuggled program
can produce **identical posteriors**. Pinned: program B (two linear
observations, factors ½·½) and program C (one `$`-read observation
smuggled into two rules, factor ½²) both total 7/2 on the same domain.
No function of the weights distinguishes them — "the posterior looks
overconfident" is not checkable, because the number is the same number.

**Theorem 2 (certificate visibility).** (a) *Localization:* under
content-addressed multiset semantics, overlapping provenance — two
bias-producing fires sharing an observation token — is possible only
through the explicit sharing markers on the observation: `$`
(read/preserve), `!` (promotion), or whole-bind. A program clean of
these markers on O satisfies S1, and Theorem 1 applies. (b)
*Exhibition:* every run certificate (the settle/collapse trace and its
kernel-checked elaboration, TODO_0294/0298) records, per fire, the
consumed and reserved tokens; define a bias fire's *provenance* as its
consumed-or-reserved observation tokens. In the honest program the
bias fires' provenances are pairwise disjoint; in the smuggled program
they overlap. Overlap is decidable by inspection of the certificate —
no re-execution, no semantics. (Pinned: B's provenances are
`{obs1},{obs2}`; C's are `{obs},{obs}` — the trace discriminates what
the totals cannot.)

*Proof.* (a) is the contrapositive of Theorem 1's consumption argument:
without `$`/`!`/whole-bind, a token reaches one fire. (b) the event
records carry `consumed` and `reserved` multisets per firing (E7.3;
elaborated into the @fire chain by certifyRun/certifyCollapse), so
provenance is a projection of the certificate; disjointness is a
finite check. ∎

**This is the sense in which "the grade is a computable certificate"
(THY_0026 §6 T4-d):** independence of the evidence entering a posterior
is not a property of the posterior — it is a structural property of
the derivation, and the derivation is what will ships as the
certificate. The endsequent carries the draws (THY_0027); the fire
chain carries the evidence provenances; both halves of the probability
are audit-readable.

## 5. What this does and does not claim

- It does **not** claim the engine detects modelling errors: a program
  free of sharing markers can still encode correlated evidence as two
  "observations" that are correlated in the world. S1–S3 guarantee the
  *product structure* matches the *token structure*; whether tokens
  model independent events is the modeller's assertion — exactly the
  assertion the certificate makes inspectable.
- The `$`-marker is not banned — reads are the correct encoding when
  one fact legitimately conditions several *different* waves or
  members (WFC's `constrain` reads `$tile` — its biases land on
  different (wave, member) pairs, which S2 permits per rule and the
  disjointness argument extends to per-(e,c) products). The marked case
  is *shared evidence into the same (e,c) product*.
- Under-counting (§2) is the dual failure and is silent in the same
  way; the source discipline S3 removes both.

## 6. Design probe for T4-d(ii): the mass-splitting box likely dissolves

The sketch's □_{r+s}A ⊢ □_r A ⊗ □_s A ("mass splits over independent
channels") presupposes weight-graded formulas. will's standing lesson
(THY_0027 §3g: grades on formulas, draws in the zone) and §§3–4 above
suggest the box dissolves the same way the two-semiring judgment did:
"independent channels" is not a connective but the *disjoint-provenance
property* of Theorem 1 — splitting mass over channels IS ⊗-composition
of evidence with disjoint provenance, and the "certificate" is not a
grade annotation but the fire chain's provenance partition. Conjecture:
every sound instance of the mass-splitting law is derivable in will as
a Theorem-1 factorization, with no new connective; the law's content is
already exhausted by S1–S3 + Theorem 2(b). To refute: exhibit a use of
□_r that is not a provenance partition — the natural candidate is
*budgeted* evidence (spend r of a likelihood budget across branches),
which smells like the credits literature, i.e. a different modality
with a different discipline, not will's.

**RESOLVED (2026-09-02, THY_0029): the conjecture holds — T4-d(ii)
closes by dissolution.** The box's count face is the counted bang's
derivable splitting law, its mass face is ⊗-context splitting of the
token zone (multiplicative — the sketch's r+s was the budget semiring),
its sum face is the forking connectives; token-backed boxes are
definable as ⟨Θ⟩ ⊗ A, unbacked ones are weight-conservation leaks, and
the contraction shape would clone a draw (refuted executably). The
budgeted-evidence candidate is not a counterexample but the counted
bang's own discipline. See THY_0029 for the theorem and pins.

## 7. Residual

T4-d(iii) — the quantitative conditional-independence theorem for
derivation forests (graded good-labelling / quantitative DIBI Thm V.1)
— is untouched by this document and remains TODO_0300's final task;
Theorem 1 here is its base case (unconditional independence = disjoint
provenance), and the certificate projection of Theorem 2(b) is the
object its labelling would grade.
