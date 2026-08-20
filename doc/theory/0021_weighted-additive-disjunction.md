---
title: "Weighted Additive Disjunction: A Probability-Graded Internal Choice for the Lax Monad"
created: 2026-08-20
modified: 2026-08-20
summary: "till's `woplus` (A +[q] B) is internal choice weighted by a rational q ∈ [0,1] — the PRODUCER decides a branch probabilistically. A plain ⊕ reading drops the weight and is unsound for the distribution semantics. This document supplies the missing proof theory (THY-A gap): a probability-graded lax judgment Δ ⊢ C ⟨w⟩ whose weight w ∈ [0,1] is carried by the (·,1) probability monoid — a SECOND grading orthogonal to THY_0018's tropical (max,+) delay grade. Two weighted right rules split the mass q + (1−q) = 1; there is no left rule (consequent-only). Mass conservation (weights of the complete derivation forest sum to 1), the derivation-forest ≅ settleExplore tree ≅ absorbing-Markov-chain unfolding correspondence (aggregate mass = the winProbDP recurrence), and unbiasedness of the settle PRF sampler are proved on paper; a weighted cut where delays add and weights multiply composes the two gradings."
tags: [linear-logic, forward-chaining, proof-theory, graded-types, lax-monad, clf, till, monad, probabilistic, additive, weighted-choice]
category: "Timed Rewriting"
unique_contribution: "Three claims not found in the literature (novelty audit 2026-08-20): (1) internal additive disjunction graded by a PROBABILITY from the ([0,1], ·, 1) monoid, with sequent right-rules that track the branch mass and a mass-conservation metatheorem — Ceptre and PPDP-style probabilistic rewriting attach probabilities to RULE choice operationally, but no additive CONNECTIVE carries a weight grade in a sequent calculus; (2) two orthogonal gradings on one lax monad — a tropical (max,+) delay grade (THY_0018) and a probability (·,1) weight grade — composed by a single cut where delays add and weights multiply; (3) a proof-theoretic identification of the weighted-derivation forest with an absorbing Markov chain's unfolding, so aggregate derivation mass equals the combat DP `winProbDP` exactly (rational, not floating-point), and the operational PRF sampler is its unbiased Monte-Carlo estimator."
references:
  - "TODO_0265 — timed graded rewriting (the till calculus; woplus is its Phase 4b weighted choice)"
  - "THY_0018 — The Delay-Graded Lax Monad (THY-A; the delay grading this document runs orthogonal to)"
  - "THY_0019 — Timed Matching and the Settle Scheduler (the PRF sampler and settleExplore)"
  - "THY_0001 — Exhaustive Forward Chaining (oplus in forward consequents; the unweighted parent)"
  - "THY_0004 — Symbolic Branching (internal vs external choice, ⊕ vs &)"
  - "Fairtlough & Mendler (1997). Propositional Lax Logic. Information and Computation."
  - "Watkins, Cervesato, Pfenning & Walker (2002). A Concurrent Logical Framework I. CMU-CS-02-101."
  - "Katsumata (2014). Parametric Effect Monads and Semantics of Effect Systems. POPL."
  - "Gaboardi, Katsumata, Orchard, Breuvart & Uustalu (2016). Combining Effects and Coeffects via Grading. ICFP."
  - "Danos & Ehrhard (2011). Probabilistic Coherence Spaces as a Model of Higher-Order Probabilistic Computation. Information and Computation."
  - "Martens (2015). Ceptre: A Language for Modeling Generative Interactive Systems. AIIDE (probabilistic rule choice)."
  - "Baccelli, Cohen, Olsder & Quadrat (1992). Synchronization and Linearity. Wiley (the (max,+) dioid)."
  - "Kemeny & Snell (1976). Finite Markov Chains. Springer (absorbing chains)."
---

# Weighted Additive Disjunction

**Status.** Design + on-paper proofs. Nothing here is machine-checked; §9 lists
exactly what a paper write-up must still discharge. The operational side (settle
sampling, `settleExplore` exact weights, agreement with the combat DP) IS
executable and tested — `tests/engine/till-woplus.test.js`, `tests/fixtures/till-duel.ill`.

## 1. The gap

`till` declares one connective with operational semantics but no sequent rules
(`calculus/till/till.rules`):

```
woplus: weight -> formula -> formula -> formula     % A +[q] B, q ∈ [0,1] ∩ ℚ
```

Operationally (`doc/documentation/till.md`): in a monad body, `A +[q] B`
produces `A` with probability `q` and `B` with `1−q`. `settle` samples one
branch through the D17 stateless PRF; `settleExplore` expands *both*, putting the
weight on the edge, so the tree is the exact outcome distribution — leaves carry
`weight : [num, den]`, the exact rational product of the branch weights on their
path, and the leaf weights sum to 1.

Why there are no rules yet. The obvious move — read `+[q]` as ordinary internal
choice `⊕` (THY_0001, THY_0004) — is **unsound for the distribution**: `⊕`'s
right rules `Δ ⊢ A / Δ ⊢ A ⊕ B` and `Δ ⊢ B / Δ ⊢ A ⊕ B` discard `q`, so the two
derivations of `A ⊕ B` are indistinguishable and carry no mass. A calculus that
erases the weight cannot state, let alone prove, that `settleExplore` computes
`9/16` for the 1-rock-versus-2-scissors duel. The weight must be *tracked in the
judgment*. That is the content of this document — the "probabilistic judgment
(THY-A)" the rules file defers to.

## 2. The weight monoid — a second grading

THY_0018 grades the lax monad `{A}` by a **delay** `d` from the tropical dioid
`(ℚ≥0, max, +, 0)`: availabilities combine by `max` (coeffect), delays compose
by `+` (effect). Weighted choice is a **different** algebra on the same monad:

> **The weight monoid** is `W = ([0,1] ∩ ℚ, ·, 1)` — the multiplicative monoid
> of rational probabilities, with a partition operation `q ↦ (q, 1−q)` splitting
> a unit of mass into two sub-units summing to 1.

`W` is commutative, associative, has unit `1`, and is exact (bigint num/den — no
floating point). It is the mass carried by a *derivation*: independent choices
multiply (probabilistic independence), which is exactly `settleExplore`'s
path-product. Delays and weights never interact — one is `(max,+)` on
availability stamps, the other is `(·,1)` on derivation mass — so a term may be
graded by both at once (§7). This orthogonality is the design's core: **till
carries two independent gradings on one lax monad.**

## 3. The probability-graded judgment

Extend the graded lax judgment `Γ ; Δ ⊢ C lax@d` (THY_0018 §3) with a **weight
annotation** — the mass of *this* derivation:

```
Γ ; Δ ⊢ C  lax@d  ⟨w⟩            w ∈ W
```

Read: "from persistent `Γ` and linear `Δ`, `C` is achievable within delay `d`,
and *this derivation* carries mass `w`." Every rule of THY_0018 leaves `w`
untouched (`w` threads unchanged; a rule with two premises requires equal
weights and passes it on — weights compose only at a `woplus` node and at cut,
§7). The unit is `w = 1`: an unweighted derivation has full mass. Two rules
introduce `woplus`, and — crucially — there is **no left rule**:

```
Γ ; Δ ⊢ A  lax@d  ⟨w⟩
─────────────────────────────────────  +[q]R₁   (take the left branch)
Γ ; Δ ⊢ A +[q] B  lax@d  ⟨q · w⟩

Γ ; Δ ⊢ B  lax@d  ⟨w⟩
─────────────────────────────────────  +[q]R₂   (take the right branch)
Γ ; Δ ⊢ A +[q] B  lax@d  ⟨(1−q) · w⟩
```

Both rules are **non-invertible** (a proof commits to one branch) and preserve
the delay `d` (a weighted choice is instantaneous — the duel's `fight` rule fires
at one activation; the weight is on the *outcome*, not the clock). `q` is a
ground rational in `[0,1]` — the compiler's `weight <: grade` fence — so
`q · w, (1−q) · w ∈ W` are well-defined.

**Why consequent-only (no `+[q]L`).** `woplus` is the PRODUCER deciding an
outcome by lottery; the consumer never chooses (that is `&`, external choice) and
never case-splits a *given* weighted disjunction into a proof obligation. A left
rule `Δ, A +[q] B ⊢ C` would have to say what it means to *use* a probabilistic
resource — a measure-theoretic hypothesis — which till does not have and does not
need: `woplus` occurs only inside a monad body, in consequent position, exactly
where the forward engine expands it. This is the proof-theoretic image of the
`till.rules` note that a weight-dropping `⊕` reading "would be dishonest": we do
not give `+[q]` an antecedent life it cannot soundly have.

## 4. The derivation forest and mass conservation

Fix a sequent `𝒮 = (Γ ; Δ ⊢ C lax@d)` whose succedent `C` contains woplus nodes.
Its **derivation forest** `𝔇(𝒮)` is the set of all cut-free proofs that differ
only in the `+[q]R₁/R₂` choices (all other rules being either forced or
weight-transparent). Each `π ∈ 𝔇(𝒮)` carries a mass `w(π) ∈ W` — the product of
the `q`/`(1−q)` factors at its woplus nodes.

> **Theorem 1 (mass conservation).** If `𝒮` is derivable, then
> `Σ_{π ∈ 𝔇(𝒮)} w(π) = 1`.

*Proof.* Induction on the number `n` of woplus nodes reachable in `C` under the
forced skeleton. `n = 0`: `𝔇(𝒮)` is a singleton with mass `1` (the empty
product). `n = k+1`: pick the topmost woplus node `A +[q] B`. Every derivation
resolves it by `+[q]R₁` (mass factor `q`, continuing into a forest for the
`A`-subgoal) or `+[q]R₂` (factor `1−q`, forest for the `B`-subgoal). By the IH
each sub-forest sums to `1`, so the total is `q · 1 + (1−q) · 1 = 1`. Associativity
and commutativity of `·` let the per-node factors be collected in any order. ∎

Mass conservation is the proof-theoretic content of "`settleExplore`'s leaf
weights sum to 1" (`till-woplus.test.js` asserts `Σ leaf weight = 1` exactly, in
bigints). `𝔇(𝒮)` **is** the settleExplore tree: each `+[q]` node is a `choice`
branch, each leaf a maximal derivation, and the edge weights are the rule
factors. The identification is definitional once the rules above are in place.

## 5. The absorbing-chain correspondence

The duel fixture (`till-duel.ill`) is `fight : rock * sci -o { woplus 3/4 rock sci }`.
Its repeated firing is an absorbing Markov chain on states `(r, s)` (rocks,
scissors): each fight kills a scissors with probability `p = 3/4`, a rock with
`1−p`, until `s = 0` (rocks absorbed-win) or `r = 0` (scissors win). The combat
reference DP (`till-woplus.test.js`) is

```
winProbDP(r, s, p) = 1 (s=0) | 0 (r=0) | p·winProbDP(r, s−1, p) + (1−p)·winProbDP(r−1, s, p)
```

> **Theorem 2 (derivation mass = chain probability).** For the duel program, the
> aggregate mass of derivations whose leaf state satisfies an observable `O`
> equals the absorbing-chain probability of `O`. In particular
> `Σ_{π : leaf(π) ⊨ rock survives} w(π) = winProbDP(r₀, s₀, 3/4)`.

*Proof.* The forced skeleton fires `fight` until quiescence; each firing
introduces one `woplus 3/4` node whose two resolutions are exactly the two chain
transitions from the current `(r,s)`, with the SAME probabilities `3/4, 1/4`
(the rule's ground weight). So the map `π ↦ (its sequence of branch choices)` is
a bijection between `𝔇(𝒮)` and root-to-absorption paths of the chain, and it
multiplies the matching per-step probabilities (§2: mass = path product =
transition-probability product). Summing over paths landing in `O` on both sides
gives the claim; Theorem 1 is its `O = ⊤` special case (total mass 1 = the chain
is almost-surely absorbing on a finite grid). The equality is *exact* in `ℚ` —
both sides are the same rational — which is why `settleExplore` reproduces
`winProbDP(1,2,3/4) = 9/16` with no floating-point drift. ∎

This is the theorem the operational suite checks numerically; §4–§5 give it a
proof-theoretic reading in which the *tree is the distribution* is a statement
about a derivation forest, not merely an engine artifact.

## 6. The PRF sampler is an unbiased estimator

`settle` (as opposed to `settleExplore`) draws ONE derivation, sampling each
`+[q]` node by a 32-bit uniform PRF (`u < q ↦ left`, D17). Write `Ŵ_N(O)` for the
fraction of `N` seeds whose settled state satisfies `O`.

> **Theorem 3 (unbiased sampling).** `settle`'s branch draw selects `π ∈ 𝔇(𝒮)`
> with probability `w(π)` up to the PRF's discretisation bias `< 2⁻³²` per draw.
> Hence `E[Ŵ_N(O)] = Σ_{leaf ⊨ O} w(π) ± Nε`, `ε < 2⁻³²`, and `Ŵ_N(O) →
> winProbDP` as `N → ∞`.

*Proof.* At each node the PRF compares a floor-discretised uniform `u ∈ {k/2³²}`
against `q`; `P[u < q] = ⌊q·2³²⌋/2³² = q ± 2⁻³²`. Draws at distinct nodes use
independent PRF sub-streams (D17 mixes the node's state hash), so the path
probability is the product of per-node probabilities `= w(π) ± (depth)·2⁻³²`.
Linearity of expectation over the finite forest gives the bias bound; Theorem 2
identifies the limit with the DP. ∎

`till-woplus.test.js`'s "chi-square-lite" test is the empirical form: 4000 seeds
land within `4σ` of `3/4`. Theorem 3 is why a `4σ` gate is the right shape — the
estimator is unbiased, so a genuinely mis-weighted sampler is tens of σ out.

## 7. Weighted cut: delays add, weights multiply

The two gradings compose in ONE cut. Alongside THY_0018's graded lax cut (delays
compose by `+`):

```
Γ; Δ ⊢ S lax@d ⟨w⟩      Γ; Δ', S ⊢ C lax@e ⟨w'⟩
────────────────────────────────────────────────────  cut  (admissible)
Γ; Δ, Δ' ⊢ C lax@(d + e) ⟨w · w'⟩
```

The delay bookkeeping `d + e` is THY_0018 §8 unchanged; the new content is the
weight `w · w'` — sequential composition of independent weighted derivations
multiplies their masses. Cut elimination:

- `woplus` is **consequent-only**, so it is NEVER a cut formula (no `+[q]L` to
  meet a `+[q]R`): there is no principal case for it. The weight rides passively
  through every commutative case (each threads `⟨w⟩` unchanged), so THY_0018 §8's
  seven-case argument applies verbatim with `⟨w⟩` a spectator, and the weight of
  the cut-free proof equals that of the original (elimination is weight-preserving,
  just as it is `≤`-preserving on delays).
- The genuine composition of weights happens at the object level — a `fight`
  followed by another `fight` — where the monadic bind (`monad_l`, the graded
  `μ`) is the cut: `w · w'` there is precisely the two-step transition product of
  §5. Associativity of `·` = associativity of `μ` = independence of successive
  rounds.

So the probability monoid is a lax-monoidal grading in Katsumata's sense, exactly
as the delay dioid is, and the two are combined by grading the monad in the
product `(ℚ≥0, max,+) × ([0,1], ·)` — coeffect–effect on the left factor, pure
effect on the right. Neither factor sees the other.

## 8. Relation to the settle bridge (THY_0018 §5)

The `monad_r2` settle bridge realises `@fire` as an oracle for the *delay*
fragment. woplus extends the residue it records: a bridge run over a
woplus-bearing program emits, per firing, the sampled branch `alt` (settle) or —
in `settleExplore` — the full weighted fork. Bridge soundness (THY_0018 §5)
lifts: a `settle` success is one *sampled* `π ∈ 𝔇(𝒮)`, hence a real derivation,
so the oracle still only asserts derivable sequents; what woplus adds is that the
oracle now also carries `w(π)`, and the *ensemble* of oracle runs is Theorem 3's
estimator of the derivation-forest distribution. Completeness is still false for
the same reason (subeffecting `monad_r` proves `a ⊢ {a}@d` with no forward step),
and the bridge step is still `unverified: 'modeSwitch'` — the sampled draw is
trusted, its adequacy is Theorem 3.

## 9. What is proved, and what a paper still owes

Proved on paper here: the rules (§3), mass conservation (Thm 1), the
absorbing-chain correspondence (Thm 2), sampler unbiasedness (Thm 3), and the
weighted-cut composition (§7). Executable and tested: all three theorems'
numerical shadows (`till-woplus.test.js`, exact rationals). **Still open for a
POPL/LICS write-up:**

1. **Mechanisation.** None of §3–§7 is machine-checked. The weight-transparent
   threading of `⟨w⟩` through every THY_0018 rule, and the spectator role of
   `woplus` in cut elimination, are routine but unverified (same status as
   THY_0018 §8).
2. **A general-`q` case study beyond the duel.** Theorem 2 is proved for the
   single-type absorbing chain; a second case study (e.g. a branching process, or
   a mixed-type combat with non-uniform matchmaking) would exercise nested
   independent woplus with distinct weights.
3. **Continuous / metavariable weights.** `weight` is a ground rational today
   (Phase 6 allows a fire-time-bound `Q`); a judgment where `q` is a *bound
   variable* solved at fire time needs the weight monoid to interact with
   unification — stated as future work, not attempted here.
4. **Categorical semantics.** The natural model is a probabilistic coherence
   space or a Markov category; identifying the graded monad `{−}⟨w⟩` with a known
   probability monad (Giry / distribution) is the semantic counterpart of Thm 2
   and is not developed here.

## 10. Novelty and related work

Ceptre (Martens 2015) and probabilistic rewriting attach probabilities to *rule
selection* operationally; probabilistic coherence spaces (Danos–Ehrhard 2011)
model higher-order probabilistic computation denotationally. Neither gives an
additive *connective* a weight grade in a sequent calculus. Graded modalities
(BLL, Granule, THY_0018) grade *exponentials* or *monads* by resource/effect
semirings, not by probabilities partitioning a unit of mass. The specific
contributions are the three claims in the frontmatter: a probability-graded
internal choice with mass-conserving right rules, two orthogonal gradings on one
lax monad composed by a single cut, and the derivation-forest ≅ absorbing-chain
identification making aggregate mass equal the combat DP exactly.

## 11. References

See the frontmatter `references`. Internal companions: THY_0018 (the delay
grading), THY_0019 (the settle sampler), THY_0001/THY_0004 (unweighted internal
choice `oplus`, the connective this weights).
