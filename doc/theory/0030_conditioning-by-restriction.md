---
title: "Conditioning by Restriction: the Derived Rule Dissolves into the Sort Slot"
created: 2026-09-02
modified: 2026-09-02
summary: "TODO_0300 item 3(c) discharged: conditioning a measure-weighted existential on a datasort event S ⊑ s needs no new connective, no new sequent rule, and no new conservation metatheory. The conjectured 'derived conditioning rule' (cut ∃_ρ against a membership derivation) dissolves into the SORT SLOT: a conditioned draw is the base draw plus a checker-side membership premise (the datasort clauses, resolved deterministically), the token carries the binder's sort name, and hard conditioning is RESTRICTION in the unnormalized mass discipline — excluded worlds go to zero, surviving worlds keep their masses, so THY_0027's cut admissibility with exact trace conservation holds verbatim (membership derivations are persistent-zone clause derivations over ground witnesses, untouched by linear-zone reductions). The inside mass m(S) — the least solution of the linear equation system read off the clauses — is exclusively the SAMPLER's normalizing constant, made observable by a zero-variance identity (importance ≡ m(root state) on bias-free fully-drawn runs; the per-draw factors telescope) and certified by substitution into its own equations, never by re-solving."
tags: [linear-logic, probabilistic, will, conditioning, graded-types, refinement-types, provenance, certificates]
category: "Probabilistic Generation"
unique_contribution: "Conditioning for a measure-weighted existential realized as a checker-side membership premise on the draw oracle over regular-tree (datasort) events — completing the dissolution pattern: grades on formulas, draws in the zone, CONDITIONING IN THE SORT SLOT. Three results: (1) the conditioned calculus IS the base calculus (a conditioned derivation is a base derivation whose draws satisfy additional ground membership side-derivations; cut admissibility with exact weight conservation is inherited verbatim, not re-proved); (2) the zero-variance identity — the mass-proportional conditioned sampler's importance weight equals m(root state) exactly on every bias-free fully-drawn run (and m(root)/Π m(dropped) in general), realizing the optimal-proposal folklore of importance sampling as a certified engine invariant that doubles as an independent solver check; (3) the certification split — the solver (calculus-bound oracle machinery) finds inside masses, the checker verifies them by SUBSTITUTION into the equation system whose uniqueness is the load-time subcriticality discipline, so the trusted base never contains the solver."
references:
  - "THY_0026 §4/§8 T1/§9 item 3 — the conditioning conjecture and the fixpoint mathematics this realizes"
  - "THY_0027 — cut admissibility with exact trace conservation (inherited verbatim here); §3g the dissolution precedent"
  - "THY_0029 — the mass-splitting dissolution (the same pattern one item earlier)"
  - "THY_0020 — refinement sorts (rung 1); datasorts are their regular-tree extension"
  - "TODO_0011 fences B slices 1–4 (calc 457b18f1, e2254216, 798fb7a5, 644d8895) — the shipped machinery and pins"
  - "Freeman & Pfenning (1991). Refinement types for ML (datasorts — here over a weighted term language)"
  - "Lari & Young (1990); Baker (1979). The inside algorithm for stochastic grammars (m(S) is an inside mass over automaton states)"
  - "Chi & Geman (1998). Estimation of probabilistic context-free grammars (subcriticality — our divergence fence)"
  - "Li, Ahmed & Holtzen (2023). Lilac (a conditioning modality at the program-logic level; ours is engine-level, certified, with no modality)"
  - "Owen, Monte Carlo theory (the optimal-proposal zero-variance folklore that Proposition 2 operationalizes)"
---

# Conditioning by Restriction

**Status.** Proved, implemented, and pinned (2026-09-02). Discharges
TODO_0300 item 3(c) — the theory half of inside-mass conditioning; the
machinery is TODO_0011 fence B (slices 1–4), pins in
`tests/engine/will-datasorts.test.js`. With 3(a)/3(b) shipped, THY_0026
§9 item 3 closes; the only remaining T4-d item is (iii), the
quantitative good-labelling theorem.

## 1. Setting

A **datasort** S ⊑ s (fence B) is a regular tree language over a
classifier's constructors, declared by ordinary membership clauses:

```
even <: lst.
even/n: even nil.
even/c: even (cons H T) <- odd T.
```

The clause-shape fences (one depth-1 constructor pattern per head,
premises classify immediate subterm variables, one clause per
(datasort, head), ≤1 recursive argument per head within its SCC) make
the clause set a top-down deterministic tree automaton with a LINEAR
mass system. Conditioning has two surfaces — static, at the binder
(`exists X: even @w. A` — the wave is born at state `even`) and
dynamic, during the run (`!within E S` facts intersect states;
anonymous products, THY_0028's bias discipline generalized from
members to events).

**The load-bearing decision (B4): hard conditioning is RESTRICTION.**
In the unnormalized mass discipline (THY_0026 §2), conditioning on S
zeroes the worlds outside S and leaves every surviving world's mass
UNCHANGED. Renormalization — division by the inside mass m(S) — exists
only in the sampler's probabilities, never in the mass calculus. Every
consequence below flows from this one decision.

## 2. The derived rule dissolves into the sort slot

THY_0026 §4 conjectured a **derived conditioning rule**: cut ∃_ρ
against a sort-membership derivation to obtain a conditioned
existential ∃_{ρ|S}, with new metatheory ("trace conservation through
the renormalization"). The realized design needs none of it:

**Theorem 1 (conditioning is the base calculus).** The conditioned
existential ∃_ρ x:S. B *is* the connective ∃_ρ with the datasort name
in its sort slot. A conditioned @draw step at S is admissible iff the
base step at S's underlying classifier is admissible AND the witness
head is admitted by S — a membership side-derivation from the declared
clauses (operationally: the automaton, which is the deterministic
image of clause resolution). The minted token is `drawn c S` — the
binder's sort name, one atom. No sequent rule is added, no rule is
changed: drawn_l matches sort slots by hash equality and never
inspects them; the membership premise lives in the CHECKER, exactly
where the base calculus already keeps the classifier-membership
premise of every draw.

*Proof.* By construction of fence B: the surface compiles to
`superpose(S, ∃x.B)` — the same suspended fact shape; the driver
resolves S to (base, state) and restricts the draw's choice set; the
@draw checker (draw-check.js) re-derives head admission from the
program's clauses via the same deterministic automaton construction.
Dynamic conditioning never reaches the sequent at all: the effective
state rides the @draw RECORD (certificate data, like bias factors on
@fire records), and the token keeps the binder's sort. ∎

This completes the dissolution pattern of THY_0027 §3g and THY_0029:
**grades on formulas, draws in the zone, conditioning in the sort
slot.** Randomness enters the calculus at exactly one point — the draw
oracle — and conditioning is a premise on that oracle, not a
connective.

**Corollary 1 (conservation verbatim).** Cut admissibility with exact
trace conservation (THY_0027) holds for conditioned derivations with
NO new argument. A conditioned derivation is a base derivation whose
draws satisfy additional membership side-derivations; those are
persistent-zone clause derivations over GROUND terms (witnesses and
tokens are ground — THY_0027 §1's fences), and cut reduction touches
them only as ground-for-ground substitution into already-ground goals
(the §3g case (g) argument, unchanged). Run mass stays Π ρ over ⟨Θ⟩:
restriction never rescales a surviving mass, so the endsequent's
weight reading is untouched. The conjectured obligation
— "conservation through the renormalization" — is vacuous: there is no
renormalization in the judgment. ∎

## 3. The inside mass is the sampler's constant — and it is observable

m(S), the total prior mass of S's language, is the least solution of
the equation system read off the clauses (m(S) = Σ_heads ρ(h)·Π
m(child states)); the linearity fence makes each SCC's system linear
over ℚ≥0, solved exactly, with divergence detected by Perron–Frobenius
(a critical/supercritical component yields a singular system or a
negative entry — a load error, since a diverging normalizing constant
makes the conditioned sampler meaningless). This is the inside
algorithm of stochastic grammars, keyed by automaton states, run once
at load and lazily for products.

The sampler draws heads mass-proportionally — w(c) = ρ(c)·Π m(child
states) — while recording ρ(c) as the mass factor (restriction!). The
normalizing constants are then not silent: they are pinned to an exact
run invariant.

**Proposition 2 (zero-variance importance; the "B6" invariant pinned in will-datasorts tests and CLAUDE.md).** On a bias-free
conditioned run in which every opened wave is drawn (none dropped),
the T3 importance weight equals m(root state) — for EVERY seed. In
general, importance = m(root) / Π m(states of waves dropped
un-observed), constant per drop pattern, and E[importance] = total
surviving mass per attempt (T3) throughout.

*Proof.* The per-draw importance factor is massFactor·total/drawWeight
= ρ(c)·m(D)/(ρ(c)·Π_j m(D_j)) = m(D)/Π_j m(D_j) at each drawn node.
Multiplying over the drawn tree: every non-root node's state mass
appears once as its parent's denominator and once as its own
numerator; the product telescopes to m(root) divided by the masses of
denominator entries that never acquire a numerator — exactly the
dropped waves. Unbiasedness is the standard importance identity
(importance = mass/P(run) by construction). ∎

This is the optimal-proposal folklore of importance sampling (the
exact conditional proposal has zero variance) realized as a CERTIFIED
ENGINE INVARIANT — and it doubles as an independent check of the
solver: the sampler and the Gaussian elimination must agree exactly,
seed by seed (pinned: importance ≡ 8/3 on even-lists, ≡ 2 on nonempty
lists, ≡ 32/15 on the entangled product even∧allb0).

## 4. Certification: the solver is never trusted

The certificate carries conditioning as data and verifies it by
re-derivation (fence B slice 4):

- the @draw record carries the EFFECTIVE conditioning state (the
  within-derived product key when it differs from the registered
  sort); the checker re-derives head admission against it — states
  resolve deterministically from the declared clauses, so a checker
  rebuilds them independently of the driver;
- claimed inside masses are verified BY SUBSTITUTION into their own
  equations, in exact rationals (`verifyMasses`): uniqueness of the
  solution is the load-time subcriticality discipline, so plug-in
  equality is the whole check. The checker never imports the solver —
  the solver is calculus-bound oracle machinery (will's config), the
  checker is ~40 lines of arithmetic;
- masses materialize as ground `mass s m` facts when the program
  declares the predicate (the subsort/prior discipline), so in-logic
  `!mass S M` premises are total lookups and the verification path is
  clause-referenceable;
- tampering is pinned in both channels: a doctored mass table fails
  certification with the violated equation named; a doctored
  conditioning state on a draw node fails kernel verification
  ("member not admitted").

Run mass remains readable off the endsequent alone (Π ρ over ⟨Θ⟩,
THY_0027); conditioning adds auditability of the sampler's accounting
without adding anything to the endsequent.

## 5. What this does not claim, and the residual

- **Nonlinear events (fence B″).** Tree-shaped datasorts (two
  recursive arguments per head) have ALGEBRAIC inside masses — outside
  the exact-rational discipline; the fence refuses them at load with a
  recorded design (interval-refined sampling terminates a.s. because a
  rational draw never equals an algebraic threshold). Unconditioned
  tree sorts are unaffected (lazy PCFG needs no masses).
- **Soft region weighting** (`!bias E S q` over an event rather than a
  member) is deferred with a recorded shape (weighted-automaton mass
  systems); member-level bias and hard event conditioning compose
  today.
- **Modelling honesty** is THY_0028's: the calculus certifies that the
  product structure matches the token structure; whether a datasort
  event models the intended real-world event stays the modeller's
  assertion, made inspectable.
- **T4-d(iii)** — the quantitative good-labelling theorem for
  derivation forests — is the one remaining open item of the will
  track (TODO_0300's final task). This document supplies its
  conditioning face: THY_0028's disjoint-provenance base case now has
  the conditioned analogue (membership side-derivations as the
  labelling's guard sites).
