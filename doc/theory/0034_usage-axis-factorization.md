---
title: "The Usage-Axis Factorization: Conservation Is Not Synchronization"
created: 2026-09-07
modified: 2026-09-07
summary: "Non-idempotent (conservation/usage) axes provably cannot live in the stamp algebra of timed linear multiset rewriting — stamp values are cartesian (broadcast to outputs, joined over reads, re-emitted by catalysts) while conserved quantities are linear at the value level, so any nontrivial conserved measure in the stamp slot double-counts. Every role a usage axis can play factors into existing machinery: trace measures over the event multiset (accounting/optimization), linear tokens (gating — conservation is what the multiset was already for), the chooser (preference), term-computed delays (timing feedback). The scheduling-dioid contract needs no generalization."
tags: [linear-logic, forward-chaining, graded-types, scheduling, timed-rewriting, trace-measures]
category: "Timed execution"
unique_contribution: "Two results not in the literature or prior CALC docs: (1) the broadcast no-go — in a timed rewrite semantics that broadcasts one conclusion stamp to every output and joins premise stamps uniformly (reads included), no nontrivial conserved measure can ride the stamp: duplication sites (multi-output broadcast, reads, $-catalysts, persistent contraction) create the quantity from nothing; readiness survives duplication because an upper bound is freely copyable — stamp values are cartesian, conservation values are linear, and a usage axis in the stamp slot is a value-level linearity violation, not merely a C4 failure (the algebraic conditions C1–C3+C4a all HOLD for (ℚ≥0,+,+,≤), so no purely algebraic refutation exists). (2) The completeness of the factorization: the five roles a usage quantity can play (accounting, optimization, gating, preference, timing feedback) each act at a distinct locus (trace, leaf set, enabledness, tie resolution, activation), and each locus already has a dedicated slot (trace measure, leaf Pareto under tied-contention adequacy, linear tokens, chooser, term-computed delays) — so the settle-optimality paper's usage-axis ⟨open⟩ closes with 'the framework was already complete', and the scheduling dioid keeps idempotent merge as a DEFINITIONAL boundary, not a limitation."
references:
  - "doc/paper/settle-optimality.md (§8.3 usage ⟨open⟩ — closed by §8.5; §8.4 tied-contention adequacy — powers the leaf-measure completeness)"
  - "THY_0033 (product stamps; the axis-confounding argument §3 is the same separation-of-concerns family)"
  - "THY_0026 (measure class — will's masses are the multiplicative trace-measure instance)"
  - "Knuth 1977 (generalization of Dijkstra to superior functions — the MONOTONE side of sum-aggregation is classical and fine; the no-go is specific to linear consumption + broadcast stamps)"
  - "Goodman 1999 / Eisner 2002 / Huang 2008 (semiring DP — aggregation over derivations lives at trace/forest level there too)"
  - "Girard–Scedrov–Scott 1992 (bounded linear logic) and graded-exponential lines: usage lives in TYPES/exponent grades, not in operational timestamps — consistent with the factorization"
---

# The Usage-Axis Factorization: Conservation Is Not Synchronization

## 1. The question

`settle-optimality.md` §8.3 left one algebra-class question ⟨open⟩: a
*usage axis* — cost/fuel values composing additively along a derivation
(`⊗ᵤ = +`) and aggregating additively across inputs (`⊔ᵤ = +`, "the
conclusion pays for all its inputs") — has a non-idempotent merge, which
breaks the induced-order framing (`a ⊔ a ≠ a`). What replaces the
scheduling story there? Does the scheduling-dioid contract need
reworking to admit conservation axes?

Answer: **no — and provably so.** The axis does not belong in the stamp
slot at all, and everything one could want from it is already served by
existing machinery. The ⟨open⟩ closes with "nothing was missing."

## 2. The refutation cannot be algebraic

On `(ℚ≥0, ⊗ = +, ⊔ = +, cmp = ≤)` the contract's core conditions all
HOLD: C1 (total order), C2 (isotone ⊗), C3 (inflationary), and C4a
(merge is an upper bound: `a + b ≥ max(a, b)`). Only C4b (selectivity)
and idempotency fail. So the B&B machinery of L1/L2 would formally run —
indeed sum-merge activation is Knuth's classical generalization of
Dijkstra to superior functions, and on the *monotone* side (facts as
values) it is a perfectly good semiring computation. The genuine no-go
is semantic, and specific to **linear consumption + stamp broadcast**.

## 3. The no-go: stamp values are cartesian, conserved values are linear

The timed semantics duplicates stamp values at four sites:

1. **Output broadcast** — every output of a firing receives the SAME
   `done = a(m) ⊗ δ` stamp;
2. **Reads** — a read premise joins its stamp into the activation
   (correctness: nothing is read before it exists) without consuming
   the token, so the same token's stamp enters every reader;
3. **`$`-catalysts** — a preserved token re-emits its stamp unchanged
   (and the engine's delta optimization relies on the before/after
   identity);
4. **Persistent facts** — timeless, contracted freely.

Duplication is *sound for readiness*: a stamp is an upper bound ("exists
from t on"), and upper bounds are freely copyable — order-theoretic
information is cartesian. It is *unsound for conservation*:

**Lemma (broadcast no-go).** Suppose token values are assigned by a rule
semantics that gives every output of a firing the same value
`f(v₁, …, vₖ)` of the premise values (broadcast), uniformly in how the
premises are held (consumed or read). Call a map μ from values to ℚ
*conservative* if for every firing, Σ_outputs μ − Σ_consumed-inputs μ is
a rule constant (independent of the state and of the number of outputs
and readers). Then no nontrivial μ exists: a rule with two outputs
books `2·μ(f(v̄))` against the same consumed inputs as its one-output
variant (the "constant" scales with output count), and a token read by
n readers contributes `n·μ` to downstream conclusions against zero
consumption. ∎

So a conserved quantity in the stamp slot double-counts at every
duplication site — cost is created from nothing. Repairing it would
need a consumption-context-sensitive merge (consumed premises sum, read
premises contribute zero, catalysts contribute zero) and a splitting
(not broadcasting) output rule — but "distinguish consumed from read
from persistent, and split rather than copy" is *precisely the resource
discipline the multiset already implements*. The stamp algebra is the
engine's cartesian value layer; the multiset is its linear value layer;
a conservation axis in the stamp slot puts a linear value in a
cartesian position. This subsumes the C4b/idempotency observation of
the paper's §8.3: idempotent merge is not a *limitation* of the
scheduling dioid, it is the *definition* of the cartesian boundary —
exactly the values for which duplication is semantically free.

(The same separation-of-concerns family as THY_0033 §3's
axis-confounding argument — there "transport is a rule, never a grade
coercion"; here "conservation is a resource/trace concern, never a
grade axis.")

## 4. The factorization: five roles, four existing slots

Every role a usage quantity can play acts at a distinct locus, and
every locus already has a slot:

| role | locus | slot |
|---|---|---|
| accounting ("what did this run cost?") | the trace | **trace measure**: `μ(world) = Σ_fires w(rule, θ)` — a fold over the event multiset (`settleExplore` `opts.leafMeasure`) |
| optimization ("cheapest vs fastest") | the leaf set | **leaf Pareto**: (stamp order) × (ℚ, ≤) dominance over explore leaves — the measure brings its own order, never derived from the stamp join |
| gating ("cannot afford this firing") | enabledness | **linear tokens**: fuel as a resource, counted takes — conservation enforced by linearity itself, where it always lived |
| preference ("among ties, prefer cheap") | tie resolution | **chooser** (semantics-free policy slot, D6) |
| timing feedback ("heavier moves slower") | activation | **term-computed delays**: quantities in matched FACTS feeding `@(T ~ D)` / clause-derived delays — cost visible to matching must be reified in terms, which is again the multiset |

Completeness argument: a residual role would have to affect the run
somewhere other than these five loci; but a firing is fully determined
by (enabledness, match selection, activation order, outputs), each of
which is one of the loci above, and reporting is the trace. There is
nowhere else for a quantity to act.

**Well-definedness and completeness of the measure (where the frontier
theorems become load-bearing):** μ is a function of the world's event
multiset — invariant under the independent-swap reorderings that
realize the same world (L3 preserves the firing multiset), and
chooser-invariant on choice-free programs (the L3/Keller permutation
argument: all maximal runs share the multiset). Under **tied-contention**
(settle-optimality §8.4) the explore leaves are outcome-complete, so
the leaf measures are the measure spectrum of ALL maximal derivations
and the (stamp × measure) Pareto set over leaves is the TRUE frontier.
Executable end-to-end on the fuel-transport domain:
`tests/engine/timed-measure.test.js` — fast (2 time, 5 fuel) vs cheap
(9 time, 1 fuel), tied contention certified (`certifyContention`
`tiedContention: true`), both worlds enumerated, measure answer ≡
fuel-tokens-burned answer leaf by leaf (the translation, executed), and
the stamp-only frontier demonstrably drops the measure-better leaf —
which is exactly why measures live on leaves, not in dominance.

## 5. Existing instances, unified

The engine already had two trace measures before the concept was named:
`settleExplore`'s `pathWeight` (multiplicative — exact woplus branch
weights, feeding the T3 estimator) and will's run mass `Π ρ` (THY_0026;
riding the certificate, not the endsequent). `leafMeasure` is the
additive instance of the same shape and the general slot. They are kept
as separate threads (pathWeight's division semantics is certified
machinery), but the classification is now principled: **measures are
functions of the certified trace; stamps are functions of readiness.**

## 6. What this closes and what it does not

Closes: the paper's §8.3 usage ⟨open⟩ (via §8.5); the question "does the
scheduling dioid need reworking for non-idempotent merge" (no — the
idempotent boundary is definitional); the second-order worry from the
frontier work (measures need no declared second stamp order).

Not claimed: a budgeted scheduler that *prunes* by accumulated cost
(that is gating → tokens, or a search-layer bound over leaf measures —
both expressible today, neither a stamp concern); mechanization of the
broadcast no-go (three lines, rides with the paper's mechanization
⟨open⟩); usage-graded *type systems* (BLL lineage — usage in exponent
grades is static typing, orthogonal to operational stamps, and
consistent with this factorization).
