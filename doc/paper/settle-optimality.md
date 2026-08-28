---
title: "Settle Optimality: Semiring Shortest-Distance under Linear Consumption"
tags: [linear-logic, forward-chaining, till, graded-types, scheduling, confluence, timed-rewriting, soundness]
---

# Settle Optimality — semiring shortest-distance under linear consumption

**Status:** paper stub (markdown master; LaTeX at venue choice). Deliverable of
TODO_0284 Phase T. Supersedes the scoping note in hq research **0138 Part B**
(2026-08-24), which conflated the two side-conditions split in §3. §10 is the
contribution statement of record (TODO_0284 R3); the prior-art evidence base
is **0138 Part A**. The companion till paper is `till/main.tex` (TODO_0270).

**One-line thesis.** Monotone semiring forward-chaining (Dyna, provenance
semirings) treats a derived fact as a reusable *value*, so shortest-distance is
an always-defined least fixed point. Linear logic treats it as a consumable
*token*, coupling the per-fact best-derivation choices by a matching/flow
constraint. We locate the exact boundary: **contention-freedom** makes the
constraint vacuous (the fixed point is realized — Theorem T2), the strictly
weaker **choice-freedom** still forces a unique outcome (confluence — Theorem
T1), and the gap between them is witnessed by a three-line program (E1) that is
deterministic, confluent, and *suboptimal*. Everything is executable: the
engine is `settle` (`lib/engine/timed/timed.js`), the conditions are
machine-checked per algebra (`tests/engine/grade-conformance.test.js`), and
each theorem, boundary, and failure mode below names its test.

Obligations not yet discharged are marked ⟨open⟩ (§11).

---

## 1. The timed rewrite system

### 1.1 Scheduling dioid

A **scheduling dioid** is `(V, ⊔, ⊗, 1̄, ⊑)` where

- `(V, ⊔)` is an idempotent commutative monoid (the *synchronization merge*),
  inducing `a ⊑ b :⇔ a ⊔ b = b`; we assume `⊑` total (so `⊔` = max by `⊑`);
- `(V, ⊗, 1̄)` is a commutative monoid (*sequential composition* — delay/cost),
  `1̄` the `⊑`-least element;
- **(C-infl)** `a ⊑ a ⊗ b` (inflationary — the *delay fence* `δ ⊒ 1̄`);
- **(C-iso)** `a ⊑ b ⟹ a ⊗ c ⊑ b ⊗ c` (isotone).

These are the standard shortest-distance conditions (Mohri 2002, `k = 0`;
Sobrinho 2002: isotonicity ⟺ Dijkstra-optimality) — *cited, not claimed*. In
the engine's GradeAlgebra contract (`doc/documentation/grade-algebra.md`):
`⊗ = compose`, `⊔ = merge` ('join'), `⊑` from `cmp`, and the aggregate `⊕`
(how *alternative* derivations combine) is `class: 'order'` realized as
min-first firing + branch-and-bound pruning. Conditions C1–C5 of the contract
(C1 total order, C2 monotone ⊗, C3 inflationary ⊗, C4 merge = join, C5
termination) are property-checked per instance by the conformance harness.

**Instances.** Time `(ℚ≥0, max, +, 0, ≤)` — `tillGrades`; distance
`(ℚ≥0, max, +, 0, ≤)` — `distGrades`: the *same* dioid under two physical
readings (stamp = availability instant vs accumulated haul cost). That identity
is load-bearing: shortest path needs no operator swap (§8.1).

### 1.2 States, rules, instances

A **state** `s` is a finite multiset `L(s)` of stamped linear tokens
`⟨p, a⟩` (`a ∈ V`) plus a set `P(s)` of *stampless* persistent facts. A
**rule** `r` has linear premises `Λ_r` (consumed), read premises `R_r`
(matched against linear tokens, *not* consumed), persistent goals `Π_r`
(proved against `P(s)` and the theory), stamped conclusions `Θ_r`, a delay
`δ_r ⊒ 1̄` (the fence), and optional `after`/`before` windows.

An **instance** `m` of `r` at `s` assigns `Λ_r` injectively to tokens (its
**cohort** `κ(m)`, respecting counts) and `R_r` to tokens, such that the
unifier and `Π_r` hold and the windows admit it. Its **activation** is

```
a(m)  =  ⊔_{f ∈ κ(m)} stamp(f)  ⊔  ⊔_{g ∈ reads(m)} stamp(g)  ⊔  after-bounds.
```

**Firing** `s —m→ s'` removes `κ(m)` from `L(s)`, adds each `θ ∈ Θ_r` stamped
`a(m) ⊗ δ_r` (its *done* stamp), and adds persistent conclusions to `P`.

`E(s)` is the set of enabled instances, `aMin(s) = ⊑-min a(E(s))`,
`Tied(s) = { m ∈ E(s) : a(m) = aMin(s) }`.

**settle(s, H).** While `E(s) ≠ ∅` and `aMin(s) ⊑ H`: pick `m ∈ Tied(s)` by
the PRF chooser and fire it. The engine realization — dirty-rule min-heap,
FIFO enumeration order inside `tryTimedMatch`, Zeno guard, cohort/batch firing
(state-identical to sequential, TODO_0278 B1) — implements, and does not
alter, this model.

### 1.3 Hypothesis S (static knowledge)

> **(S)** No rule fired below `H` has a persistent conclusion that makes a
> goal in `Π` of some other instance provable.

Sufficient syntactic check: timed rules have no `!`-conclusions (persistent
knowledge is loaded, or derived timelessly by the backward theory, not
produced mid-settle). The engine *does* permit persistent conclusions
(`producePers`, `timed.js` fire()), and without S frontier monotonicity (L2)
genuinely fails: a stampless fact learned at frontier `t` can enable an
instance whose cohort is older than `t` — its activation `⊏ t`, and the event
sequence regresses ("learned knowledge backdates enablement"). The audit-era
note missed this hypothesis. A static lint is ⟨open⟩ (§11).

---

## 2. Per-firing optimality and the frontier

**Lemma L1 (per-firing optimality).** For each rule `r` and state `s`,
`tryTimedMatch` returns an instance minimizing `a(m)` over instances of `r`,
and among minimizers the first in cohort-enumeration order (FIFO).

*Proof.* The assignment space is finite. The search accumulates the partial
activation as the `⊔` of the tokens chosen so far; since `x ⊑ x ⊔ y`
definitionally, `a` is nondecreasing along any completion, and `after`-windows
only `⊔`-join further. Hence the branch-and-bound cut — abandon a partial
whose activation already satisfies `prunes(partial, best) ⇔ partial ⊒ best`
— never discards an assignment whose leaf would *strictly* improve `best`;
`before`-windows only reject leaves, which cannot improve `best` either. The
un-pruned search is exhaustive, so the final `best` is the minimum. FIFO: the
leaf accepts on strict `<` only, so the first minimizer found is kept, and the
prune's `⊒` (not `⊐`) never explores an assignment the leaf would reject —
the invariant pair (`timed.js` `search`/`leaf`, pinned by the till
equal-activation tie tests). ∎

**Lemma L2 (frontier monotonicity).** Under S, the activations of the
instances `settle` fires form a `⊑`-nondecreasing sequence.

*Proof.* Suppose `settle` fires `m` at `t = aMin(s)`. Consider any
`m' ∈ E(s')`. If `m' ∈ E(s)`, then `a(m') ⊒ t` by minimality of `t`, and
`a(m')` is unchanged: an instance is a fixed token assignment, so it survives
only if `m` consumed none of its tokens, leaving its activation intact. If
`m' ∉ E(s)`, its enablement changed, which under S can only be because it
matches at least one token produced by `m` (consumption never enables;
`after`-windows are state-independent; `before`-windows only disable;
persistent enablement is excluded by S). Every produced token has stamp
`t ⊗ δ_r ⊒ t` by C-infl, and stamps enter `a(m')` via `⊔`, so `a(m') ⊒ t`.
Hence `aMin(s') ⊒ t`. ∎

L1 + L2 are the operational content of Dijkstra's algorithm over the dioid —
this much is Mohri/Sobrinho, cited not claimed. The theorem content is what
survives *consumption*.

---

## 3. The two side-conditions (and the gap between them)

**Definition (independence).** Two instances `m₁, m₂ ∈ E(s)` are
**independent**, `m₁ ⌣ m₂`, iff

1. **disjoint cohorts:** the combined take of `κ(m₁)` and `κ(m₂)` is
   available in `L(s)` (per-token: take₁ + take₂ ≤ count);
2. **no read-starvation:** neither's consumption reduces a token count below
   the other's read demand, and neither *changes* a quantity the other's
   match binds — in particular a whole-bind `!_W A` binds the current total,
   so *any* co-instant consumption or arrival on `A` breaks independence
   with it (the `!_W`-trim starvation gotcha, PP2 §3b);
3. **no instant-feeding:** no same-instant conclusion of one (`δ = 1̄`)
   unifies into a premise or window of the other.

This is behavioral **persistence** in the Petri-net sense (Keller 1975;
Landweber–Robertson 1978), lifted to stamped multiset rewriting.

**Definition (choice-freedom below H).** At every state reachable by `settle`
below `H` (including mid-instant states), all pairs in `Tied(s)` are
independent.

**Definition (contention-freedom below H).** At every state reachable by
`settle` below `H`, **all pairs of enabled instances** are independent.

**Correction (vs 0138 Part B).** The scoping note defined one condition
("H-persistent", tied pairs only) and used it for both theorems. That is too
weak for optimality: consumption across *different* activation levels never
produces a tie, so choice-freedom does not see it — yet it destroys
derivations (E1 below). The split is: choice-freedom ⟹ T1 (confluence);
contention-freedom ⟹ T2 (optimality); and contention-freedom ⟹
choice-freedom trivially (tied pairs are enabled pairs).

**Hierarchy.**

```
structural conflict-freedom  ⟹  contention-freedom  ⟹  choice-freedom
     (syntactic, static)           (behavioral)           (behavioral)
```

*Structural conflict-freedom*: no two rule instances can ever demand the same
token — each linear predicate is consumed by at most one rule, matched at most
once per firing, with reads unrestricted (the *one-shot-edge discipline*,
§8.1). Both inclusions are strict: a program whose sharing rules are never
co-enabled is contention-free but not structural; and **E1** separates the
behavioral pair:

**Example E1 (choice-free, contended, suboptimal) —**
`calculus/gill/tests/forward/contention.gill`, executable:

```
r1: a * tok -o { won_a }.
r2: b * tok -o { won_b }.        % initial: a@0, tok@0, b@5
```

`r1`'s instance activates at `0`, `r2`'s at `5` — never tied, so the run is
deterministic (the PRF chooser is never consulted) and trivially confluent.
`settle` fires `r1` at the frontier `0`, consumes `tok`, and `r2` starves
forever. The monotone relaxation derives `won_b@5`; the run does not. T1
holds; T2's hypothesis and conclusion both fail. The spec's twin program
(`read rtok` instead of consuming) is contention-free and realizes both
relaxation stamps — the recovery of §5.

**Lemma L3 (diamond).** If `m₁ ⌣ m₂` at `s`, then `s —m₁→ · —m₂→ t` and
`s —m₂→ · —m₁→ t'` with `t = t'`.

*Proof.* By (1) each cohort is intact after the other fires; by (2) read
demands and bound quantities are undisturbed, so both remain enabled *as the
same instances*; by (3) neither's activation gains a term from the other's
outputs, so each fires at its original `a(m)` and produces identically
stamped conclusions. Multiset removals with available combined take commute,
additions commute, persistent-set unions commute. ∎

**Lemma L4 (enabledness preservation).** In a contention-free program, if
`m ∈ E(s)` and `settle` fires `m' ≠ m`, then `m ∈ E(s')` with `a(m)`
unchanged. *Proof.* Immediate from independence clauses (1)–(3) applied to
the pair `{m, m'}`. ∎

---

## 4. Theorem T1 — confluence under choice-freedom

**Theorem T1.** For a choice-free (below `H`), `H`-terminating program
satisfying S, the final state of `settle(s, H)` is independent of the PRF
chooser: all maximal firing sequences reach the same state.

*Proof.* By L2 the frontier never regresses, and at each step `settle` fires
some member of `Tied(s)` — the only nondeterminism is the within-tie choice.
Every reachable peak is therefore a pair of tied instances, independent by
choice-freedom, and L3 closes it (one-step local confluence). `H`-termination
(§7) makes the firing relation terminating, so Newman's Lemma lifts local to
global confluence; a terminating, confluent relation has unique normal forms. ∎

*Attribution.* T1 is the timed/graded lift of **Keller's theorem** (1975):
determinism + commutativity + persistence ⟹ Church–Rosser. L1/L2 supply
determinism-with-forced-order, L3 the commutation, choice-freedom the (tied
fragment of) persistence. No novelty is claimed for the confluence *shape*;
T1 is stated because it is the hypothesis under which T2 becomes a statement
about *the* outcome. Weighted rules (`woplus`) are excluded: their branch
draw is nondeterministic by design (sampled, TODO_0278 A3a).

---

## 5. Theorem T2 — optimality under contention-freedom

### 5.1 The monotone relaxation

The **relaxation** of a program is the same rule set executed with
consumption disabled: firing does not remove `κ(m)` (every token is a
reusable value; equivalently, all linear premises become reads). Each
relaxation instance fires at most once (an instance is a fixed token
assignment). Over the relaxation's derivation hypergraph the **stamping
system** is

```
σ(f)  =  ⊕_{(r,m) producing f}  [ (⊔_{g ∈ inputs(m)} σ(g)) ⊗ δ_r ]      (★)
```

with `⊕ = ⊑-min`. Under C-infl/C-iso, Kleene iteration converges to the
`⊑`-least fixed point `σ*` — the algebraic shortest-distance / critical-path
equation (Mohri 2002; PERT: Baccelli et al. 1992 for `(max,+)`).

### 5.2 Adequacy and the theorem

**Lemma L5 (relaxation adequacy).** For a contention-free (below `H`),
`H`-terminating program satisfying S, the set of firings `settle` performs
below `H` equals the set of relaxation firings with activation `⊑ H`, with
identical activations and done-stamps.

*Proof sketch.* (⊆) A run firing is a relaxation firing verbatim: the
relaxation's states dominate the run's (nothing is ever removed), so every
run-enabled instance is relaxation-enabled with the same activation (its
input tokens exist with the same stamps, by induction on the firing
sequence). (⊇) Induction on the relaxation's frontier order. Let `m` be a
relaxation firing with `a(m) ⊑ H`; by induction every token in
`κ(m) ∪ reads(m)` is produced by the run with its relaxation stamp (or is
initial). At the point the last of them is produced, `m` is enabled in the
run — *enabled as an instance of the linear system*, because
contention-freedom guarantees no earlier run firing consumed any of them
(a consumer of `m`'s inputs co-enabled with `m`'s producers or with `m`
would violate independence clause (1)/(2) at a reachable state). By L4, `m`
stays enabled with unchanged activation until fired; `settle` exits only at
quiescence or when `aMin ⊐ H`, and `a(m) ⊑ H`, so `H`-termination forces
`m` to fire, at exactly `a(m)`. ∎ ⟨open: mechanize the double induction⟩

**Theorem T2 (settle computes σ*).** Under the hypotheses of L5, `settle`
produces exactly the relaxation's tokens with stamps `⊑ H`, each at its
`σ*` value; in particular, for every predicate `p` derivable in the
relaxation with `σ*(p) ⊑ H`, the run's `⊑`-least token of `p` carries
exactly `σ*(p)`.

*Proof.* By L5 the run and the relaxation perform the same firings with the
same stamps; the relaxation's realized stamps are the unique solution of the
dataflow equations on its (deduplicated) derivation hypergraph, i.e. `σ*`
restricted to `⊑ H`, by C-iso and induction along L2's nondecreasing frontier
(the standard Dijkstra invariant: when the frontier passes `t`, every
derivation with value `⊑ t` has been realized, and no token was ever produced
below its `σ*` — soundness because every run derivation *is* a relaxation
derivation). ∎

**Corollary (Dyna / provenance recovery).** A program whose rules only read
and never consume (equivalently: all-persistent) is contention-free by
construction, so `settle` on it *is* the Dijkstra-agenda semiring
shortest-distance evaluation of Dyna / provenance-semiring Datalog (Green et
al. 2007; Eisner–Filardo 2020). The novelty budget is spent entirely on what
happens when consumption is switched on.

---

## 6. The dichotomy, and how real programs decompose

**Proposition P1 (beyond contention-freedom).** If a program is not
contention-free below `H`, some reachable state has enabled instances
`m₁ ⌣̸ m₂` sharing demand. Then the relaxation's `σ*` need not be realized
(E1), and distinct firing orders can reach `⊑`-incomparable final states
(Pareto-incomparable under a product grade). `settle` realizes exactly one —
the PRF-committed, locally-greedy world (still chooser-independent if the
program is choice-free, E1) — and `settleExplore` enumerates the reachable
set. A precise Pareto-frontier characterization is ⟨open⟩ (product
scheduler, 0285 P6).

**The reframing** (the paper's central claim): monotone semiring
forward-chaining solves a *fixed point*; linear forward-chaining solves a
fixed point *coupled with a matching problem* (which derivations get the
tokens). Contention-freedom is precisely the vacuity of the matching
constraint. Beyond it, "the optimal schedule" is a set, not a value.

**Layered reading of real programs.** A useful program is rarely
contention-free end-to-end; it decomposes:

- a **derivation core** that is contention-free (often structurally
  conflict-free) — T2 applies, stamps are `σ*`;
- **competitive harvest** steps that deliberately consume from alternatives
  — T2 does not apply, but L1 does: the harvester fires with the `⊑`-least
  available cohort;
- genuinely **contended** parts — the dichotomy (P1).

The acceptance example `calculus/gill/tests/forward/depot.gill` is exactly
this decomposition: the hop rules (read-marked positions, one-shot road
tokens, cost as delay) are the structurally conflict-free core, so arrival
stamps are the exact shortest-path distances — property-tested against an
independent exact-rational Dijkstra on random graphs
(`tests/engine/gill-dist.test.js`); `deliver` is a harvest step — it consumes
`good` and the `⊑`-least `depot_reached` cohort (6, not 7) by L1 alone.

---

## 7. Termination

`H`-termination — `settle` reaches quiescence or `aMin ⊐ H` in finitely many
firings — was operationally enforced (Zeno guard + horizon) but not
characterized. The following discharges the obligation with an honest
sufficient condition.

**Proposition (H-termination).** Suppose the program is finite and:

1. **(lattice delays)** all initial stamps and all ground delay values that
   occur in any firing lie in `(1/D)·ℕ` for a fixed `D` — which holds
   whenever delays are built from the finitely many rational constants of
   the program and input by `+`, `max`, `min`, and fenced monus `⊖` (a
   common denominator exists and is preserved; *division escapes it*);
2. **(instant acyclicity)** the zero-delay feed graph on predicates — edge
   `p → q` when some rule with `δ = 1̄` consumes `p` and concludes `q` at
   the same instant — is acyclic;
3. **(instant consumption)** every rule with `δ = 1̄` consumes at least one
   linear token.

Then `settle(s, H)` terminates for every horizon `H`.

*Proof.* By (1), all activations and done-stamps lie in `(1/D)·ℕ` (closed
under `max` and `+`), which is well-ordered; at most `⌈H·D⌉ + 1` distinct
frontier values fit below `H`, and by L2 the frontier visits them
nondecreasingly. Within one instant, assign each predicate its height in the
acyclic feed graph (2); a zero-delay firing removes, by (3), at least one
token of some height `h` and adds same-instant tokens only of heights `< h`
— positive-delay conclusions belong to later frontier values and do not
enter the instant's measure. The multiset of heights of same-instant tokens
therefore strictly decreases in the Dershowitz–Manna multiset order, which
is well-founded, so each instant fires finitely often. Finitely many
instants × finite instants = termination. ∎

**Hypotheses ↔ engine guards.** Violating (2)/(3) is *instant Zeno* — a
zero-delay cycle pinning logical time — caught loudly by `maxInstantSteps`
(D16). Violating (1) — e.g. a rule computing its next delay by *division* —
permits *accumulation Zeno*: infinitely many distinct instants below a finite
horizon, which no default guard detects (only the opt-in `maxSteps` cap).
The proposition is the clean condition those guards approximate
operationally; conditions (2)–(3) are statically checkable, and (1) is
implied by the syntactic absence of division in delay positions. C5 of the
conformance contract records the per-algebra half (a well-ordered reachable-
stamp bound); this proposition is the per-program half.

---

## 8. Instantiation

### 8.1 Time and distance — one dioid, two readings

`tillGrades` (time) and `distGrades` (distance) are the *same* scheduling
dioid `(ℚ≥0, max, +, 0, ≤)`; C1–C5 are machine-checked for both by
`tests/engine/grade-conformance.test.js` (exact BigInt rationals; the
`merge`/`prunes` slots declared symbolically as `'join'`/`'geq'` and id-lifted
by the StampTable). Under the time reading, T2 says: stamps are
earliest-availability — the critical-path least fixed point. Under the
distance reading: stamps are shortest-path distance — Dijkstra. The
modelling discipline that puts a graph program inside T2's hypotheses (the
one-shot-edge discipline) is: positions are **read** (measured, never
consumed, original stamp — both routes race without competition), each edge
is a **one-shot linear token** consumed by exactly one rule (structural
conflict-freedom + termination), and the segment cost is the **rule delay**.
`$`-preservation is *wrong* here: it re-produces the position at the firing's
done-stamp, which both re-stamps (breaking the original-stamp requirement)
and serializes conflicting hops through committed choice.

### 8.2 Executable evidence

| claim | witness |
|---|---|
| C1–C5 for time/distance (and their coherence with the hash face) | `tests/engine/grade-conformance.test.js` |
| L1's FIFO invariant pair (prune `⊒` / leaf `<`) | till equal-activation tie tests (till-eat, till-fifo-pair) |
| T2 on the conflict-free fragment ≡ exact Dijkstra | `tests/engine/gill-dist.test.js` (random graphs, exact rationals) |
| the layered decomposition (core + harvest) | `calculus/gill/tests/forward/depot.gill` |
| T1 ⇏ T2 (choice-free, contended, suboptimal) | `calculus/gill/tests/forward/contention.gill` (E1) |
| read-relaxation recovers `σ*` (Dyna corollary) | `contention.gill` twin program |
| the measure-class fence (§8.3) | `tests/engine/gill-weight.test.js` |

### 8.3 Where the conditions fail (each failure has a shipped fence or witness)

- **Non-idempotent ⊕ (measure class).** `weightGrades` (ℚ≥0 masses, ⊗ = ·,
  ⊕ = +) is not a scheduling dioid at all: aggregation sums alternatives, so
  *any* pruning discards mass (M1, THY_0026). `buildTimedConfig` rejects it
  at the class fence — before asking for scheduler faces it must never carry.
  Measure aggregation is an execution mode (will / TODO_0292), not a
  scheduler policy.
- **Non-inflationary ⊗.** Masses `< 1` shrink under composition, so C-infl
  fails and the B&B cut of L1 would be unsound — same fence, same reason
  stated differently.
- **Non-idempotent ⊔ (usage).** A consumption merge `⊔ = +` breaks C4
  (merge is no longer the order's join), so L1's "activation nondecreasing
  along completions" argument needs re-proving; the StampTable executes such
  slots correctly (value-level function slots, running even at equal ids),
  but *scheduling* over a usage axis is unproven — ⟨open⟩.
- **Contention (independence clause 1).** E1. The general dichotomy (§6).
- **Read-starvation (clause 2).** A whole-bind `!_W A` binds the total, so
  its instance is disturbed by any co-instant arrival or take on `A`; a trim
  rule written with `!_W` can starve forever under a deterministic chooser
  (PP2 §3b). The starvation-free form is a counted take (`!_201 g -o
  { !_200 g }`) — which restores independence by demanding a fixed cohort.
- **Instant-feeding (clause 3).** Zero-delay production into a co-tied
  instance's premises orders the tie causally; the settle loop detects this
  (`_feedsInstant`) as tie-sensitivity for acceleration.
- **Hypothesis S.** A timed rule with a `!`-conclusion can backdate
  enablement (§1.3): frontier regression, outside L2. Static lint ⟨open⟩.

---

## 9. The `(max,+)` clarification (a referee will ask)

`(max,+)` longest-path is NP-hard and its closure diverges on positive
cycles — but till never *maximizes* path length. The objective is the
`⊑`-least completion (outer `⊕ = min`, a *min-first* frontier); `max` is the
within-derivation synchronization `⊔`, never the objective. `(★)` with these
roles is the PERT/critical-path least fixed point, well-defined precisely
because delays sit above the unit (C-infl — the engine's delay fence *is*
the inflationary condition). No contradiction: the NP-hard problem has `max`
as the aggregation `⊕` on cyclic graphs, a different seat at the table.

---

## 10. Contributions (the statement of record — TODO_0284 R3)

This section is the canonical contribution statement; hq research 0138
Part A is the evidence base (six blind literature agents + an engine-source
audit, 2026-08-24).

### 10.1 The novelty axis

Distinguish three uses of a grade; only the third is claimed:

- **(a) grade = static typecheck artifact, then erased.** Granule
  (Orchard–Liepelt–Eades 2019), QTT (Atkey 2018; McBride 2016), Idris 2,
  Linear Haskell. The grade never runs. Prior art.
- **(b) grade drives compile-time synthesis or scheduling.** Ghica–Smith
  2014 (semiring grade → fixed hardware schedule at synthesis time);
  Hughes–Orchard 2024 (grades as static SMT-discharged pruning in term
  synthesis). Prior art.
- **(c) grade = live runtime quantity driving dynamic resource resolution
  and an optimal schedule of an actual execution.** No prior system found
  occupies this — in particular none combines *graded*, *linear/consuming*,
  *optimal*, and *executable* (0138 Part A §1–2).

### 10.2 Claimed

1. **The boundary theorem pair.** The **choice-freedom / contention-freedom
   split** (§3): two behavioral side-conditions with distinct theorems —
   T1 (confluence: the committed world is chooser-independent) under the
   weaker, T2 (optimality: realized stamps = the semiring least fixed point
   `σ*`) under the stronger — separated by an executable three-line witness
   (E1) that is deterministic, confluent, and suboptimal. This locates
   *exactly* where semiring shortest-distance survives linear consumption.
2. **The reframing.** Monotone semiring forward-chaining solves a fixed
   point; linear forward-chaining solves a fixed point **coupled with a
   matching problem** (which derivations get the tokens). Contention-freedom
   is precisely the vacuity of the matching constraint; the persistent/read
   limit degenerates back to Dyna/provenance evaluation (T2's corollary);
   the layered decomposition (§6) makes the reframing an engineering
   discipline, not just a theorem scope.
3. **The executable, pluggable realization.** `settle` as an operational
   semiring shortest-distance engine over a *declared* grade algebra:
   per-firing optimality and frontier monotonicity held unconditionally
   (L1; L2 under S), `σ*` on the contention-free fragment, one committed
   world beyond it with `settleExplore` as the enumerator — with every
   algebraic condition machine-checked per instance (C1–C5 harness) and
   every out-of-scope algebra loudly fenced rather than silently mis-run.
   The aggregation `⊕` is **routed as a policy** `(⊕, realization)`: order
   class realized by min-frontier + B&B prune (this paper), measure class
   (`⊕ = +`) realized by exact mass-sum or unbiased PRF sampling — the
   semiring-DP lineage of Goodman 1999 (semiring parsing), Eisner 2002
   (expectation semirings), and Huang 2008 (semiring/hypergraph dynamic
   programming), executed by the companion calculus `will` (THY_0026
   T1/T3; TODO_0292). One scheduler-correctness story, two condition
   families.

Companion (claimed in the till paper, not here): the delay-graded lax monad
`{A}@d` as an *operational* `(max,+)` scheduler, with the `(min,+)`
transport comonad `!!_d` as its spatial dual (TODO_0270; `till/main.tex`).

### 10.3 Not claimed

The dioid optimality conditions (Mohri 2002; Sobrinho 2002; Höfner–Möller
2012); `(max,+)`/`(min,+)` scheduling algebra and critical-path fixed
points (Baccelli et al. 1992); persistence ⟹ Church–Rosser (Keller 1975;
Landweber–Robertson 1978; Newman 1942); semiring-weighted *monotone*
forward-chaining and its Dijkstra agendas (Dyna; provenance semirings);
semiring parsing / expectation semirings / hypergraph DP (Goodman; Eisner;
Huang); graded modal type systems as static artifacts (Granule, QTT);
linear forward-chaining engines as such (Ceptre, LolliMon, Celf/CLF).

### 10.4 The three collisions, pre-empted

**"Isn't this Dyna / provenance semirings?"** Those systems are monotone:
facts are values, never consumed, which is exactly what makes their
semiring compositionality and Dijkstra-agenda optimality unconditional. We
are the linear generalization: consumption couples the per-fact choices
(claim 2), the unconditional theorem provably fails (E1 — a fact that is
*derivable but never derived* because its token was spent, a phenomenon
inexpressible in monotone Datalog), and we characterize the exact boundary
(contention-freedom) at which the monotone theory is recovered verbatim.

**"Isn't this graded LL / SELL / Bounded LL?"** Their `!^r` is an
*exponential* graded by a usage semiring, or a subexponential indexed by a
*preorder* — no run-time arithmetic on grades, no synchronization rule, and
the grade lives only in the static derivation. Ours is a graded *lax monad*
(different proof theory: the `⊖`-residual left rule, the `⊔`-join of
co-consumed grades as logical content) whose grade is a live scheduling
quantity — the engine computes `max`/`+`/`−` on it at every firing and lets
it *select* the firing order.

**"Isn't the cost story Simmons–Pfenning?"** Linear Logical Algorithms
assigns a cost semantics to LL forward-chaining *a posteriori* — it
measures derivations to state complexity bounds. Here the grade *guides*
the search: the B&B prune and min-activation frontier are the `⊕`
realization, and under committed choice they change *which world is
reached*, not merely its measured cost. E1 again is the observable: a cost
semantics would report the starved world's cost; a grade-driven scheduler
*produced* that world.

### 10.5 Venues

Theory: FSCD / CSL / substructural workshops (LINEARITY, TYPES) — the
T1/T2 split with the mechanization (§11) as the spine. Systems: a
tool/experience track with Ceptre as precedent, differentiator = the
graded/optimal-scheduling runtime. The measure-class companion (will)
strengthens a combined submission: one parametrized scheduler, two
realized condition families.

---

## 11. Open obligations

- ⟨open⟩ **Mechanization.** L3 + T1 (Newman) are small and POR-shaped; L5's
  double induction is the real target. Machine-checked clause split = the
  paper's spine.
- ⟨open⟩ **Pareto characterization** of the contended case (P1) — needs the
  product-scheduler / stamp-vector model (0285 P6).
- ⟨open⟩ **Static analyzers.** Three syntactic conservative checks fall out
  of §3/§1.3: (a) unifiable-linear-premise overlap across rules (structural
  conflict-freedom ⟹ contention-freedom); (b) whole-bind co-instant
  activity (clause 2); (c) `!`-conclusions in timed rules (Hypothesis S).
  Each would let the engine *certify* T1/T2 applicability per program.
- ⟨open⟩ **Usage-axis scheduling** (non-idempotent ⊔) — C4 fails; what
  replaces L1's monotone-completion argument?
- ✔ **Termination** — discharged as §7's proposition (lattice delays +
  instant acyclicity + instant consumption); remaining only necessity /
  decidability refinements.

---

## 12. Citations

Mohri, "Semiring Frameworks and Algorithms for Shortest-Distance Problems,"
JALC 7(3), 2002. Sobrinho, "Algebra and algorithms for QoS path computation
and hop-by-hop routing," IEEE/ACM ToN 10(4), 2002. Höfner–Möller, "Dijkstra,
Floyd and Warshall Meet Kleene," FAC 24, 2012. Baccelli–Cohen–Olsder–Quadrat,
*Synchronization and Linearity*, Wiley 1992. Keller, "A Fundamental Theorem
of Asynchronous Parallel Computation," LNCS 24, 1975. Landweber–Robertson,
"Properties of Conflict-Free and Persistent Petri Nets," JACM 25(3), 1978.
Newman, Ann. Math. 43, 1942. Dershowitz–Manna, "Proving Termination with
Multiset Orderings," CACM 22(8), 1979. Green–Karvounarakis–Tannen,
"Provenance Semirings," PODS 2007. Eisner–Filardo, "Dyna," Datalog 2.0,
2020. Petricek–Orchard–Mycroft, "Coeffects," ICALP 2013. Gaboardi et al.,
"Combining Effects and Coeffects via Grading," ICFP 2016. Barbarossa–
Pistone, "Tropical Mathematics and the Lambda-Calculus I," CSL 2024. Martens,
"Ceptre," AIIDE 2015. Simmons–Pfenning, "Linear Logical Algorithms," ICALP
2008. Nigam–Olarte–Pimentel, subexponential LL, TCS 2017. Kamide, TCS 353,
2006. Kanovich–Ito, "Temporal Linear Logic Specifications for Concurrent
Processes," LICS 1997. Orchard–Liepelt–Eades, "Granule," ICFP 2019. Atkey,
"Syntax and Semantics of Quantitative Type Theory," LICS 2018. Ghica–Smith,
"Bounded Linear Types in a Resource Semiring," ESOP 2014. Hughes–Orchard,
"Program Synthesis from Graded Types," ESOP 2024. Goodman, "Semiring
Parsing," Computational Linguistics 25(4), 1999. Eisner, "Parameter
Estimation for Probabilistic Finite-State Transducers," ACL 2002
(expectation semirings; also Li–Eisner, EMNLP 2009). Huang, "Advanced
Dynamic Programming in Semiring and Hypergraph Frameworks," COLING 2008.
