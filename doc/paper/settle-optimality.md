---
title: "Settle Optimality: Semiring Shortest-Distance under Linear Consumption"
tags: [linear-logic, forward-chaining, till, graded-types, scheduling, confluence, timed-rewriting, soundness]
---

# Settle Optimality — semiring shortest-distance under linear consumption

**Status:** complete draft (markdown master; LaTeX at venue choice). Deliverable
of TODO_0284 Phase T; focused presentation §5.3 per TODO_0293; product
instance §8.4 per TODO_0285 P6; focused-frontier gap resolved (§8.4:
witness W-gap + tied-contention adequacy, 2026-09-07). Supersedes the scoping note in hq research **0138 Part B**
(2026-08-24), which conflated the two side-conditions split in §3. §10 is the
contribution statement of record (TODO_0284 R3); the prior-art evidence base
is **0138 Part A**. The companion till paper is `till/main.tex` (TODO_0270).

**One-line thesis.** Monotone semiring forward-chaining (Dyna, provenance
semirings) treats a derived fact as a reusable *value*, so shortest-distance is
an always-defined least fixed point. Linear logic treats it as a consumable
*token*, coupling the per-fact best-derivation choices by a matching/flow
constraint. We locate the exact boundary: **contention-freedom** — a condition
on the program's *monotone relaxation*, hence statically analyzable — makes the
constraint vacuous (the fixed point is realized — Theorem T2), the strictly
weaker **choice-freedom** still forces a unique outcome (confluence — Theorem
T1), and the gap between them is witnessed by a three-line program (E1) that is
deterministic, confluent, and *suboptimal* — with a deferred-producer twin (E2)
showing why the condition must live on the relaxation, not on run states. The
theorem pair carries an Andreoli-shaped packaging (§5.3): committed
min-activation firing is a *temporally focused* restriction of forward
derivation — sound by inclusion, complete exactly on the contention-free
fragment — and there settle's stamps are the *principal grades* of the timed
sequent judgment, so the scheduler is a canonical-form normalizer, not an
extra-logical policy.
Everything is executable: the engine is `settle`
(`lib/engine/timed/timed.js`), the algebraic conditions C1–C4 and M1–M3 are
machine-checked per algebra (`tests/engine/grade-conformance.test.js`; C5 is
operational — §7), and each theorem, boundary, and failure mode below names
its test.

Obligations not yet discharged are marked ⟨open⟩ (§11).

---

## 1. The timed rewrite system

### 1.1 Scheduling dioid

A **scheduling dioid** is `(V, ⊔, ⊗, 1̄, ⊑)` where

- `(V, ⊔)` is an idempotent commutative monoid (the *synchronization merge*),
  inducing `a ⊑ b :⇔ a ⊔ b = b`; we assume `⊑` total (so `⊔` = max by `⊑`) —
  §8.4 relaxes exactly this coincidence for the product instance;
- `(V, ⊗, 1̄)` is a commutative monoid (*sequential composition* — delay/cost),
  `1̄` the `⊑`-least element;
- **(C-infl)** `a ⊑ a ⊗ b` (inflationary — the *delay fence* `δ ⊒ 1̄`);
- **(C-iso)** `a ⊑ b ⟹ a ⊗ c ⊑ b ⊗ c` (isotone).

These are the standard shortest-distance conditions (Mohri 2002, `k = 0`;
Sobrinho 2002: isotonicity ⟺ Dijkstra-optimality) — *cited, not claimed*. In
the engine's GradeAlgebra contract (`doc/documentation/grade-algebra.md`):
`⊗ = compose`, `⊔ = merge` ('join'), `⊑` from `cmp`, and the aggregate `⊕`
(how *alternative* derivations combine) is `class: 'order'` realized as
min-first firing + branch-and-bound pruning. Conditions C1–C4 of the contract
(C1 total order, C2 monotone ⊗, C3 inflationary ⊗, C4 merge = join) are
property-checked per instance by the conformance harness; C5 (termination) is
deliberately *not* property-testable — the harness records it as an
operational condition (Zeno guard + horizon, pinned by the till suite), and
§7 characterizes it analytically.

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

Sufficient syntactic check: no rule that `settle` can fire — static or
possessed loli — has a `!`-conclusion, *except* external-choice menus
`!(… & …)`, which are exempt: `settle` never auto-fires a `&`-projection
(the choice is external — only an interactive cut turns a branch into a
rule, and the cut order then carries its own stamp), so a menu conclusion
never puts an instance into `E(s)` and cannot backdate one. The engine
*does* permit persistent conclusions (`producePers`, `timed.js` fire()),
and without S frontier monotonicity (L2) genuinely fails: a stampless fact
learned at frontier `t` can enable an instance whose cohort is older than
`t` — its activation `⊏ t`, and the event sequence regresses ("learned
knowledge backdates enablement"). The audit-era note missed this
hypothesis. The static lint ships as the C2 advisory (§11).

**Corpus status (machine-checked — the C2 advisory).** `depot.gill` and
`contention.gill` have no `!`-conclusions at all. `PP2.till`'s only
`!`-conclusions are unlock menus (the barracks army menu) — covered by the
menu exemption. The shipped timed corpus therefore satisfies S.

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

**Lemma L2 (frontier monotonicity).** Under S, for a program without
whole-bind (`!_W`) premises — or, with them, for a choice-free program — the
activations of the instances `settle` fires form a `⊑`-nondecreasing
sequence.

*Proof.* Suppose `settle` fires `m` at `t = aMin(s)`. Consider any
`m' ∈ E(s')`. If `m' ∈ E(s)`, then `a(m') ⊒ t` by minimality of `t`, and
`a(m')` is unchanged: an instance is a fixed token assignment, so it survives
only if `m` consumed none of its tokens, leaving its activation intact. If
`m' ∉ E(s)`, its enablement changed. Consumption never *lowers* a rule's
least enabling activation for ordinary premises: the enabled instance per
rule is the `⊑`-minimum over token assignments (L1), and removing tokens
shrinks the assignment space, so per-rule minima only rise. A **whole-bind**
premise `!_W A` is the exception — its activation is a *forced join* over
the current total, not a minimum over choices, so consuming a cohort can
lower it. But a regression through whole-bind re-formation is self-excluding
under choice-freedom: if the re-formed instance has activation `a' ⊏ t`,
then before the firing its activation was `⊔(a', shared stamps ⊑ t) = t`
exactly (it is `⊒ t` by minimality of `t` and `⊑ t` since every joined
stamp is), so it was *tied* with `m` — a dependent tie (`m` consumes from
the whole-bound predicate, independence clause 2), contradicting
choice-freedom; without whole-bind premises the case is void. The remaining
way to enter `E(s')` is matching a token produced by `m` (`after`-windows
are state-independent; `before`-windows only disable; persistent enablement
is excluded by S — the menu exemption adds nothing to `E`). Every produced
token has stamp `t ⊗ δ_r ⊒ t` by C-infl (C3), and stamps enter `a(m')` via
`⊔` (C4), so `a(m') ⊒ t`. Hence `aMin(s') ⊒ t`. ∎

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

**Definition (contention-freedom below H).** **All pairs of distinct firings
of the program's monotone relaxation** (§5.1) with activations `⊑ H` are
independent — clauses (1)–(3) evaluated against the relaxation's states,
which dominate every run state.

**Why the relaxation, and not run states (E2).** Quantifying over
run-reachable enabled pairs is too weak: defer the competitor's enabling
token and no two instances are ever co-enabled in the run — the run-state
condition holds *vacuously* — yet the shared token is still spent before the
competitor ever becomes enabled. Executably
(`calculus/gill/tests/forward/contention.gill`, E2): add `mk: c -o { b }` to
E1 below and start from `a@0, tok@0, c@5` — every reachable `E(s)` is a
singleton, yet `won_b@5` is starved exactly as in E1. The demand overlap is
visible only in the relaxation, where both firings exist. As a bonus, the
relaxation-level condition is *statically analyzable*: the relaxation's
firing set is a monotone least fixed point, independent of scheduling.

**Correction (vs 0138 Part B).** The scoping note defined one condition
("H-persistent", tied pairs only) and used it for both theorems. That is too
weak for optimality twice over: consumption across *different* activation
levels never produces a tie, so choice-freedom does not see it (E1) — and
even all-enabled-pairs quantification over run states misses demand from
instances that never co-exist in the run (E2). The split is: choice-freedom
⟹ T1 (confluence); contention-freedom (on the relaxation) ⟹ T2
(optimality); and contention-freedom ⟹ choice-freedom (below): every
run-enabled instance is a relaxation firing, so tied run pairs are
independent relaxation pairs.

**Hierarchy.**

```
structural conflict-freedom  ⟹  contention-freedom   ⟹  choice-freedom
     (syntactic, static)        (on the relaxation,       (behavioral,
                                 statically analyzable)    on the run)
```

*Structural conflict-freedom*: no two rule instances can ever demand the same
token — each linear predicate is consumed by at most one rule, matched at most
once per firing, with reads unrestricted (the *one-shot-edge discipline*,
§8.1). Both inclusions are strict: two rules may share a consumed predicate
(not structural) while the relaxation only ever fires one of them — demand
never overlaps (contention-free); and **E1** separates the second pair:

**Example E1 (choice-free, contended, suboptimal) —**
`calculus/gill/tests/forward/contention.gill`, executable:

```
r1: a * tok -o { won_a }.
r2: b * tok -o { won_b }.        % initial: a@0, tok@0, b@5
```

`r1`'s instance activates at `0`, `r2`'s at `5` — never tied, so the run is
deterministic (the PRF chooser is never consulted) and trivially confluent.
`settle` fires `r1` at the frontier `0`, consumes `tok`, and `r2` starves
forever. The monotone relaxation derives `won_b@5`; the run does not — the
spec's `#expect_not_starved` asserts the *absence* of `won_b@5` in the
settled state, which here equals non-reachability across all runs because
the program never ties (the one run is all runs). T1 holds; T2's hypothesis
and conclusion both fail. The spec's twin program (`read rtok` instead of
consuming) is contention-free and realizes both relaxation stamps — the
recovery of §5.

**Lemma L3 (diamond).** If `m₁ ⌣ m₂` at `s`, then `s —m₁→ · —m₂→ t` and
`s —m₂→ · —m₁→ t'` with `t = t'`.

*Proof.* By (1) each cohort is intact after the other fires; by (2) read
demands and bound quantities are undisturbed, so both remain enabled *as the
same instances*; by (3) neither's activation gains a term from the other's
outputs, so each fires at its original `a(m)` and produces identically
stamped conclusions. Multiset removals with available combined take commute,
additions commute, persistent-set unions commute — and a persistent
conclusion of one cannot *disable* the other's `Π` goals: backward
provability is monotone in `P` (no negation), and the other was already
enabled without it, so it fires identically in both orders. ∎

**Lemma L4 (enabledness preservation).** In a contention-free program, if
`m ∈ E(s)` at a run-reachable state and `settle` fires `m' ≠ m`, then
`m ∈ E(s')` with `a(m)` unchanged. *Proof.* Both `m` and `m'` are firings of
the relaxation (every run-enabled instance is relaxation-enabled with the
same activation — the relaxation's states dominate the run's, L5 (⊆)), so
they are independent by contention-freedom; clauses (1)–(3) applied to
`{m, m'}` give preservation. ∎

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
sequence). This direction needs no side-condition. (⊇) Induction on the
relaxation's frontier order. Let `m` be a relaxation firing with
`a(m) ⊑ H`; by induction every token in `κ(m) ∪ reads(m)` is produced by
the run with its relaxation stamp (or is initial). No run firing ever
consumes one of them: a run firing is itself a relaxation firing by (⊆),
distinct from `m`, and a distinct relaxation firing whose cohort overlaps
`m`'s demand would violate contention-freedom — clause (1)/(2) over the
relaxation, *regardless of whether it and `m` are ever co-enabled in the
run* (this is exactly where the run-state quantification failed, E2). So
`m`'s inputs persist; when the last arrives, `m` is enabled in the linear
system; by L4 it stays enabled with unchanged activation; `settle` exits
only at quiescence or when `aMin ⊐ H`, and `a(m) ⊑ H`, so `H`-termination
forces `m` to fire, at exactly `a(m)`. ∎ ⟨open: mechanize the double
induction⟩

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

### 5.3 The focused presentation, and principality

Focusing (Andreoli 1992) is not a search heuristic but a second *calculus*: a
restriction of derivations proved complete, after which the strategy's choices
are canonical rather than semantic. T1/T2 admit exactly this packaging for the
scheduling order.

**Definition (temporally focused derivation).** A forward derivation
`s —m₁→ s₁ —m₂→ ⋯` is **focused below `H`** iff each `mᵢ ∈ Tied(sᵢ₋₁)` and
`a(mᵢ) ⊑ H`. The runs of `settle(s, H)` are precisely the maximal focused
derivations (by construction; under S, L2 makes the activation sequence
nondecreasing).

**Soundness** is inclusion: every focused derivation is a forward derivation —
the restriction adds no rules, so it can prove nothing new.

**Completeness (T2 recast).** Under contention-freedom (below `H`),
`H`-termination, and S: every token that *any* forward derivation produces
with stamp `⊑ H` is produced by *every* maximal focused derivation, at the
same stamp — and the `⊑`-least token of each predicate sits at `σ*`.
*Proof.* An arbitrary derivation's firings are relaxation firings verbatim
(L5 (⊆), which needs no side-condition), so each of its tokens is a
relaxation token; every relaxation firing with activation `⊑ H` is performed
by the focused run with identical stamps (L5 (⊇)), and the least per
predicate is `σ*` (T2). ∎

The min-activation discipline and the B&B prune (L1) thereby acquire the same
status the focusing discipline has in backward search: they discard only
derivations that completeness proves redundant. The committed scheduler is
the canonical-form normalizer of the forward calculus — *precisely* on the
contention-free fragment. P1 (§6) is where the packaging honestly stops:
beyond contention-freedom, the restriction changes what is derivable-in-the-
run, and only `settleExplore` is complete.

**Principality (the derivability face).** In the till sequent calculus the
timed judgment `Δ ⊢ {S}@T` (stamped contexts `at(A,t)`, horizon as monad
grade) is upward closed in `T` — subeffecting derives every bound above an
achievable one — so the semantic content of a goal is its *least* derivable
horizon: the principal grade. T2 is the statement that `settle` realizes it:
on the contention-free fragment the least derivable `T` for `S` is `σ*(S)`,
and the settle run is its witness — each firing is one derivable `@fire`
instance (bridge soundness, THY_0018 §5). This sharpens the "ASAP scheduling
computes principal grades" metatheorem (THY_0018 §7) with its side-condition
now exact: contention-freedom, not conflict-freedom. The deliberate
asymmetry stands: derivability does *not* imply settle-reachability
(subeffecting has no forward step) — principality is a claim about least
witnesses, and the up-set above them is pure logic.

One guard against a natural conflation: the principal grade of the *pure*
graded monad — no stamped contexts — is a different quantity. With rules as
linear hypotheses, `⊢ {⊗R}@W` holds iff `W` bounds **total sequential work**
`Σδ`, not makespan: the work/makespan separation (THY_0023 Thms 10–11; till
paper Thms 6.3–6.4; kernel-verified pure-backward in
`tests/till-pure-adequacy.test.js` — the join program's least pure grade is
`6 = 2+3+1` while settle's stamp is `4 = max(2,3)+1`). Makespan is
contributed exclusively by the stamp *coeffect*, and the focused calculus
above is the coeffect-side statement. The engineering half is landed:
settle is a *certifying* scheduler (TODO_0294) — the event trace
elaborates into a fully kernel-checked `@fire` derivation (the trace≅term
observation made executable; `@fire` is a first-class rule of the
calculus, check-only in search), fuzz-tested on random programs. The
elaborator covers the full antecedent/consequent surface (counted takes
and consequents, whole-bind, possessed rules, bang succedents); with a
bound fire checker an elaboration failure *throws* as an
engine/elaborator disagreement. The trusted-oracle node survives only
for calculi that have not bound a fire checker, and the checker proves
its stamp judgments clause-only — the numeric FFI is never on the
verification path.

---

## 6. The dichotomy, and how real programs decompose

**Proposition P1 (beyond contention-freedom).** If a program is not
contention-free below `H`, some pair of relaxation firings `m₁ ⌣̸ m₂`
shares demand. Then the relaxation's `σ*` need not be realized
(E1, E2), and distinct firing orders can reach `⊑`-incomparable final states
(Pareto-incomparable under a product grade). `settle` realizes exactly one —
the PRF-committed, locally-greedy world (still chooser-independent if the
program is choice-free, E1) — and `settleExplore` enumerates the reachable
set. The Pareto-frontier characterization is discharged in §8.4
(frontier adequacy: `settleFrontier` = the `⊑ₚ`-minimal completion
vectors of the committed worlds); the residual ⟨open⟩ is the
focused-frontier gap.

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
implied by the syntactic absence of division in delay positions. Note the
guard modes differ: `maxInstantSteps` *throws*, while the proposition's
conclusion is a clean exit — no conflict, because under (2)/(3) the
Dershowitz–Manna measure guarantees each instant fires finitely often, so
the guard never triggers on a program satisfying the hypotheses. C5 of the
conformance contract records the per-algebra half (a well-ordered reachable-
stamp bound); this proposition is the per-program half.

---

## 8. Instantiation

### 8.1 Time and distance — one dioid, two readings

`tillGrades` (time) and `distGrades` (distance) are the *same* scheduling
dioid `(ℚ≥0, max, +, 0, ≤)`; C1–C4 are machine-checked for both by
`tests/engine/grade-conformance.test.js` (exact BigInt rationals; the `merge`
slot declared symbolically as `'join'` and id-lifted by the StampTable, whose
B&B cut is the contract-fixed `cmp ≥ 0`). Under the time reading, T2 says: stamps are
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
| C1–C4 for time/distance (and their coherence with the hash face; C5 is §7's proposition + the operational guards) | `tests/engine/grade-conformance.test.js` |
| L1's FIFO invariant pair (prune `⊒` / leaf `<`) | till equal-activation tie tests (till-eat, till-fifo-pair) |
| T2 on the conflict-free fragment ≡ exact Dijkstra | `tests/engine/gill-dist.test.js` (random graphs, exact rationals) |
| the layered decomposition (core + harvest) | `calculus/gill/tests/forward/depot.gill` |
| T1 ⇏ T2 (choice-free, contended, suboptimal) | `calculus/gill/tests/forward/contention.gill` (E1) |
| run-state quantification too weak (deferred producer, `E(s)` always a singleton, still starved) | `contention.gill` (E2) |
| read-relaxation recovers `σ*` (Dyna corollary) | `contention.gill` twin program |
| the measure-class fence (§8.3) | `tests/engine/gill-weight.test.js` |
| the C4 split (C1ₗ–C3ₗ + C4a hold; C4b + lex-monotone `⊔` fail, witnesses pinned) | `tests/engine/grade-conformance.test.js` (product arm) |
| L1× lex tie-break; cw-join activation; the L2× whole-bind regression witness; coalesce/accel fences | `tests/engine/sill-product.test.js` |
| product algebra ∥ BigInt reference ∥ clause face ∥ engine ∥ certifyRun (differential) | `tests/engine/sill-fuzz.test.js` |

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
  but *scheduling* over a usage axis is unproven — ⟨open⟩. §8.4's C4a is
  the candidate replacement (`⊔ = +` is still a `≤`-upper bound), but
  losing idempotency breaks the induced-order framing itself
  (`a ⊔ a ≠ a`), so the dioid definition, not just the lemma, needs
  reworking.
- **Contention (independence clause 1).** E1 — and E2 for why the condition
  must be read off the relaxation, not the run. The general dichotomy (§6).
- **Read-starvation (clause 2).** A whole-bind `!_W A` binds the total, so
  its instance is disturbed by any co-instant arrival or take on `A`; a trim
  rule written with `!_W` can starve forever under a deterministic chooser
  (PP2 §3b). The starvation-free form is a counted take (`!_201 g -o
  { !_200 g }`) — which restores independence by demanding a fixed cohort.
- **Instant-feeding (clause 3).** Zero-delay production into a co-tied
  instance's premises orders the tie causally; the settle loop detects this
  (`_feedsInstant`) as tie-sensitivity for acceleration.
- **Hypothesis S.** A timed rule with a `!`-conclusion can backdate
  enablement (§1.3): frontier regression, outside L2. Shipped as the C2
  advisory (§11).

### 8.4 The product instance: the C4 split and the materialized frontier

sill's scheduler axis is the product `(time, dist)` — one stamp value,
`⊗` and `⊔` componentwise, both axes the scalar dioid of §8.1 (TODO_0285
P6; the theory record is THY_0033 §2). Two orders now live on the
carrier: the **product order** `⊑ₚ` induced by the merge (`a ⊑ₚ b :⇔
a ⊔ b = b`, partial — the order every dioid axiom speaks about) and the
**lexicographic order** `⊑ₗ` (time primary, dist tie-break; `∞` above
every finite dist) that the engine runs as `cmp`. `⊑ₗ` refines `⊑ₚ`
(per-axis dominance implies lex dominance), and the two agree exactly on
the scalar embedding (dist 0). The scheduling-dioid definition of §1.1
assumed they coincide; the product is the instance where they don't, and
the honest question is which theorems needed the coincidence.

**The C4 split.** C4 ("merge is the join for `⊑`") factors into two
strictly weaker halves:

- **(C4a)** `⊔` is a `⊑ₗ`-**upper bound**: `a ⊑ₗ a ⊔ b`. Holds — the
  `⊑ₚ`-join dominates both inputs per axis, and `⊑ₗ` refines `⊑ₚ`.
- **(C4b)** `⊔` is **selective**: `a ⊔ b ∈ {a, b}` (the `⊑ₗ`-max).
  Fails: `(3,5) ⊔ (4,2) = (4,5)`, neither argument — the join of
  co-consumed stamps waits for the last input in time AND carries the
  dearest accumulated cost, which no single input witnesses.

Both halves, and every claim of the transfer lemma below, are
machine-checked on the shipped instance
(`tests/engine/grade-conformance.test.js`, product arm). C4b is exactly
**coalesce-safety**: coalescing rewrites past-of-bound stamps to a
normal form, which is sound only when the activation join is the
scheduling-order max — so the engine fences coalesce (and acceleration,
which requires it) on the function-valued-merge discriminator. The fence
and the split are the same line, stated operationally and algebraically.

**Lemma L6 (lex transfer).** Let `V₁` (primary) and `V₂` be scheduling
dioids with `⊗₁` *strictly* isotone (`a ⊏₁ b ⟹ a ⊗₁ c ⊏₁ b ⊗₁ c`).
Equip `V₁ × V₂` with componentwise `⊗`/`⊔` and the lex order for `cmp`.
Then C1 (totality), C-iso, C-infl hold for `⊑ₗ`, and C4 weakens to C4a.
*Proof.* Totality and inflation are immediate per axis (a tie on the
first axis falls through to the second). Isotonicity: if `a₁ ⊏₁ b₁`
then `a₁ ⊗ c₁ ⊏₁ b₁ ⊗ c₁` by strictness — the first axis still decides;
if `a₁ = b₁` both first components stay equal and the second axis is
isotone. C4a as above. ∎ Strictness is load-bearing: with `⊗₁ = max`
(not strict), `(1,9) ⊑ₗ (2,0)` but composing both with `(3, 0)` gives
`(3,9) ⊐ₗ (3,0)` — the lex order does not survive a non-strict primary
compose. Time's `⊗ = +` on ℚ≥0 is strict, so the shipped instance
qualifies. One further loss is worth pinning: `⊔` is **not
`⊑ₗ`-monotone** (`x ⊑ₗ x'` does not give `x ⊔ y ⊑ₗ x' ⊔ y`), so
Kleene-style fixed-point arguments over `⊑ₗ` are unavailable — the
optimality proof below goes through relaxation adequacy (operational),
not through (★) as a `⊑ₗ`-least fixed point.

**What survives, by inspection of the proofs.** L1 and L2 used C4 only
through "activation is nondecreasing along completions" and "a join with
one input `⊒ t` is `⊒ t`" — both are C4a. The single C4b-dependent step
in the entire development is L2's **whole-bind rescue**: the argument
that a re-formed `!_W` instance below the frontier must have been *tied*
before the firing concluded "every joined stamp `⊑ t`, hence the join
`⊑ t`" — join-below-bound from inputs-below-bound, which is C4b. Under
C4a only, the join of lex-bounded stamps can lex-exceed the bound, and
the rescue fails *executably*: a choice-free product program with
`!_W g` and cohorts `g@(1~5), g@(2~3)` fires a competing rule at
`(2,3)`, after which the whole-bind's forced join drops from `(2,5)` to
`(1,5)` — the frontier regresses with no tie ever occurring
(`tests/engine/sill-product.test.js`, the L2× witness). Hence:

- **L1× (per-firing optimality)** — verbatim under L6's conditions
  (B&B prune, FIFO invariant pair; the lex tie-break test pins the
  dist-cheaper cohort winning at equal time).
- **L2× (frontier monotonicity)** — under S, for **whole-bind-free**
  programs; the choice-freedom disjunct of L2 does not lift.
- **T1× (confluence)** — choice-free, whole-bind-free, `H`-terminating,
  S: chooser-independent final state. Same Newman/L3 skeleton (L3 and
  L4 are order-free).
- **T2× (lex optimality + materialized frontier)** — contention-free
  (on the relaxation), whole-bind-free, `H`-terminating, S: `settle`
  performs exactly the relaxation's firings with activation `⊑ₗ H`,
  with identical stamps (L5's double induction runs on `⊑ₗ`, which is
  total and, below `H`, well-founded on the firing set). Note
  `certifyContention` already *refuses* whole-bind shapes
  conservatively, so the analyzer's certified fragment sits inside the
  theorem's hypotheses.

**Corollary (the materialized frontier).** Under T2×'s hypotheses, the
run *produces* one token per relaxation instance below `H` — so for
every fact `p`, *every* achievable `(time, dist)` value of `p` is
realized as a concrete token of the run, and in particular the entire
per-fact **Pareto frontier** (the `⊑ₚ`-minimal achievable values) is
materialized in one committed run — persisting to quiescence for any
predicate no rule consumes, and consumed by at most one firing
otherwise (contention-freedom makes the consumer unique). The scalar
shadow is already visible in `depot.gill`: both route derivations
coexist as `depot_reached` tokens (stamps 6 and 7) and the harvest step
takes the least. On the contention-free fragment,
multi-objective optimality needs no exploration: all Pareto-optimal
derivations coexist because nothing competes for their tokens. The
frontier *problem* — choosing among incomparable completions — is
created by consumption, precisely the paper's central reframing (§6)
restated in two dimensions.

**Proposition (frontier adequacy, the contended case).**
`settleFrontier(s, H)` returns the `⊑ₚ`-minimal **completion vectors**
(a leaf's cost = `⊔` over its final tokens' stamps) over the leaves of
`settleExplore` — dominance derived from the join, `a ⊑ₚ b :⇔ a ⊔ b =
b`, no second order ever declared. Soundness: every leaf is the final
state of some committed (temporally focused, §5.3) run — explore
branches only on genuine conflicts and commits independent tied sets,
whose members commute (the ample-set argument; fuzzed by the
containment arm of `tools/fuzz-till.js`). Completeness over the focused
set: every chooser-reachable final state appears among the leaves. So
the output is exactly the Pareto frontier *of the committed worlds*;
for a scalar algebra it degenerates to the singleton T1 already forces.

**The focused-frontier gap is real, and strict.** Witness **W-gap**
(`tests/engine/sill-product.test.js`, "the focused-frontier gap is
STRICT"): E1's shape with the greedy winner made slow —

```
r1: a -o { c }@(100 ~ 9).
r2: a * b -o { c }@(1 ~ 1).      % initial: a@(0,0), b@(5,0)
```

`r1` activates at `(0,0)`, `r2` at `(5,0)` — never tied, so the program
is *choice-free* (the chooser is never consulted, T1 holds) and
`settleExplore` has exactly one leaf: `settle` fires `r1`, and the
committed frontier is `{(100, 9)}`. The *unfocused* derivation that
spares `a` fires `r2` at `(5,0)` and completes at `{(6, 1)}` — strictly
`⊑ₚ`-below on **both** axes. And it is a genuine derivation of the full
program: the witness elaborates its trace against the full rule set and
the kernel verifies the resulting `@fire` tree — a certified derivation
the exploration cannot reach. Here the true frontier `{(6,1)}` and the
committed frontier `{(100,9)}` are *disjoint*. So frontier adequacy
under choice-freedom alone is irreparably partial: the E1 separation
between the two side-conditions (§3) recurs verbatim at the frontier
face — and sharpened, since E1's own missed world was cost-*equal*
(both completions 5), while W-gap's scalar shadow (`r1 … @100`,
`r2 … @1`, same test file) turns T2's failure into a strictly worse
completion, `100` against the achievable `6`.

What voids the gap is contention control — and strictly less than full
contention-freedom suffices:

**Proposition (tied-contention adequacy).** Let the program satisfy S,
be `H`-terminating, whole-bind-free below `H`, and **tied-contended**:
every *dependent* pair of relaxation firings with activations `⊑ H` is
co-activated (equal activation). Then the final state of every maximal
spec-conformant derivation below `H` is the state of some
`settleExplore` leaf — the committed worlds are *outcome-complete* —
and `settleFrontier` returns the true Pareto frontier over all such
derivations. ("Spec-conformant": within-rule equal-activation match
selection follows the Matching spec's FIFO break — the same scope as
explore's own enumeration guarantee, whose docstring flags the broader
assignment-level branching criterion as open.)
Contention-freedom is the degenerate case with *no* dependent pairs —
then there is one leaf, and the proposition collapses to T1× plus the
materialized frontier.

*Proof.* Two steps. (i) *Every maximal derivation reorders to
activation order.* Take an adjacent inversion: `m'` fired immediately
before `m` with `a(m) <ₗ a(m')`. `m` cannot consume an output of `m'`:
outputs of `m'` carry stamps `⊒ₚ a(m')` (per-axis inflationarity,
C-infl), and `a(m)` joins over `m`'s consumed stamps, so it would be
`⊒ₗ a(m')`. If `m ⌣̸ m'` (dependent — clauses (1)–(3), read on the
relaxation via L5 (⊆): every run-enabled instance is a relaxation
firing with the same activation), tied-contention forces
`a(m) = a(m')`, contradicting strictness. So the pair is independent,
and L3 (proved from C1–C3 + C4a, so it holds for the product) swaps
them with identical stamps and final state. `H`-termination makes the
derivation finite; the bubble sort terminates. (ii) *An
activation-ordered maximal derivation is an explore path.* Suppose at
state `s` the sorted derivation next fires `m` with `a(m) >ₗ aMin(s)`,
and let `m₀` realize `aMin`. All later firings have activation
`≥ₗ a(m) >ₗ aMin`, so any firing that disables `m₀` or disturbs a
quantity it binds is dependent with it at unequal activation —
excluded. Hence `m₀` remains enabled forever and is never fired:
maximality is violated. So the sorted derivation always fires inside
`Tied(s)`; within an instant, explore either branches over every
tied-first order (conflict or instant-feeding present — covering the
derivation's choice) or commits one order of an independent,
non-feeding tied set, all of whose orders reach the same state (L3).
Induction along the derivation (well-founded by `H`-termination) lands
its final state on a leaf. ∎

Tied-contention is statically analyzable in the same sense as
contention-freedom: the relaxation's firing set and activations are a
scheduling-independent least fixed point, and `certifyContention`'s
pairwise pass extends by *comparing activations* of dependent pairs
(refuse only the unequal ones) — recorded as engineering follow-up, not
shipped; today's analyzer certifies the stronger condition, which sits
strictly inside the hypotheses. The hierarchy, at the frontier face:

```
contention-freedom  ⟹  tied-contention  ⟹  frontier adequacy
```

and W-gap pins that choice-freedom implies none of it.

**Termination lifts per-axis, asymmetrically.** §7's proposition holds
with "instant" read on the *time* axis only: (1) lattice delays on the
time components, (2) the zero-*time*-delay feed graph acyclic, (3)
every zero-*time*-delay rule consumes. The dist axis needs no lattice
condition — the per-instant Dershowitz–Manna measure counts firings
regardless of their dist values, and the instant count below `H` is
bounded by the time axis alone. The engine asymmetry mirrors §7's:
a `(0, d>0)` self-feeding loop violates (2)/(3) analytically, but
*evades* `maxInstantSteps` (lex progress includes dist-only progress at
a fixed time), so the operational catch is the opt-in `maxSteps` — the
same guard-shape as accumulation Zeno under division.

**Transport stays a rule.** The lawful axis coupling is per-hop rule
structure (`!dist L L' T D` feeding `@(T ~ D)`), never a grade coercion
of dist into time — algebraically lawful coercions exist in abundance
(graded-monad morphisms), and the refutation is semantic: a coercion
feeds each hop's cost into both axes and collapses the two objectives
the product exists to keep apart. THY_0033 §3 (the axis-confounding
argument) is the record; the certified face stays clause-only (the
componentwise join is re-derived through the declared `join` predicate,
since under C4a it may equal no single input —
`tests/engine/sill-product.test.js`, certification block, and the
four-leg differential fuzzer `tests/engine/sill-fuzz.test.js`).

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
   split** (§3): two side-conditions with distinct theorems — T1
   (confluence: the committed world is chooser-independent) under the
   weaker, run-level condition, T2 (optimality: realized stamps = the
   semiring least fixed point `σ*`) under the stronger condition, which
   lives on the program's *monotone relaxation* and is therefore statically
   analyzable — separated by executable three-line witnesses: E1
   (deterministic, confluent, suboptimal) and E2 (the same starvation with
   every run state contention-blind, forcing the relaxation-level
   quantification). This locates *exactly* where semiring shortest-distance
   survives linear consumption. Equivalently packaged (§5.3): T1 + T2 are
   the soundness and completeness of a *temporally focused* restriction of
   forward derivation — the Andreoli move applied to the scheduling order —
   under which the B&B prune discards only derivations completeness proves
   redundant, and settle's stamps are the principal grades of the timed
   sequent judgment.
2. **The reframing.** Monotone semiring forward-chaining solves a fixed
   point; linear forward-chaining solves a fixed point **coupled with a
   matching problem** (which derivations get the tokens). Contention-freedom
   is precisely the vacuity of the matching constraint; the persistent/read
   limit degenerates back to Dyna/provenance evaluation (T2's corollary);
   the layered decomposition (§6) makes the reframing an engineering
   discipline, not just a theorem scope.
3. **The executable, pluggable realization.** `settle` as an operational
   semiring shortest-distance engine over a *declared* grade algebra:
   per-firing optimality unconditionally (L1), frontier monotonicity under
   S with the whole-bind caveat (L2), `σ*` on the contention-free fragment,
   one committed world beyond it with `settleExplore` as the enumerator —
   with the algebraic conditions C1–C4 machine-checked per instance
   (conformance harness; C5 characterized analytically in §7 and enforced
   operationally) and every out-of-scope algebra loudly fenced rather than
   silently mis-run.
4. **The C4 split and the multi-objective transfer** (§8.4). The scalar
   theory's C4 (merge = order max) factors into C4a (merge is an
   upper bound in the scheduling order — all the core lemmas need) and
   C4b (merge is selective — needed only by the whole-bind rescue and
   by coalesce/acceleration, making C4b *exactly* coalesce-safety). The
   time×dist product satisfies C4a under the lex order (the transfer
   lemma, with strict primary isotonicity as the one extra hypothesis),
   so T1×/T2× survive with whole-bind excluded — the exclusion witnessed
   by an executable choice-free frontier regression. Two payoffs: on the
   contention-free fragment one committed run **materializes the entire
   per-fact Pareto frontier** (multi-objective optimality without
   exploration — the frontier *problem* is created by consumption,
   claim 2 in two dimensions); beyond it, `settleFrontier` returns
   exactly the `⊑ₚ`-minimal completion vectors of the committed worlds,
   with dominance derived from the join rather than a second declared
   order — and that committed frontier is the *true* frontier exactly
   under **tied-contention** (every dependent relaxation pair
   co-activated: the adequacy proposition, strictly weaker than
   contention-freedom), while dropping the condition is strict
   (witness W-gap: choice-free, one committed leaf, a kernel-certified
   unfocused derivation strictly below it on both axes).
   Multi-priced timed automata compute Pareto curves by model
   search over clock valuations; graded type systems carry product
   grades statically; neither runs a committed scheduler whose total
   order provably survives the product, nor locates the C4a/C4b
   boundary.
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

### 10.4 The four collisions, pre-empted

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

**"Isn't priority-driven committed choice CHRrp — or timed MSR?"** CHR
with rule priorities (De Koninck–Schrijvers–Demoen 2007) is the closest
*operational* neighbor: a consuming committed-choice rewriting engine whose
firing order is user-controlled. But its priorities are static integers
declared per rule — no algebra over them (no `⊗` accumulation along a
derivation, no `⊔` synchronization of co-consumed inputs, no residual), no
per-firing minimization over cohorts, and no optimality theorem; it answers
"which *rule* first," not "which *cohort* realizes the `⊑`-least stamp."
Timed multiset rewriting (Kanovich–Ban Kirigin–Nigam–Scedrov–Talcott 2016)
consumes timestamped facts, but its time annotations are *constraints* for
verification — reachability, realizability, survivability, with
PSPACE-completeness results checked by model search — not grades an
operational scheduler optimizes; nothing there computes `σ*` or claims a
schedule optimal.

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
- ✔ **Pareto characterization** — discharged as §8.4 (0285 P6): the C4
  split, the lex transfer lemma, T1×/T2× with the whole-bind exclusion
  (executable witness), the materialized per-fact frontier on the
  contention-free fragment, and frontier adequacy for `settleFrontier`.
  Residual — the **focused-frontier gap** — resolved both ways (§8.4):
  YES, strictly (witness W-gap: choice-free, one committed leaf at
  `(100,9)`, a kernel-certified unfocused derivation at `(6,1)` —
  disjoint frontiers); and the focused frontier is full under
  **tied-contention** (every dependent relaxation pair co-activated) —
  the tied-contention adequacy proposition, sitting strictly between
  contention-freedom and adequacy. Remaining engineering: the
  `certifyContention` extension that compares activations of dependent
  pairs; remaining theory: the assignment-level branching scope
  (shared with explore's own enumeration guarantee — its docstring's
  open criterion).
- ✔ **Static analyzers** — discharged (TODO_0293 a/b/c):
  (a) `certifyContention` (`lib/engine/timed/certify.js`) — structural
  conflict-freedom (the one-shot-edge discipline, state-independent),
  else the relaxation-level check: the monotone relaxation's firing set
  as a fixpoint over the declared rule data (never settle), with
  pairwise independence over clauses (1)–(3); conservative (whole-bind /
  counted / weighted shapes refuse with a reason). E1 and E2 are refused
  — E2 exactly because the relaxation exposes the deferred producer's
  demand — the read twin and one-shot-edge graphs certify, and a
  horizon-bounded contention outside `H` correctly certifies below it
  (`tests/engine/timed-certify.test.js`). Hardened by a 2026-08-29
  adversarial audit (TODO_0296): the first release wrongly certified
  four families — same-rule multi-instance contention through non-ground
  premises, consume/read starvation at the structural tier, implicit
  zero-delay rules, and a relaxation under-enumeration bug — each now a
  refusing regression test. The structural tier additionally demands
  ground consumed premises and ground positive delays; anything else
  falls to the relaxation;
  (b) the whole-bind arrival advisory (`timedAdvice` C3) — flagged on
  PP2's own documented §3b family (kiln/wood, spoil/food, merge_space);
  (c) the Hypothesis-S advisory (`timedAdvice` C2) with the
  external-choice-menu exemption, including `!`-conclusions inside
  MINTED possessed rules; PP2's menu-only corpus status is now
  machine-checked, not by-inspection.
- ⟨open⟩ **Usage-axis scheduling** (non-idempotent ⊔) — C4 fails; what
  replaces L1's monotone-completion argument?
- ✔ **Termination** — discharged as §7's proposition (lattice delays +
  instant acyclicity + instant consumption); remaining only necessity /
  decidability refinements.
- ✔ **Focused presentation** — discharged as §5.3 (temporally focused
  derivations; completeness = T2 recast; principality via THY_0018 §7 and
  the work/makespan separation as the guard). The certifying-scheduler
  engineering landed with it (TODO_0294 B1–B4: first-class `@fire` rule,
  trace elaborator, full kernel verification, certification fuzzing).

---

## 12. Citations

Andreoli, "Logic Programming with Focusing Proofs in Linear Logic," J. Logic
Computat. 2(3), 1992.
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
Processes," LICS 1997. Kanovich–Ban Kirigin–Nigam–Scedrov–Talcott, "Timed
Multiset Rewriting and the Verification of Time-Sensitive Distributed
Systems," FORMATS 2016 (arXiv:1606.07886). De Koninck–Schrijvers–Demoen,
"User-definable Rule Priorities for CHR," PPDP 2007.
Orchard–Liepelt–Eades, "Granule," ICFP 2019. Atkey,
"Syntax and Semantics of Quantitative Type Theory," LICS 2018. Ghica–Smith,
"Bounded Linear Types in a Resource Semiring," ESOP 2014. Hughes–Orchard,
"Program Synthesis from Graded Types," ESOP 2024. Gurney–Griffin,
"Lexicographic Products in Metarouting," ICNP 2007 (strict primary
isotonicity for lex-product routing algebras — the transfer lemma's
hypothesis in its native habitat). Bouyer–Brinksma–Larsen, "Optimal
Infinite Scheduling for Multi-Priced Timed Automata," FMSD 32, 2008
(Pareto reachability by model search over clock valuations — the §8.4
contrast). Goodman, "Semiring
Parsing," Computational Linguistics 25(4), 1999. Eisner, "Parameter
Estimation for Probabilistic Finite-State Transducers," ACL 2002
(expectation semirings; also Li–Eisner, EMNLP 2009). Huang, "Advanced
Dynamic Programming in Semiring and Hypergraph Frameworks," COLING 2008
(tutorial notes).
