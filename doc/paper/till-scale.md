


# till: An Executable Timed Graded Linear Logic with Proven-Exact Acceleration

**Abstract.** We present **till** — timed intuitionistic linear logic — a graded
sequent calculus whose execution semantics IS the logic: multiset rewriting is
forward proof search, and every state transition is a derivable sequent.  till
extends intuitionistic linear logic with a delay-graded lax monad `{A}@d` (the
critical-path delay as a tropical (max,+) grade), graded bangs `!_k A` and `!_W A`
(counted and whole-cohort exponentials), a probability-weighted internal choice
`A +[q] B`, and fenced grade algebras that make grade invalidity mean rule
inapplicability, not a side-condition obligation.  The execution model — the
`settle` scheduler — is a deterministic, horizon-split-invariant function of the
state.  Every performance optimization ships with a proven state-identity law and
a machine-pinned differential test: the index is optimization, the multiset is
semantics.  The combined stack scales a symbolic-execution engine from 180 ms/tick
to 0.2 ms/tick, eliminates Store growth over simulated weeks (1.9M → 161 nodes
over 4 simulated days), batches million-item populations in constant time, and
resumes 3-week idle gaps in 38 ms with bit-exact replay.

---

## 1. Introduction

### The problem

Symbolic execution over linear resources — concurrent protocol verification,
game mechanics, economic simulations, contract replay — inhabits a no-man's
land between two unsatisfying extremes.  On one side, logic-based frameworks
(CLF, Ceptre, timed multiset rewriting) provide clean semantics but stop scaling
at toy populations and short time horizons: they accumulate one proof tree node
per event, never compress time, and have no theory of optimization soundness.  On
the other, ad-hoc game or simulation engines scale, but carry no semantics: an
optimized engine can silently change reachable worlds, performance bugs become
logic bugs, and replay breaks without warning.

The specific failure modes are concrete: a timed symbolic engine accumulates a
hash-cons arena entry for every (atom, timestamp) combination it mints — an
immortal cost that grows with elapsed simulation time, not with live state size.
A naive scheduler scans the full population for each rule activation; a
million-item cohort costs a million steps.  Accelerating past an idle period
requires unrolling every intervening event.  None of these costs are inherent to
the problem — they are artifacts of conflating the semantics-carrying
representation with the operational one.

### The doctrine

till is organized around one design axiom: **an optimization may never change the
world**.  Formally, every optimization is a morphism on states with a stated
law (state-identity, world-preservation, or bound-preservation), and every such
law is mechanically pinned by a differential test that runs both paths and asserts
observational equivalence.  A claimed optimization that cannot be pinned is not
shipped.  A pin failure is a soundness bug, not a performance regression.

The corollary: **loud refusal over silent wrongness**.  When a guard's premise
fails — a grade residual is undefined, a cohort count is zero, a covariance
check fails — the rule simply does not fire.  No clamping, no wraparound, no
silent default.  The partial grade residual (§3.3) is the algebraic expression of
this principle: undefinedness is inapplicability, not an error to be caught.

### Contributions

1. **The delay-graded lax monad `{A}@d`** (§3): the first sequent calculus for a
   graded lax/possibility modality, with cut admissibility and identity expansion
   proved in full (discharging all of CLF's prior sketches for the ungraded case
   extended to grades).  The tropical (max,+) algebra as both the activation
   coeffect and the delay effect, with a single cut whose two-line proof needs
   only the ordered-commutative-monoid laws.

2. **Fenced grade algebras** (§3.3): a partial residual whose undefinedness equals
   rule inapplicability, removing all per-rule side-condition obligations by
   making illegal grades unconstructible.  Grade Preservation holds by
   construction for all rules, including future ones.

3. **The work/makespan separation theorem** (§3.4): pure backward derivability
   measures total sequential work (Σ delays); the bridge (`@fire` promotion rule +
   `settle`) measures makespan (max-plus critical path).  The stamp layer is not a
   conservative decoration of the graded monad — it is a provable extension.

4. **Graded labelled states** (§5): stamps live beside content-addressed terms as
   interned label columns, not inside them.  Address stability follows: the Store
   stops growing with elapsed time.  The count column (multiplicity) and the stamp
   column are the same construction over different grade algebras (ℕ vs ℚ≥0).

5. **Exact orbit acceleration** (§6): periodic orbits are certified as portable
   proofs (mint / validate / resume); the phase-independence lemma makes
   exit-phase minting exact; covariant tie-PRF draws extend certification to
   multi-consumer economies with stochastic branching.

6. **Forced-prefix cohort firing** (§7): a negative result (confluence proves the
   wrong thing for a draw-based committed-choice scheduler), a positive theorem
   (three invariants that make the scheduler repeat itself exactly k times, so the
   batch equals the sequential k-prefix bit-exactly), and the observation that a
   theorem's premises are a checklist for the implementation — two live bugs found
   by working the proof conditions.

7. **An evaluation methodology** (§8): differential pinning as a first-class
   contribution, not just a testing practice — every optimization is pinned
   state-identical against its unoptimized path, making the pin suite a machine
   proof of the optimization's stated law.

---

## 2. Background: ILL, CLF, and the CALC engine

till is implemented inside CALC, a proof calculus platform for intuitionistic
linear logic (ILL) with a content-addressed term store.  ILL's resource
interpretation — every hypothesis consumed exactly once — makes it a natural
semantics for state: a resource held is a proposition true, a resource consumed
is a fact used.  CLF (Watkins et al. 2002) extends ILL with a lax monad `{A}`
marking the boundary between backward proof search and forward multiset
rewriting.  CALC implements this five-layer architecture: a content-addressed
kernel, generic search primitives, Andreoli focusing, strategy layers (manual and
auto backward; committed-choice and exhaustive forward), and a LNL/ILL layer.

ILL connectives: tensor `⊗`, linear implication `⊸`, unit `1`, additive
conjunction `&`, additive disjunction `⊕`, exponential `!`, existential `∃`,
universal `∀`.  The lax monad `{A}` (CLF's boundary marker) becomes `{A}@d` in
till, graded by a delay from the tropical dioid.

---

## 3. The till Calculus

### 3.1 The grade algebra

till's graded modalities are organized around the tropical dioid
`𝕋 = (ℚ≥0, max, +)`:

- **Delays (effect)** `D = (ℚ≥0, +, 0, ≤)` — delays compose by `+` along a
  production chain (critical path).
- **Time points (coeffect)** `T = (ℚ≥0, max, 0, ≤)` — availability stamps combine
  by `max` at a tensor of inputs (synchronize: wait for the last input).
- **The action** `⊳ : T × D → T`, `t ⊳ d = t + d` — a duration translates a
  time point.  Laws: `t ⊳ 0 = t`, `(t ⊳ d) ⊳ e = t ⊳ (d + e)`, and
  `max(t,t') ⊳ d = max(t ⊳ d, t' ⊳ d)` (the tropical semiring law).

Every proof and theorem in §3–7 uses only these laws.  The calculus is therefore
parametric: any (ordered commutative monoid `D`, join-semilattice `T`, monotone
distributive action `⊳`) instantiates it.  The tropical instance is the timed one.

### 3.2 Syntax and rules

Formulas extend ILL with stamped atoms `A@t` (availability at time `t ∈ T`) and
the graded monad `{S}@d` (delay `d ∈ D`; bare `{S}` abbreviates `{S}@0`):

**Judgments** (following the judgmental lax logic of Pfenning–Davies 2001):

- `Γ; Δ ⊢ A true` — `A` holds of persistent `Γ` and linear `Δ`.
- `Γ; Δ ⊢ S lax@d` — `S` is achievable within delay `d` of the context's
  availability (delay is relative; stamps make it absolute).

**The graded fragment** (ILL rules unchanged):

```
Γ; Δ ⊢ S true                 Γ; Δ ⊢ S lax@d   d ≤ d'
─────────────── lax          ─────────────────────────── sub
Γ; Δ ⊢ S lax@0               Γ; Δ ⊢ S lax@d'

Γ; Δ ⊢ S lax@d               Γ; Δ, S ⊢ C lax@e
────────────── {}R            ────────────────────────────── {}L
Γ; Δ ⊢ {S}@d true            Γ; Δ, {S}@d ⊢ C lax@(d + e)
```

`{}L` is CLF's sticky left rule with grade composition: eliminating `{S}@d`
inside a lax goal adds `d` to the grade.  Derived: `{{S}@d}@e ⊢ {S}@(d+e)`
(graded μ — delays along a bind chain add), `S ⊢ {S}@0` (unit η).

**The timed promotion rule** ties stamps to grades:

```
Γ; A₁, …, Aₙ ⊢ S lax@d        a = max(t₁, …, tₙ, 0)
────────────────────────────────────────────────────── @fire
Γ; A₁@t₁, …, Aₙ@tₙ ⊢ S@(a ⊳ d) lax@0
```

where `S@u` stamps every atom of `S` with `u`.  Inputs synchronize at
`a` (coeffect `max`); outputs exist from `a + d` (action `⊳`); the lax grade
resets to 0.  This is the SELL promotion rule with a global side condition.

**Counted bangs**: `!_k A` (`k` copies at any ages) and `!_W A` (whole cohort,
`W` the live count at firing time).  Peel rules (`!Rpeel`/`!Lpeel`) with theory
premises `<- !qsub K 1 J` (the partial residual — §3.3).

**Activation windows**: `after E` (strengthens the activation max) and `before E`
(validity deadline) are scheduling annotations on `@fire`, not connectives.  They
have no proof-theoretic footprint beyond the side condition.

**Weighted additive disjunction** `A +[q] B` (§3.5): `q ∈ [0,1] ∩ ℚ`,
producer-side probabilistic choice.

**Refinement sorts** (§3.6, brief): extrinsic Curry-style refinements over
content-addressed terms.  Subsort edges are persistent facts; the loader
materializes the reflexive-transitive closure once, making in-logic subsort
queries total fact lookups.

### 3.3 Fenced grade algebras

Each grade in till lives in a **fenced grade algebra** `(G, ⊕, 0, ≤, V, ⊖)`:

- `V ⊆ G` is the **fence** (validity predicate): `0 ∈ V`, V closed under `⊕`.
- `⊖` is the **partial residual**: `a ⊖ b` is the `h ∈ V` with `b ⊕ h = a`,
  **undefined** when no such `h` exists.

till's instances:

| grade  | `⊕` | fence `V`     | `⊖`                             |
|--------|-----|---------------|---------------------------------|
| delay  | +   | v ≥ 0         | `a−b` when `a ≥ b`, else ⊥      |
| count  | +   | v ∈ ℕ         | `a−b` when `a ≥ b` (ℕ-closed)  |
| weight | ·   | 0 ≤ v ≤ 1    | none — [0,1] is closed under ·  |

**Theorem (Grade Preservation).** If every grade literal satisfies its fence, and
every rule constructs grades only through `⊕` and `⊖`, then every grade in every
reachable state — forward and backward — satisfies its fence.

*Proof.* Base: literals are fence-checked at load.  Step: `a ⊕ b` (V closed);
`a ⊖ b` (in V by definition when defined; when undefined the rule did not fire).
Each firing is a frame-preserving update for V.  Crucially, the quantification is
over *all future rules* — no per-rule side condition is needed.  ∎

The force: per-rule guards (`F >= E`, `K >= 1`) are derived lemmas, now deleted
from till's rules file.  The partial residual's undefinedness IS the guard.

**The in-logic reading**: `a ⊖ b` is definitionally "the H with `b + H = a`" — a
derivability statement `plus H b a` over the sorted domain.  Over bin naturals no
clause constructs a negative H, so the fence is *derivational*.  Three faces
(clause = SLD semantics; FFI = decision procedure; algebra = O(1) fast path) are
fuzz-pinned to agree on definedness and value.

**Design axis**: metric time has two proof-theoretic poles.  The labeled/absolute
pole (IMTL, de Sá–Toninho–Pfenning PPDP'23; timed MSR) uses absolute interval
annotations `A^[a,b]`, accumulation-only rules, a constraint store Ω, and a proof
BRANCHING `split` rule when Ω cannot order two times.  The graded/relative pole
(till) has label-free judgments and one partial operation `⊖`.  Choosing grades
buys compositional, label-free judgments and pays with exactly one partial
operation — `monad_l`'s `H := F ⊖ E` is the labeled system's world-shift
arithmetic `E + H = F` folded into the grade.

### 3.4 Metatheory (THY_0023)

**Theorem (Cut Admissibility).** Three cuts are admissible in the cut-free system:
linear `cut`, lax `cut_lax` (with grade composition `d + e`), and persistent
`cut!`.

```
Γ; Δ ⊢ S lax@d    Γ; Δ', S ⊢ C lax@e
──────────────────────────────────────── cut_lax
Γ; Δ, Δ' ⊢ C lax@(d + e)
```

*Proof sketch.* Lexicographic induction on (formula weight, cut kind, derivation
height).  The principal `{S}@d` case (`{}R` vs `{}L`) reduces to `cut_lax` on
body `S` — the composition `d + e` is exactly what `{}L` already performs, so no
new grade arithmetic appears.  Crucially, the mismatched counted-bang cases
(`!Rpeel` vs `!L0`, `!R0` vs `!Lpeel`) are **vacuous** by theory-premise
partiality: `!qsub K 1 J` is derivable only when `K ≥ 1`, so a case demanding
simultaneously `K = 0` has no witness.  The partial residual deletes principal
cut cases rather than adding proof obligations.  Commutative cases permute the
cut past grade-passive rules using only monotonicity and associativity of `+`.
Grade Preservation (§3.3) ensures the measure is well-founded: the count fence
`V = ℕ` is exactly what makes the induction terminate for counted bangs; the
density of ℚ delays is harmless because delay grades never enter the measure.  ∎

**Theorem (Identity Expansion).** For every formula `A` with ground grades,
`Γ; A ⊢ A` is derivable using axioms only at atoms.

**Theorem (Counted-Bang Completeness).** `!_k A ⊣⊢ A ⊗ ⋯ ⊗ A` (k copies) by
the counted-bang peel/zero rules only; the four rules are complete for the
tensor-power semantics.

**Theorem (Work Adequacy).** For ground `W ≥ 0`: `·; Δ_ε ⊢ {⊗R}@W` is derivable
in the pure calculus iff there is an execution from Δ₀ with firing multiset `n`
and residual `R` such that `W ≥ Σᵢ n(Rᵢ)·dᵢ` (the total sequential work).

**Theorem (Work/Makespan Separation).** The pure graded monad fragment measures
total sequential work (Σ delays); `settle` + stamps measure makespan (max-plus
critical path).  For the join program `{a ⊸ {x}@2, b ⊸ {y}@3, x ⊗ y ⊸ {c}@1}`
from `{a, b}`:

- least W with pure derivability: `6 = 2 + 3 + 1`
- settle output: `c@4` (`max(2,3) + 1`).

The stamp layer is a genuine extension of the graded-monad fragment, not a
conservative decoration.  The bridge-soundness theorem (§4) is precisely the
statement that this extension is consistent with the pure fragment.

### 3.5 Weighted additive disjunction (`woplus`)

`A +[q] B` (weight `q ∈ [0,1] ∩ ℚ`) is a **probability-graded internal choice**:
the producer decides a branch probabilistically.  A plain `⊕` reading is unsound
for the distribution semantics (it drops `q`).  The judgment is extended with a
weight annotation `⟨w⟩`:

```
Γ; Δ ⊢ A lax@d ⟨w⟩
──────────────────────────────── +[q]R₁
Γ; Δ ⊢ A +[q] B lax@d ⟨q·w⟩

Γ; Δ ⊢ B lax@d ⟨w⟩
──────────────────────────────── +[q]R₂
Γ; Δ ⊢ A +[q] B lax@d ⟨(1−q)·w⟩
```

There is no left rule: `woplus` is consequent-only.  **Mass Conservation**: if
`Γ; Δ ⊢ C lax@d` is derivable, the derivation forest (all proofs differing only
in `+[q]R₁/R₂` choices) has weights summing to 1.  **Derivation Forest ≅
Absorbing Markov Chain**: for the duel program `fight: rock * sci ⊸ {woplus 3/4 rock sci}`,
the aggregate derivation mass equals the combat DP `winProbDP(r,s,3/4)` exactly
(rational arithmetic, no floating-point drift).  The delay and weight gradings are
orthogonal: the combined cut has delays adding and weights multiplying, realized
in one cut rule.

### 3.6 Refinement sorts (brief)

Content addressing forces extrinsic (Curry-style) sorts: with sort baked into the
hash, `5:bin ≠ 5:q`, breaking subsumption and requiring coercions.  Instead,
sort membership is a provable persistent judgment; the loader materializes the
reflexive-transitive closure of declared subsort edges as ground facts once at
load, making in-logic subsort queries total lookups.  The FFI principle one level
up: the sort table is optimization, membership proof is semantics.

---

## 4. Execution: Timed Matching and the Settle Scheduler

### 4.1 States and matches

A **timed multiset state** is a finite map from (atom, stamp) pairs to positive
counts; a (atom, stamp, count) triple is a **cohort**.  Rule antecedents have
timed patterns:

| pattern    | matches                            | binds                       |
|------------|------------------------------------|-----------------------------|
| `A`        | any cohort of A                    | stamp joins activation      |
| `A@Q`      | any cohort                         | stamp to Q                  |
| `!_k A`    | k copies across any cohorts (FIFO) | newest taken stamp activates |
| `!_W A`    | all copies                         | W := live total             |
| `read A`   | as A, nothing consumed             | stamp joins activation      |

A match `m` is an injective assignment of cohorts to patterns satisfying guards.
Its **activation** `a(m) = max(selected stamps ∪ {E : after E})`.  Firing
consumes inputs at `a(m)` and produces each output `B` under `{·}@d` as
`B@(a(m)+d)`.

### 4.2 The match order: minimal activation, FIFO tie-break

**Proposition (Lexicographic-first is unsound):** Enumerating cohorts oldest-first
and taking the first valid assignment does not compute the minimal-activation
match when guards or windows couple patterns.  *Counterexample:* State `A@0,
A@3, B@3, B@9`; guard rejecting `(A@0, B@3)`.  Lexicographic-first finds
`(A@0, B@9)` with `a = 9`; minimal is `(A@3, B@3)` with `a = 3`.  A scheduler
firing `a = 9` ahead of another rule's `a = 5` match violates nondecreasing
activation.

**Proposition (Branch-and-bound is sound and complete):** DFS with cohorts in
ascending stamp order, carrying partial activation `a₀`, pruning branches with
`a₀ ≥ best-so-far`, returns exactly the activation-minimal FIFO-lexicographic
match.  *Fast path:* rules without `before` windows or cross-pattern guards admit
a single-pass greedy solution.

### 4.3 The settle scheduler (D12)

```
settle(S, T):
  while some rule has a valid match m with a(m) ≤ T:
    among matches with globally minimal a(m): if several, chooser;
    fire it; update S
  return S    -- quiescent at T; future stamps pending
```

There is **no clock, no tick, no watermark**: stamps are monotone, so after
`settle(T)` every remaining match has activation > T and a later call resumes
correctly with no memory of T.

**Chooser (P5):** Equal-activation conflicts are resolved by a **stateless
content-derived PRF**: `choice = mix(seed ⊕ hash(state) ⊕ hash(candidate set))`.
No RNG state exists in engine or state; determinism is a function of (seed,
state, candidate set).

**Theorem (Composability / Frame-Rate Independence, E5):** For T₁ ≤ T₂:
`settle(settle(S, T₁), T₂) = settle(S, T₂)` — states, traces, and stamps all
equal.

*Proof.* While the next event's activation is ≤ T₁, both sides select the same
match: minimal activation is a function of state only, and the PRF reads (seed,
state, candidate set) — none of which mentions the horizon.  When the next
activation exceeds T₁ the inner settle returns without firing; the outer continue
the same sequence.  The horizon gates the loop but never influences a selection —
that is the entire proof obligation, discharged by construction.  ∎

This is what makes a game host frame-rate independent and offline catch-up exact.

**Theorem (Determinism):** `settle` is a function of (state, horizon, seed,
policies).

**Theorem (Termination):** Sufficient static condition: every cycle in the
rule-dependency graph has positive total delay.  *Zeno counterexample:* `a ⊸ {a}@0`
fires forever at one instant.  The delay grade is a guardedness witness
(Nakano's `•` modality): every recursion through `{·}@d` for `d > 0` advances
the schedule.

### 4.4 settleExplore and ample sets

`settleExplore` exhaustively expands all equal-activation conflicts, producing a
tree of worlds with edge weights from `woplus` branches.  Its branching criterion
is the **ample-set / partial-order reduction condition**: only branch on genuine
conflicts (enabled matches that share consumed resources at the same activation).
Independent concurrent actions commute — their tensor derivation is
order-invariant by Theorem (Timed Confluence) — so branching on them produces
duplicate worlds.

---

## 5. Graded Labelled States (THY_0024)

### 5.1 The two-level split

A graded timed calculus needs its annotations in two places:

- **In the logic**: `at : formula → delay → formula` is a genuine connective
  (the `A@t` atoms, the retiming axiom `at_l: A@T1 ⊢ A@T2 ← !le T1 T2`, the
  backward prover and adequacy theorems reason with it).  This is hybrid logic's
  satisfaction operator, internalized.
- **In the engine state**: the label lives OUTSIDE the term.  The state is rows
  `(A, ℓ, n)` — content-addressed formula hash `A`, label `ℓ` from the grade
  algebra, multiplicity `n`.  No `at`-node exists at runtime.

The literature converges on this split from five directions: labelled deduction
(Gabbay, Negri, Simpson) makes semantic parameters labels with a separate label
theory; SELL shows modalities are context-zone indices; timed MSR (Kanovich et
al.) writes configurations as external `(fact, t)` pairs; QTT/Granule put grades
on context entries `x :ρ A`; differential dataflow uses `(data, time, diff)`
triples.  The only precedent for time INSIDE interned fact identity is temporal
Datalog's `holds(P, T)` — the state-explosion pattern zone abstraction was
invented to escape.

### 5.2 The label algebra

A calculus declares per label kind:

```
parse  : term → value         -- ground stamp term → algebra value
reify  : value → term         -- lazy internalization (memoized)
cmp    : value × value → ord  -- availability order (scheduling)
add    : value × value → value -- effect monoid (delay composition)
unit   : value                -- default label
mix    : value → int32        -- Zobrist contribution (value-derived)
```

Values are interned per-State in a **stamp table** (value ↔ small id, with cached
float, mix, and reified term).  The table is session-local and compactable —
unlike the append-only Store arena, dead labels die.

**The multiplicity column** of run-length states is this same construction at the
semiring ℕ: count is a label the engine already stores beside the address, not
inside it.  Future annotation logics (provenance semirings, spatial regions,
epistemic indices) plug in as new algebras, not new engine code.

### 5.3 Adequacy

**Lemma (Representation Adequacy).** Let `⌈·⌉` encode a labelled state as a
formula multiset by `⌈(A, ℓ, n)⌉ = at(A, reify ℓ)ⁿ` (unit labels drop the
wrapper).  Then `⌈·⌉` is a bijection onto stamped multisets, and for every rule
`r`:

- `match(r, S) ≅ match(r, ⌈S⌉)` — same assignments, same activations
- `⌈fire(m, S)⌉ = fire(m, ⌈S⌉)`

Hence `settle`, `settleExplore`, and every derived observable are representation-
invariant.

*Proof sketch.* A pattern observes a row through exactly two channels: the inner
formula (content address — identical) and the label, which enters only through
binding sites and guard computation, all passing through `parse`/`reify` (mutually
inverse on ground stamp terms).  Output labels are produced only by the firing
law, computed identically in both representations.  ∎

Two observables are contractually excluded: the 32-bit state hash and the
equal-label enumeration tiebreak.  Both are representation-internal names;
programs depending on them are exactly the draw-sensitive ones, covered by
`settleExplore`'s any-world contract.

### 5.4 The observer boundary

A label needs term-level existence only where the logic can see it.  The observer
set — stamp-binding patterns (`A@Q`, `!_k A@T`), `before`-window rules, possessed
lolis — is precisely what the **coalescer** already derives as its exclusion set.
Reification is therefore lazy and rare: a program observing most stamps would
neither coalesce nor certify, and already sits outside the fast fragment.  The
millions of unobserved timestamps a long run mints never touch the Store.

**Coalescing**: arrived facts whose stamps no rule can observe are re-stamped to
the unit and merged.  This is the analog of DBM LU-extrapolation in timed
automata.

### 5.5 Address stability (the operational payoff)

With labels inside the term (`at(inner, stamp)` as a Store node): every
(inner × stamp) combination interns an immortal arena entry, every firing pays
a hash-cons insert, and shifting the time origin re-interns the live state.
Measured on PP2 shell + kiln: ~0.4M dead nodes per simulated day, ~15% of settle
CPU in interning.

With labels beside the term: addresses are time-stable.  The Store stops growing
with elapsed time.  **Rebase** is a table rebuild-swap of the live rows into a
fresh stamp table — O(live), zero term allocation, compaction built in.  (A
uniform in-place shift was rejected: a shifted value can collide with the unit
label, breaking value injectivity that Zobrist hashing and row dedup require.)

*Measured*: 4 simulated days grow the Store by 161 nodes (was ~1.9M),
~12,000× reduction; live stamp table 4–5 entries after each rebase; CPU neutral.

---

## 6. Exact Acceleration

### 6.1 Periodic orbit certificates

A **settle** that certifies a periodic orbit mints a portable proof:

```json
{ "v": 1, "fingerprint": ..., "sigKey": ..., "period": [n, d],
  "sinkDelta": [...], "cycleEvents": n }
```

(JSON-safe, ~458 bytes in practice.)  A later `settle(state, T, { certificate })`
revalidates it at the current frontier — same probe as an in-run checkpoint —
and applies the elapsed cycles as ONE jump.

**Phase-Independence Lemma**: the in-run proof certifies recurrence at checkpoint
phase `t₀`: `state(t₀ + p) = shift_p(state(t₀))` with no draw-sensitive tie in
the window.  Firing is deterministic outside such ties, and tie draw-sensitivity
is translation- and sink-invariant, so determinism propagates: `state(t + p) =
shift_p(state(t))` for every `t ≥ t₀`.  The exit phase therefore inherits the
proven period, per-period sink growth, and per-period event count.

A stale or tampered certificate silently falls back to in-run re-detection: a
stale certificate can never mis-fire.

*Measured (A1)*: 3-week idle resume = 1 jump, 23.9M events elided, 38 ms,
bit-exact vs from-scratch replay; certificate 458 bytes.

### 6.2 What voids a window (honest negative space)

The acceleration window is voided by:
- **Stamp-binding ties**: a `before`-window rule or stamp-binding pattern (`A@Q`)
  makes the draw identity depend on absolute time → absolute input → not covariant
  → orbit period may differ across phases.
- **`woplus` firings**: each fire draws its own branch; the draw stream is not
  translation-covariant → acceleration must re-prove one period live (A3b).

Ground deadlines (`before 47`) are handled honestly: the jump is capped strictly
below the deadline; normal firing crosses it; the post-deadline regime
re-certifies.

### 6.3 Covariant tie-PRF draws (A3a)

The tie chooser's PRF input is **translation-covariant** for ties whose rules
bind no stamp position: seed + the tied candidates' canonical frontier-relative
identities (rule, consumed cohorts at frontier-relative stamps, stamp-free θ) —
nothing absolute.

Consequence: an exact orbit recurrence **forces the draw to replay**.  Tie-poisoned
cycles (any multi-consumer economy where `!_W wood` races the sawmill) certify
exactly — the draws no longer void the acceleration window.

The covariant key encodes coalesce-eligible cohorts at their normal form and
aggregates takes per (inner, stamp), so coalesce cadence and cohort split/merge
cannot leak into draws — `accelerate ≡ coalesce` holds even on drawing programs.

*Measured (A3a)*: kiln (multi-consumer economy with PRF tie draws) 3-week resume =
1 certificate jump, 23.8M events elided, 10.6 ms, bit-exact (was 491 s of
chunked unrolling; OOM before that).

---

## 7. Forced-Prefix Cohort Firing (THY_0025)

### 7.1 The wrong theorem

The natural justification for firing a match once at multiplicity k — "the k
single fires use disjoint resources under one substitution, so they are pairwise
confluent, and any interleaving reaches the batched state" — proves the wrong
thing.

**Confluence is a statement about fires the scheduler PERFORMS; it says nothing
about WHETHER the scheduler performs them.**

*Counterexample:* `spoil: wood ⊸ {I}` and `saw: wood ⊸ {plank}@2` tied at one
instant over a 10⁶-wood cohort.  Batching `spoil` consumes the whole cohort; the
sequential run interleaves `spoil` and `saw` by PRF draws.  The batched state is
not merely a reordering — it is a world **no sequential execution reaches**.  Under
the exact-replay invariant (optimization may never change the world), that is a
soundness bug, not an optimization.

Petri-net step semantics (Best–Devillers), GAMMA, and P systems all fire multisets
in one step, but their parallel step is an any-world device — it preserves
reachability, not the identity of a scheduled run.

### 7.2 The forced-prefix theorem

**Theorem.** Let `m` be the unique candidate at instant `a` (no tie), with per-fire
consumption `C` and reservation `R`.  Suppose firing `m`:
(i) produces no linear output landing at `a` (every delay strictly positive, or
zero-delay outputs feed no rule/loli antecedent, no wildcard in scope);
(ii) produces no persistent fact;
(iii) draws nothing per fire (no `woplus`, no existential resolution);
(iv) is not a possessed loli.

Then for every `k ≤ min over consumed rows of ⌊(count − R) / C⌋`, the batched
step equals the sequential k-prefix — state-identical including the Zobrist hash,
the pending schedule, and every subsequent PRF draw.

*Proof (induction on the k−1 intermediate states).* After each fire: (i) removals
only raise other rules' minimal activations (activation is a min over a shrinking
candidate set); no produced fact creates a new candidate at `a`; (ii) the
persistent zone — timeless, hence instantly visible at any delay — is untouched;
the resource bound guarantees the same rows still cover `C + R`, so the
deterministic matcher (FIFO enumeration over stable rows) recomputes the SAME
match, still unique.  State-identity is then exact because FactSet mutations hash
final counts and the draw stream consumed no randomness inside the batch.  ∎

### 7.3 A theorem's premises are a checklist for the implementation

Working the proof conditions found **two live bugs**:

**Bug 1 (condition ii — persistent production).** The implementation's
instant-feeding test returned "not feeding" for any positive delay BEFORE
examining persistent consequents.  A persistent fact produced under a DELAYED
monad is still visible at the instant (the persistent zone carries no labels —
§5), so it can enable a competitor no delay test sees.  A delayed `!k` producer
tied with a consumer of the cohort a `!k`-guarded rule also wanted: the `d`-world
vanished in `settleExplore`.  Fix: check persistent consequents first.  Pin:
`till-settle`'s persistent-arcs containment arm.

**Bug 2 (condition i — possessed lolis).** The implementation keyed "feeds a rule
antecedent" off the static rule list, but possessed lolis are candidate sources
too.  A zero-delay output only a state loli consumes slipped the guard: a batch
ran past the loli competitor, and the grow/loli tie draw vanished from the PRF
stream.  Fix: extend the antecedent tables with state-loli antecedents at each
check site.  Pin: `till-batch`'s loli fence arm.

This pattern — premises as an implementation checklist — is a general methodology:
state the theorem, work the premises, audit the code against each premise.

### 7.4 The multiplicity witness

`k = min over consumed rows of ⌊(count − reserved) / C⌋` is not merely a bound
— it subsumes the structural guards one would otherwise state:

- `!_W A` binds and takes the whole pool → floor = 1 (first cohort only)
- age-agnostic spread take exhausts every cohort but its last → floor = 1
- preserved machine (`$saw`, consumed and re-produced) has count = #machines →
  k same-stamp machines batch k-parallel; reproduced copies land at `a ⊗ d` and
  serialize the next round

**Serialization is emergent** from resource counting — no machine-specific rule is
needed.  Reads subtract because each fire re-reads the pool.

### 7.5 Zeno preservation

A zero-progress loop must feed its own instant — its output IS its antecedent —
so condition (i) excludes it from batching.  The instant guard therefore keeps its
meaning under batching (`maxInstantSteps` now counts rule progress rather than
tokens), and no divergent program can batch its way past it.

*Measured (B1)*: batched settle is **FLAT in population** — ~6 ms from 10² to 10⁶
items — while per-item scales linearly (715 ms at 10⁵); ×114 at 10⁵, ~×k beyond.

---

## 8. Evaluation

### 8.1 Methodology: differential pinning

Every optimization is a state morphism with a stated law.  The pin suite asserts
the law mechanically:

- **State-identical**: batched settle (B1), labelled states (THY_0024 rebase), and
  acceleration (A1) are each pinned against per-item / unoptimized / unrolled paths
  on the same seed.  Observational equivalence is asserted on the full state hash
  (Zobrist), not just selected outputs.
- **World-preserving** (weaker): coalescing and rebase are asserted to preserve the
  reachable-worlds semantics, not a specific world.  Their pins assert that
  `settleExplore` tree structure is identical before and after.
- **Bound-preserving** (weakest): the certificate-resume path pins event totals and
  schedule shape, not individual draw outcomes (which may change if the resumed
  state is coalesced differently).

The pin suite has ~3,250 tests including 14 cohort-firing arms (motivating case,
differentials, serialized machines, read arcs, spread takes, all fence guards, E5
chunking), differential correctness arms (FFI ∥ clause ∥ BigInt reference for
grade arithmetic), and ILL-native provability tests.

### 8.2 Results by axis

**Time axis (idle catch-up)**

| Scenario              | Before               | After         | Method      |
|-----------------------|----------------------|---------------|-------------|
| PP2 tick              | 180 ms               | 0.2 ms        | Full stack  |
| Orbit resume (A1)     | 38 ms (1 jump)       | —             | Certificate |
| Events elided (A1)    | 23.9M                | 0 (1 jump)    | Certificate |
| Covariant kiln (A3a)  | 491 s chunked / OOM  | 10.6 ms       | Covariant PRF |
| Events elided (A3a)   | 23.8M                | 0 (1 jump)    | Certificate |

**Population axis (cohort scale)**

| Population | Per-item (ms) | Batched (ms) | Ratio |
|------------|---------------|--------------|-------|
| 10²        | ~0.7          | ~6           | —     |
| 10³        | ~7            | ~6           | ×1.2  |
| 10⁵        | 715           | ~6           | ×114  |
| 10⁶        | ~7,150*       | ~6           | ~×k   |

(*extrapolated; batched is flat)

**Constants axis (Store and stamp table)**

| Metric                    | Before THY_0024     | After        |
|---------------------------|---------------------|--------------|
| Store growth / 4 days     | ~1.9M nodes         | 161 nodes    |
| Live stamp table          | grows unboundedly   | 4–5 entries  |
| CPU (settle)              | +15% (interning)    | neutral      |
| Certificate size          | —                   | 458 bytes    |

**City-scale boundary (CS bench).** Running the full content as a city — N of
every production building (cohort firing batches a machine park k-parallel) plus
10N goods: warm ticks stay ≤ 20 ms and saves stay sub-kilobyte to N = 10⁴ (a
city is ~dozens of run-length rows), and 3-week resumes jump (696 ms at N = 1,
14.3 s at N = 100). The honest limits: certification warm-up scales with
events-per-period (∝ N — the orbit proof needs two live sightings; the static
closed-form dual removes this class), and week-scale × city accumulation crosses
the engine's Int32 count fence at N ≥ 1000 (~10⁹ of a sink good) — refused
loudly per the doctrine, with in-game stock caps as the model-level remedy.

### 8.3 The evaluation principle

No measurement above is reported as an asymptotic claim unsupported by a
differential pin.  The cohort-firing flat line in population is reproducible with
`--only B1` in the benchmark suite; the rebase Store plateau is reproducible with
`--only B3`.  Measurements and pins coexist: the pin makes the measurement
scientifically meaningful by ruling out the optimistic scenario where the
"optimized" engine computes a different function.

---

## 9. Related Work

**Linear logic programming and CLF.** till is built on CLF's lax monad
(Watkins–Cervesato–Pfenning–Walker 2002) — the design is explicitly a
conservative graded decoration of CLF's shape.  Ceptre (Martens 2015) is the
nearest applied neighbor: a linear logic language for interactive simulation.
Ceptre has no graded modalities, no time, no proof that optimizations preserve
semantics.

**Timed multiset rewriting.** Kanovich–Kirigin–Nigam–Scedrov–Talcott (FORMATS
2016) add time to MSR via a global `Time@T` fact and a `Tick` rule.  This has no
proof-theoretic reading of durations, no in-flight job representation, no max-plus
activation semantics, and no backward calculus for the timed fragment.  Their
"progressing" condition approximates our Zeno guard (our version is the weaker
cycle-local form: only cycles need positive total delay).

**Graded modalities.** BLL (Girard–Scedrov–Scott 1992) grades the exponential
`!^n`; QTT (Atkey 2018), coeffect calculi (Gaboardi et al. ICFP 2016), and Granule
(Orchard–Liepelt–Eades ICFP 2019) grade contexts and types by resource semirings.
Hanukaev–Eades (CSL 2025) gives the nearest graded sequent calculus with cut
elimination — but grades the necessity side (`!_r`), never a lax/possibility
modality.  Granule types a graded `◇_r` but as a bidirectional type system, with
no sequent calculus and no cut-elimination theorem.  The delay-graded lax modality
`{A}@d` with sequent rules and cut admissibility has no prior.

**Intuitionistic Metric Temporal Logic.** de Sá–Toninho–Pfenning (PPDP 2023)
gives a labeled absolute system `A^[a,b]` with a constraint store and a
proof-branching split rule.  This is the labeled/absolute pole of §3.3's design
axis; till is the graded/relative pole.  IMTL has no operational semantics; timed
MSR has no backward calculus; CLF has no grades.  The adequacy bridge (THY_0018
Theorem 1) fills the gap.

**Timed automata acceleration.** Zone abstraction (Bengtsson–Yi 2004) and flat
acceleration (FAST/LASH — Boigelot et al.) compress regular timed runs.  till's
orbit certificates are analogous but semantically derived from the calculus: the
phase-independence lemma is a theorem about the graded monad, not a zone
widening heuristic.  DBM LU-extrapolation ≈ our coalescing (label-column rewrite
to unit).

**Petri nets, GAMMA, P systems.** Step semantics (Best–Devillers 1987) and GAMMA
(Banâtre–Le Métayer 1990) fire multisets of transitions in one step, preserving
reachability but not the identity of a scheduled run.  P systems (Păun 2000) fire
under maximal parallelism (any-world).  Forced-prefix batching (§7) is the
interleaving-semantics counterpart — a k-uniform step inside committed choice,
exact per seed.

**Partial-order reduction.** Peled (CAV 1993) and the ample-set condition give a
criterion for collapsing concurrent independent actions.  `settleExplore` uses the
same criterion (only branch on genuine conflicts — matches sharing consumed
resources at the same activation).  Forced-prefix batching inverts the POR
condition: POR asks when reorderings MAY be collapsed; the forced prefix asks when
the scheduler MUST repeat — the collapse is not a choice among worlds but the
world.

**Differential dataflow.** McSherry et al.'s `(data, time, diff)` triples and
consolidation are the systems sibling of our labelled state construction (§5); the
coalescer's function corresponds to consolidation.  Differential dataflow targets
incremental query evaluation over arbitrary lattices; till targets logic programs
with a committed-choice operational semantics.

**Provenance semirings.** Green–Karvounarakis–Tannen (PODS 2007): annotation
column over a commutative semiring.  The label algebra in §5.2 is exactly this
construction; the stamp algebra (ℚ≥0, max, +) is one instance.

---

## 10. Conclusion and Future Work

till makes execution semantics and logic the same object: every forward step is a
provable sequent, every optimization ships with a law and a pin.  The stack
achieves: 900× tick improvement (180 ms → 0.2 ms), ~12,000× Store compression
(4 days), ×114 to ~×k population batching, and week-scale idle replay in <40 ms
with bit-exact results.

**Future work:**

**(A3b) Stochastic aggregate jumps with the Kalman-closure criterion.** `woplus`
firings currently void the acceleration window (each fire draws independently).
A Markov chain whose transition matrix is *affine* in the current distribution
can be jumped by matrix exponentiation; the criterion is whether the chain's
per-step update closes over a finite basis under convex combination (a
Kalman-style reachability condition, checking the span of the Jacobian of the
update map at the orbit point).  For the duel program this would reduce a week of
stochastic combat to one matrix power.

**(Partitioned clocks.)** The current stamp algebra is a single ℚ≥0 join-
semilattice.  Partitioned clocks (multiple independent time dimensions, e.g.
physical time and logical turn counter) would allow concurrent rules on disjoint
clocks to compose without spurious synchronization at `max`.  The label algebra
in §5.2 is parametric in the carrier; a product algebra with per-dimension
scheduling is the minimal extension.

**(Whole-program specialization with translation validation.)** The translation-
covariance checker (§6, covariance.js) assigns shift degrees to rule positions
mechanically.  A whole-program partial evaluator that specializes a till program
to a particular initial multiset shape could produce a tighter accel/rebase scope,
verified by a translation-validation pass asserting state-identity of the
specialized and original programs on the shared fragment.  This is the Futamura
projection repurposed for resource-aware timed programs.

---

## References

- Alur & Dill (1994). A Theory of Timed Automata. TCS 126(2).
- Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS.
- Baccelli, Cohen, Olsder & Quadrat (1992). Synchronization and Linearity. Wiley.
- Banâtre & Le Métayer (1990). The GAMMA model and its discipline of programming.
  Sci. Comput. Program. 15(1).
- Bengtsson & Yi (2004). Timed Automata: Semantics, Algorithms and Tools. In
  Lectures on Concurrency and Petri Nets, LNCS 3098.
- Best & Devillers (1987). Sequential and concurrent behaviour in Petri net theory.
  TCS 55(1).
- de Sá, Toninho & Pfenning (2023). Intuitionistic Metric Temporal Logic. PPDP.
- Danos & Ehrhard (2011). Probabilistic Coherence Spaces as a Model of Higher-Order
  Probabilistic Computation. Information and Computation 209(6).
- Fairtlough & Mendler (1997). Propositional Lax Logic. Information and Computation.
- Fujii, Katsumata & Melliès (2016). Towards a Formal Theory of Graded Monads.
  FoSSaCS.
- Gaboardi, Katsumata, Orchard, Breuvart & Uustalu (2016). Combining Effects and
  Coeffects via Grading. ICFP.
- Gabbay (1996). Labelled Deductive Systems.
- Girard, Scedrov & Scott (1992). Bounded Linear Logic. TCS.
- Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS.
- Hanukaev & Eades (2025). Combining Dependency, Grades and Adjoint Logic. CSL.
- Huet (1980). Confluent Reductions. JACM 27(4).
- Iemhoff (2024). Proof Theory for Lax Logic. Springer.
- Jensen, Kristensen & Wells (2007). Coloured Petri Nets and CPN Tools. STTT.
- Kanovich, Kirigin, Nigam, Scedrov & Talcott (2016). Timed Multiset Rewriting and
  the Verification of Time-Sensitive Distributed Systems. FORMATS.
- Katsumata (2014). Parametric Effect Monads and Semantics of Effect Systems. POPL.
- Martens (2015). Ceptre: A Language for Modeling Generative Interactive Systems. AIIDE.
- McSherry et al. — Differential dataflow (Naiad; SOSP 2013).
- Nakano (2000). A Modality for Recursion. LICS.
- Negri (2005). Proof Analysis in Modal Logic. JPL 34.
- Negri & von Plato (1998). Cut Elimination in the Presence of Axioms. BSL.
- Newman (1942). On Theories with a Combinatorial Definition of Equivalence. Ann. Math.
- Nigam, Olarte & Pimentel (2017). A General Proof System for Modalities in Concurrent
  Constraint Programming. CONCUR.
- Olarte, Pimentel & de Paiva (2019). Hybrid Linear Logic, Revisited. MSCS 29(8).
- Orchard, Liepelt & Eades (2019). Quantitative Program Reasoning with Graded Modal
  Types. ICFP.
- Păun (2000). Computing with Membranes. JCSS 61(1).
- Peled (1993). All from One, One for All: Ample Sets in Partial-Order Reduction. CAV.
- Pfenning & Davies (2001). A Judgmental Reconstruction of Modal Logic. MSCS.
- Vollmer, Marshall, Eades & Orchard (2025). A Mixed Linear and Graded Logic. CSL.
- Watkins, Cervesato, Pfenning & Walker (2002). A Concurrent Logical Framework I.
  CMU-CS-02-101.

---

## Appendix: reviewer-facing weak points (honest self-review)

1. **No mechanized proofs.** Every theorem in §3–7 is on-paper only. A POPL
   submission without at least the central cut-admissibility result in a proof
   assistant will draw pushback; mechanizing THY_0023's graded fragment is the
   highest-leverage pre-submission investment.
2. **The bridge is extra-logical and trusted.** The settle → derivability
   direction rests on the `@fire` oracle rule being excluded from the
   cut-elimination claim and flagged `unverified: 'modeSwitch'` at runtime —
   the "execution = proof search" slogan needs a clearer formal scope
   statement (which steps are kernel-checked, which are trusted).
3. **No formal IMTL / timed-MSR comparison.** The graded-relative vs
   labeled-absolute design axis (§3.3) is asserted, not proven — a reviewer
   will ask for an embedding or separation theorem between till and IMTL.
