# The Delay-Graded Lax Monad: Proof Theory for Timed Multiset Rewriting

*Paper draft (TODO_0270). Source of truth for claims: THY_0018 (calculus),
THY_0019 (scheduler), THY_0022 (fenced grade algebras), THY_0023 (metatheory).
Markdown master; LaTeX (acmart) conversion is mechanical and deferred until
venue choice. Cross-system benchmark table (§8.3) pending a controlled host.*

---

## Abstract

Concurrent logical frameworks in the CLF tradition separate backward proof
search from forward multiset rewriting with a lax modality `{A}`: a proof of
`{A}` records *that* forward chaining can achieve `A`, but not *how long it
takes*. We present **till**, a sequent calculus for intuitionistic linear
logic whose lax modality is **graded by a delay** from the tropical
(max, +) dioid: availability stamps `A@t` on hypotheses combine by `max`
(a coeffect: synchronisation waits for the last input), delay grades `{S}@d`
compose by `+` (an effect: durations accumulate along a causal chain), and a
timed promotion rule stamps outputs at `max(inputs) + d`. Grade side
conditions enter the calculus as *theory premises* — object-level derivability
goals over a decidable arithmetic theory — whose partial residual `⊖` makes
illegal rule instances *unconstructible* rather than guarded.

We prove cut admissibility for the graded calculus — to our knowledge the
first cut-elimination result for a graded **lax/possibility** modality; all
published graded sequent calculi with cut elimination grade the necessity
side (`!_r`), and the state of the art for lax logic proof theory is
ungraded. We further prove identity expansion, an exact-accounting adequacy
theorem (operational stamps are the *least and only* derivable production
stamps), and a **work/makespan separation theorem**: the pure graded fragment
is a *cost* logic — rules-as-hypotheses derivability computes total
sequential work (Σ of delays) — while the max-plus *makespan* is contributed
exclusively by the stamp coeffect through the promotion rule. Time-as-grades
is therefore a genuine extension of graded lax logic, not a decoration.

Fused rules are uninterruptible *by theorem*: in-flight work is a node of the
monadic proof term, not a state token, and interruption requires explicit
fission. The scheduler that realises the promotion rule is deterministic and
frame-rate independent (`settle(settle(S,T₁),T₂) = settle(S,T₂)`), and serves
the prover as a *sound oracle* whose every step is a derivable promotion
instance. All results are witnessed by an executable artifact: a
kernel-verified prover, an executable specification suite, and differential
fuzz harnesses over exact rational arithmetic.

---

## 1. Introduction

### 1.1 The gap

The Concurrent Logical Framework (CLF) [Watkins et al. 2002] marks the
boundary between backward proof search and committed-choice forward chaining
with a lax modality `{A}`, following the judgmental reconstruction of lax
logic [Fairtlough–Mendler 1997; Pfenning–Davies 2001]. The modality is
ungraded: a CLF derivation of `{A}` certifies reachability and nothing more.

Quantitative refinements of linear logic are by now standard — but on the
**necessity** side. Bounded linear logic [Girard–Scedrov–Scott 1992], the
coeffect calculi, quantitative type theory [Atkey 2018], Granule
[Orchard–Liepelt–Eades 2019], and a current line of graded sequent calculi
[Moon–Eades–Orchard 2021; Vollmer–Marshall–Eades–Orchard CSL 2025;
Hanukaev–Eades CSL 2025] all grade the exponential `!_r A`, and there cut
elimination is settled. Graded *monads* are equally standard in semantics
[Katsumata POPL 2014; Fujii–Katsumata–Melliès 2016] — as categorical
structure, with no sequent calculus. Granule types a graded possibility
`◇_r` — as a bidirectional type system, with no proof theory. For the lax
modality itself, the sharpest recent result is cut elimination and uniform
interpolation for *ungraded* propositional lax logic [Iemhoff 2024]. To our
knowledge **no published system gives a sequent calculus with cut
elimination for a graded lax, monadic, or possibility modality** (novelty
sweeps 2026-08-18 and 2026-08-21; §9).

Meanwhile, *time* in multiset rewriting is operational folklore: timed MSR
[Kanovich et al. FORMATS 2016] threads a global `Time@T` fact with a `Tick`
rule; Coloured Petri Nets [Jensen et al. 2007] stamp tokens and delay
outputs with exactly the operational surface we want — and no proof theory.
Temporal session types [Das–Hoffmann–Pfenning ICFP 2018] put discrete-time
`◯` on channel types for complexity analysis; intuitionistic metric temporal
logic (IMTL) [de Sá–Toninho–Pfenning PPDP 2023] labels propositions with
absolute intervals and proves cut elimination — with additive label
arithmetic and a constraint store, and no resource multisets.

This paper closes the square: **time enters CLF-style forward chaining as a
grade**, with the proof theory done properly.

### 1.2 Contributions

1. **The calculus** (§3). ILL plus stamped atoms `A@t` and a delay-graded
   lax modality `{S}@d`, in judgmental presentation: `Γ; Δ ⊢ A true` and a
   graded lax judgment `Γ; Δ ⊢ S lax@d`. One tropical algebra plays two
   roles: durations compose by `+` in the graded bind; availability stamps
   combine by `max` in a timed promotion rule `@fire` whose side condition
   is the dioid action `t ⊳ d = t + d`. The calculus is parametric in an
   ordered-monoid/semilattice/action triple; the tropical instance is the
   timed one.

2. **Grade side conditions as theory premises with a partial residual**
   (§3.4). Rules carry object-level derivability premises over a decidable
   arithmetic theory (`⟨– !qsub F E H⟩`: "H is the residual F ⊖ E"). The
   residual is *partial* — no proof exists when `F < E` — so fences like
   "grades never go negative" are not side conditions but *Grade
   Preservation by construction*: no rule, present or future, can build an
   invalid grade. This is CLP-style constraint discharge
   [Lassez–McAloon 1990] meeting geometric-rule cut elimination
   [Negri–von Plato 1998], with output variables disciplined exactly as
   properly-oriented extra variables in deterministic 3-CTRSs [Ohlebusch].

3. **Metatheory** (§4). Cut admissibility for the graded calculus (three
   cuts: linear, persistent, and a graded lax cut composing `d + e`),
   identity expansion, and completeness of the counted-exponential rules.
   Two structural observations with independent interest: the count fence
   `ℕ` is precisely what makes the cut measure well-founded, while the
   *dense* delay grades never enter the measure; and mismatched principal
   cut cases are *vacuous* by premise partiality — the partial residual
   deletes proof obligations rather than adding them.

4. **Adequacy, in both directions, with exact accounting** (§6).
   *Exactness:* an execution's residual is derivable, and a produced token's
   operational stamp is the least — and only — derivable production stamp
   (grade weakening lives on the monad, stamp weakening on hypotheses;
   production claims admit neither). *Work adequacy* (non-circular, no
   oracle in the proof path): encoding program rules as linear hypotheses,
   pure backward derivability of `{⊗R}@W` holds iff `W` bounds the
   execution's **total work** Σdᵢ. *Separation:* the pure graded fragment
   cannot express the max-plus **makespan** — on a two-branch join with
   delays 2, 3 then 1, the least pure-derivable grade is 6 while the
   scheduler's stamp is 4. The lax grade is sequential cost; parallelism is
   exactly what the stamp coeffect adds.

5. **Processes as proof terms; atomicity as a theorem** (§7). A firing with
   delay d occupies the open interval (a, a+d) in which *no* rule can
   consume or observe its effects: fused rules are uninterruptible by
   construction, and fission into `start`/`end` rules — related to the fused
   rule by cut elimination on the fresh intermediate — is the *honest model*
   of interruptible work. The timed trace is the graded monadic proof term;
   its settled prefix prunes to a hash accumulator (engineering corollary).

6. **A deterministic scheduler as a sound oracle** (§5, §6.3). `settle`
   fires activation-minimal matches (lexicographic-first is *unsound*; we
   give the counterexample and a branch-and-bound match that is sound and
   complete) and satisfies the composability law
   `settle(settle(S,T₁),T₂) = settle(S,T₂)` — frame-rate independence for a
   logic-based engine. The prover uses settle as an oracle rule: each step
   is a derivable `@fire` instance, so oracle success implies derivability
   (soundness); the converse fails and is not claimed.

7. **Artifact** (§8). An implementation in the CALC proof calculus sandbox:
   backward prover with an independent proof-checking kernel (pure
   derivations fully verified; oracle steps disclosed as unverified),
   executable specification suite, and three differential fuzz harnesses
   (FFI ∥ clause ∥ bignum-reference; scheduler ∥ oracle; random monad
   towers, kernel-checked). Exact rational time throughout.

### 1.3 Non-claims

The oracle is sound, not complete (§6.3); its steps are checked structurally
by the kernel and reported as unverified — trust in a bridge derivation
reduces to trust in the scheduler, by design and disclosed. All proofs are
on paper, none machine-checked; the mechanisation is future work. The
probabilistic grade on the weighted additive disjunction (a second axis in
the implementation) has operational semantics but no sequent rules here — it
needs a probabilistic judgment and is a separate paper.

---

## 2. The grade algebra: one tropical dioid, two roles

Fix the tropical dioid `𝕋 = (ℚ≥0, max, +)`. Its fragments:

- **Durations (effect)** `D = (ℚ≥0, +, 0, ≤)`, an ordered commutative
  monoid: delays compose along causal chains.
- **Time points (coeffect)** `T = (ℚ≥0, max, 0, ≤)`, a join-semilattice:
  stamps synchronise at a tensor of inputs — wait for the last.
- **The action** `⊳ : T × D → T`, `t ⊳ d = t + d`, monotone in both
  arguments, with `t ⊳ 0 = t`, `(t ⊳ d) ⊳ e = t ⊳ (d+e)`, and
  `max(t,t') ⊳ d = max(t ⊳ d, t' ⊳ d)` — the last being precisely the
  semiring distributivity of `𝕋`.

Every proof in this paper uses only these laws; the calculus is parametric
in any such (D, T, ⊳) triple (§9 discusses instances). Stamps are absolute
points, delays relative translations — the effect/coeffect pairing is the
*trivial* matched pair in the sense of [Gaboardi et al. ICFP 2016]; the
substantive interaction is not their distributive law σ but the action `⊳`
inside the promotion rule, structure their framework does not supply.

**Fenced grade algebras.** Grades live inside a *fence* (validity predicate)
V with a *partial residual*: `a ⊖ b` is the `h ∈ V` with `b + h = a`,
undefined when none exists. till's instances: delays (`V = ℚ≥0`,
`⊖` defined iff `a ≥ b`), counts (`V = ℕ`), weights (`V = [0,1]`,
multiplicative, no residual needed — a theorem of its signature). V is
closed under the exposed operations, which yields:

**Theorem 2.1 (Grade Preservation).** If every grade literal in a program
satisfies its fence and rules construct grades only through `+` and `⊖`,
every grade in every reachable state — forward execution and backward search
alike — satisfies its fence. Per-rule guards (`F ≥ E`, `K ≥ 1`) are derived
lemmas, not stated conditions; the force of the theorem is quantification
over *future* rules. ∎ (Proof: induction over firings; THY_0022.)

The residual is the graded analogue of an Iris resource algebra's validity
[Jung et al. 2018] and a residuated commutative monoid [Galatos et al. 2007]
restricted to its valid cone. We deliberately do *not* adopt the clamping
monus (`a ∸ b = 0` when `b ≥ a` [Amer 1984]): a too-late resource must make
a rule inapplicable, not free.

---

## 3. The calculus

### 3.1 Syntax and judgments

Formulas: ILL (`⊗, ⊸, 1, &, !`) extended with **stamped atoms** `a@t`
(`t ∈ T`; `@` attaches to atoms only), **counted exponentials** `!_k A`
(`k ∈ ℕ`), and the **graded lax monad** `{S}@d` (`d ∈ D`; bare `{S}`
abbreviates `{S}@0`), `S` ranging over the synchronous fragment as in CLF.

Judgments, with the lax judgment graded:

- `Γ; Δ ⊢ A true` — A holds of persistent context Γ and linear context Δ.
- `Γ; Δ ⊢ S lax@d` — S is *achievable* from Γ; Δ within delay bound d
  (relative to the availability of the consumed resources; stamps make it
  absolute in §3.3).

### 3.2 The graded lax fragment

```
Γ; Δ ⊢ S true                    Γ; Δ ⊢ S lax@d    d ≤ d'
───────────────  lax             ─────────────────────────  sub
Γ; Δ ⊢ S lax@0                   Γ; Δ ⊢ S lax@d'

Γ; Δ ⊢ S lax@d                   Γ; Δ, S ⊢ C lax@e
─────────────────  {}R           ────────────────────────────  {}L
Γ; Δ ⊢ {S}@d true                Γ; Δ, {S}@d ⊢ C lax@(d + e)
```

`lax` is the unit: what is true now is achievable with zero delay. `{}L` is
CLF's *sticky* left rule with grade composition — eliminating `{S}@d` inside
a lax goal adds d to the bill; it fires only under a lax conclusion, so
grading rides the existing modal discipline. `sub` is subeffecting: the
grade is an upper *bound*, and the operational stamp will be its least
solution (§6.1). Left rules of the ILL fragment are generic in the
conclusion judgment. Erasing grades yields exactly the judgmental lax
fragment of [Pfenning–Davies 2001] — CLF's discipline; the calculus is a
conservative decoration of it, and its proof theory (Theorem 4.2) is the
graded extension of [Iemhoff 2024].

Derived: graded μ `{{S}@d}@e ⊢ {S}@(d+e)`; functoriality; unit `S ⊢ {S}@0`.
The μ law is the critical-path reading of `+`: a CLF monadic let-chain
accumulates the sum of its step grades.

**Counted exponentials.** `!_k A` is k linear parcels (`A^⊗k`), in the
SELL/BLL tradition, with four rules (left peel/weaken, right peel/zero)
whose side conditions are arithmetic over ℕ (`k = j+1` resp. `k = 0`).
Completeness of the four rules for the `A^⊗k` reading is Theorem 4.4. The ω
exponential `!A` keeps ILL's promotion/dereliction/absorption, disjoint from
the counted grades.

### 3.3 Stamps and timed promotion

Stamps are the coeffect. Three laws with deliberately different standings:

- **Retiming** (the one sequent rule; axiom): `Γ; a@t ⊢ a@t' true` for
  `t ≤ t'` — delaying availability is free, never early. The coeffect
  mirror of `sub`.
- **Ambient** `a ≡ a@0` is a canonicalisation convention at the state
  boundary, *not* a rule: inside the calculus `a ⊬ a@t` for every t
  (admitting `a ⊢ a@0` would compose with retiming into stamp forgery).
  Stamps are born at the boundary, moved only by retiming.
- **Monoidal** `(A ⊗ B)@t ≡ A@t ⊗ B@t`, `1@t ≡ 1` is a meta-level law of
  the state representation (compound stamped formulas are not syntax); its
  sequent shadow is derivable pointwise.

The rule tying stamps to grades is a **promotion rule** in the SELL style —
a global condition on the context, not a local left rule:

```
Γ; A₁, …, Aₙ ⊢ S lax@d         a = max(t₁, …, tₙ, 0)
──────────────────────────────────────────────────────  @fire
Γ; A₁@t₁, …, Aₙ@tₙ ⊢ S@(a ⊳ d) lax@0
```

Reading: the body promises S within d of its inputs; the inputs synchronise
at `a` (coeffect `max`); the outputs exist from `a + d` (action); the lax
grade *resets* — the effect is fully internalised into stamps. Boundary
cases: `n = 0` gives `S@d lax@0` ("the delay grade is the stamp of the
future"); `d = 0` with zero stamps is ordinary untimed firing. Activation
windows (`after E` strengthens `a`; `before E` bounds it) are scheduling
annotations on this rule, not connectives. Persistent hypotheses carry no
stamps; the interaction of `ω` with time is future work.

In the implementation `@fire` is realised as an *oracle* rule (§6.3), which
keeps the pure calculus's metatheory clean: cut elimination is about the
syntactic system; the oracle only ever asserts sequents that are already
derivable.

### 3.4 Grade side conditions as theory premises

The implemented calculus is single-level (one judgment; `S lax@d`
represented as `{S}@d` — the equivalence is Theorem 4.1), and its rules
carry **theory premises**: object-level goals over a decidable arithmetic
theory, discharged during rule application and re-checked by the proof
kernel. The two monad rules:

```
monad_l:  Γ; Δ, {A}@E ⊢ {C}@F   ⟵   Γ; Δ, A ⊢ {C}@H     ⟨– !qsub F E H⟩
monad_r:  Γ; Δ ⊢ {A}@E          ⟵   Γ; Δ ⊢ A            ⟨– !le 0 E⟩
```

`!qsub F E H` derives "H is the residual F ⊖ E": it *binds* the output
variable H when `F ≥ E` and has **no derivation** when `F < E` — the rule is
then simply inapplicable. No guard `F ≥ E` is stated anywhere; the fence is
derivational (Theorem 2.1). Variables not bound by the conclusion are output
variables, bound by the derivation — the exact discipline of properly
oriented extra variables in deterministic 3-CTRSs [Ohlebusch], transported
from rewriting to proof theory.

Two published lineages meet here. The premises are CLP-style constraint
goals in the sense of the constraint sequent calculus
[Lassez–McAloon LICS 1990], living object-level in the rules. And they are
*geometric*: the residual axiom `∀F,E. (F ≥ E ⊃ ∃H. F = E + H)` is a
geometric implication, so by [Negri–von Plato 1998] building it into the
rules preserves cut eliminability — in our direct proof (§4) this
materialises as the observation that theory premises carry no sequent-level
principal formula and therefore never obstruct a permutation. Unlike Twelf's
constraint domains (which cannot appear in dynamic assumptions — exactly
where ours live) and unlike deduction modulo (congruence, not functional
discharge; cut elimination conditional on super-consistency), our premises
are decidable derivability goals with functional output binding, and cut
elimination is unconditional.

---

## 4. Metatheory

Full proofs: THY_0023. We state the results and the load-bearing points.
Throughout, "the calculus" is the pure syntactic system (id, the ILL rules,
ω-bang, counted bangs, `lax/sub/{}R/{}L`, retiming, copy); the oracle rule
is excluded by scoping (§6.3).

**Theorem 4.1 (presentation equivalence).** The judgmental two-level system
and the implemented single-level system derive the same sequents, with
cut-free derivations mapping to cut-free derivations both ways,
size-linearly. The glue: a `{}`-inversion lemma (`{S}@d true` yields
`S lax@d`) and admissible grade weakening in the single-level system —
`sub` needs no primitive rule there because subeffecting lives in
`monad_r`'s slack and `monad_l`'s residual freedom. ∎

**Theorem 4.2 (cut admissibility).** The three cuts

```
Γ; Δ ⊢ A true    Γ; Δ', A ⊢ J            Γ; Δ ⊢ S lax@d    Γ; Δ', S ⊢ C lax@e
────────────────────────────── cut       ───────────────────────────────────── cut_lax
Γ; Δ, Δ' ⊢ J                             Γ; Δ, Δ' ⊢ C lax@(d + e)

Γ; · ⊢ A true    Γ, A; Δ ⊢ J
────────────────────────────── cut!
Γ; Δ ⊢ J
```

are admissible in the cut-free calculus. *Proof.* Lexicographic induction on
(cut-formula weight, cut kind with `cut! ≻ cut_lax ≻ cut`, the premise
derivations). The principal `{}R`/`{}L` case reduces a true-cut on `{S}@d`
to exactly `cut_lax` with grades composing as `d + e` — the same composition
`{}L` performs, no new arithmetic. `cut_lax` analyses the left derivation:
the `lax` case drops to `cut` with the unit law `0 + e = e`; `sub` commutes
by monotonicity (`d₀ ≤ d ⟹ d₀+e ≤ d+e`); `{}L` re-associates
(`d' + (d₀ + e) = (d' + d₀) + e`). The only grade facts used are the
ordered-commutative-monoid laws — the proof is parametric in the algebra
exactly as the calculus is. Retiming cuts compose by transitivity of `≤`.
Counted-bang principal cases use functionality of the residual
(`J = J' = K−1`), and the mismatched pairings (peel against zero) are
**vacuous**: their theory premises demand `K ≥ 1` and `K = 0`
simultaneously, so no such pair of derivations exists — partiality deletes
case obligations. ∎

Two structural remarks worth the reader's attention:

- **The fence is the measure.** Counted bangs enter the termination measure
  as `w(!_K A) = (K+1)(w(A)+1)`, well-founded *because* the count fence is
  ℕ. The delay grades — dense in ℚ≥0 — never enter the measure: every
  monad-cut descends to the body. Cut elimination is measure-blind to
  exactly the grade that is dense. The fence (Theorem 2.1) is not
  bookkeeping; it is the induction principle.
- **No erasure lift.** THY_0018's original sketch routed through grade
  erasure onto the ungraded lax fragment. The direct proof does not: the
  graded system is proved outright, and the erased proof re-emerges as its
  shadow under grade deletion.

**Theorem 4.3 (identity expansion).** For every formula with ground grades,
`Γ; A ⊢ A` is derivable with axioms only at atoms (`id` at unstamped atoms;
retiming with reflexive `t ≤ t` at stamped atoms). For non-ground (pattern)
grades the primitive general identity remains necessary — symbolic-grade
identity is axiomatic, ground-grade identity admissible. ∎

**Theorem 4.4 (counted-bang completeness).** For ground `k ∈ ℕ`,
`!_k A ⊣⊢ A^⊗k` with the four counted rules; with Theorem 4.2, a sequent is
provable in the counted reading iff its expansion is provable in the
bang-free fragment. The split/merge iso `!_{a+b} A ⊣⊢ !_a A ⊗ !_b A`
follows. ∎

**Corollary 4.5.** Consistency; the analytic subformula property up to
grade recomputation (every formula in a cut-free derivation is a subformula
of the end-sequent with grades produced by `+`/`⊖` from end-sequent
grades); and admissibility of the compositions used by the adequacy and
fusion theorems below — they never leave the cut-free calculus.

---

## 5. Operational semantics: timed matching and settle

A till program is a set of rules `In ⊸ {Out}@d`; a state is a **timed
multiset** — a finite map (atom, stamp) → count; equal-stamp copies merge
into cohorts. A **match** m assigns cohorts to pattern atoms (with counted
patterns `!_k A` taking k copies across cohorts and `!_W A` binding a whole
cohort at firing time); its **activation** is the max-plus linear form
`a(m) = max(selected stamps ∪ after-bounds)`, valid iff below every
`before`-bound. Firing consumes at `a(m)` and produces each output stamped
`a(m) + d` — one `@fire` instance.

```
settle(S, T):  while some rule has a valid match m with a(m) ≤ T:
                 among globally minimal a(m) (ties: stateless PRF chooser);
                 fire it (consume at a(m), produce at a(m)+d)
               return S            -- quiescent at horizon T
```

There is no clock, no tick, no watermark: stamps are monotone, so `settle`
resumes correctly after any horizon with no memory of it.

**Proposition 5.1 (lexicographic-first is unsound).** Per-pattern
oldest-first matching with backtracking does not compute the
activation-minimal match when guards couple patterns. *Counterexample:*
state `A@0, A@3, B@3, B@9`, a guard rejecting exactly `(A@0, B@3)`:
lexicographic-first finds activation 9; the minimum is 3. Firing the 9-match
ahead of another rule's 5-match violates nondecreasing activation. A
branch-and-bound search over stamp-sorted cohorts, pruning on the partial
`max`, is sound and complete (activation is monotone in partial
assignments), and degrades to one greedy pass exactly when no guard or
window couples two patterns — the common case costs what untimed matching
costs. ∎ (THY_0019 Props. 1–3.)

**Theorem 5.2 (determinism and composability).** `settle` is a function of
(state, horizon, seed, policies), and for `T₁ ≤ T₂`:
`settle(settle(S,T₁),T₂) = settle(S,T₂)` — states, traces, stamps all
equal. The proof obligation is precisely that no selection ever reads the
horizon: minimal activation is a function of the state; equal-activation
ties are resolved by a *stateless* content-derived PRF
(`mix(seed ⊕ hash(state) ⊕ hash(candidates))`). The law is frame-rate
independence: a game host that jumps the horizon replays exactly the
history a small-stepping host would have produced. ∎ (THY_0019 Thms. 4–5.)

**Theorem 5.3 (termination / Zeno guard).** `settle(S,T)` terminates iff
finitely many events have activation ≤ T; sufficient statically: every
cycle in the rule-dependency graph has positive total delay (each traversal
advances activation). `a ⊸ {a}@0` from `a@0` is the Zeno counterexample;
with `@1` the same rule is productive — the delay grade as a guardedness
witness in the sense of Nakano's `▷`. Off-cycle zero-delay rules are fine —
a strictly weaker condition than timed MSR's global progressing condition. ∎

---

## 6. Adequacy

Three results, in increasing order of what they refuse to assume.

### 6.1 Exactness (operational stamps are the only production stamps)

**Theorem 6.1.** Let `R = settle(Δ, T)` be the residual of an
activation-ordered conflict-free execution (ground grades, exact
accounting). Then:

1. *(Soundness)* `Γ; Δ ⊢ {⊗R}@T` is derivable — the execution *is* a
   derivation: each firing is one `@fire` instance, and composing the chain
   requires one `{}L` residual per step, each *defined* because activation
   order keeps the budget above the spent delay. The argument appeals only
   to the residual's intrinsic partiality — never to which other rules
   exist — so it is stable under rule-set extension.
2. *(Exactness)* for a token `b@u ∈ R` produced by the execution, the claim
   `Γ; Δ ⊢ {b@u'}@T'` is derivable **iff** `u' = u`: the operational stamp
   is the least — and *only* — derivable production stamp. A claimed stamp
   below the max-plus critical path makes some residual along the
   derivation undefined; a stamp above it is blocked because the calculus
   deliberately omits stamped-claim weakening.
3. *(Where weakening lives)* hypothesis-side only for stamps
   (`b@t ⊢ b@t'` iff `t ≤ t'`, retiming) and monad-side only for grades
   (`S ⊢ {S}@E` for `E ≥ 0`, subeffecting). ∎ (THY_0018 Thm. 1; the
   `b@(u+1)` refutation clause was found by the fuzzer against an earlier
   wrong sketch that claimed production-stamp weakening.)

Stamps are max-plus polynomial evaluations; the scheduler evaluates them,
the logic pins them exactly.

**Theorem 6.2 (timed confluence).** Conflict-free executions (no two
enabled matches sharing a consumed cohort; read arcs exempt) have
order-independent residuals: the event DAG is unique, a token's stamp is
its max-plus path weight, and firing orders are linearisations — CLF's
concurrent equality with stamps as a permutation invariant. ∎

### 6.2 Work adequacy and the separation theorem

Theorem 6.1's soundness direction runs *through* the promotion rule. The
following is the adequacy the pure calculus supports with no oracle at all —
and it isolates what the graded monad alone measures.

Encode a program's rules as **linear hypotheses** with multiplicities as
counted bangs: for an execution ε from unstamped Δ₀ with firing multiset n
and residual R, let `Δ_ε = Δ₀ ⊎ {!_{n(Rᵢ)}(Inᵢ ⊸ {Outᵢ}@dᵢ)}`.

**Theorem 6.3 (work adequacy).** `·; Δ_ε ⊢ {⊗R}@W` is derivable in the
pure calculus **iff** some execution from Δ₀ with firing multiset n reaches
residual R and `W ≥ Σᵢ n(Rᵢ)·dᵢ` — the **total sequential work**. The ⇐
direction replays the execution as peel/`⊸L`/`{}L` steps (every proof tree
fully kernel-verified in the artifact, no oracle steps); the ⇒ direction is
the CLF adequacy permutation argument plus a telescoping residual chain:
linearity forces every rule copy to fire and every monadic output to be
opened, charging its delay exactly once. ∎ (THY_0023 Thm. 10.)

**Theorem 6.4 (work/makespan separation).** The pure grade measures work,
not makespan. Join program `{a ⊸ {x}@2, b ⊸ {y}@3, x⊗y ⊸ {c}@1}` from
`{a, b}`: least pure-derivable W is `6 = 2+3+1` (`{c}@5`, `{c}@4` refuted),
while settle produces `c@4` (`max(2,3)+1`). The readings coincide exactly
when the firing DAG is a chain. Moreover stamped inputs are *outside* the
pure encoding entirely (`a@t ⊬ a` — stamps are born at the boundary).
**Consequently: the delay-graded lax monad alone is a cost logic —
sequential composition of delays; max-plus synchronisation is contributed
exclusively by the stamp coeffect through `@fire`.** Time-as-grades is a
genuine extension of graded lax logic, and the bridge-soundness theorem
below is exactly the statement that the extension is consistent. ∎
(THY_0023 Thm. 11; both columns pinned by test.)

### 6.3 The oracle rule (bridge soundness)

The implementation realises `@fire` as an admissible **oracle rule**: for a
goal `Γ; Δ ⊢ {S}@T` the prover may run `settle(Δ, T)` — reading the
succedent grade as the observation horizon — and then prove S against the
residual timed multiset by the pure calculus (retiming + decomposition +
identity).

**Theorem 6.5 (oracle soundness).** If the oracle succeeds,
`Γ; Δ ⊢ {S}@T` is derivable: each settle step is an `@fire` instance
(Theorem 6.1's compositionality), and the residual match is an ordinary
derivation. The **converse is false and not claimed**: `sub` derives
`a ⊢ {a}@d` for every `d ≥ 0` with no forward step, so derivability does
not imply settle-reachability. The implemented prover searches both the
pure calculus and the oracle, so *prover* failure refutes the sequent;
oracle failure alone refutes only the oracle route. ∎

Kernel checking of an oracle step is structural: the settle run is trusted
and *disclosed* — the checker reports it as an unverified step, and "fully
verified" is reserved for pure derivations. All Stage-1 results (§4) and
all of Theorem 6.3's derivations meet full verification; Theorem 6.1's
bridge derivations are verified modulo the disclosed oracle step, by
design.

---

## 7. Processes as proof terms: Fusion = Atomicity

**Theorem 7.1 (Fusion = Atomicity).** (a) *Atomicity of fused rules.* For a
firing at activation a with delay d, inputs are consumed at a and every
output carries stamp `a + d`; any match involving an output — consuming
*or reading*, since read stamps join the activation max — has activation
`≥ a + d`. The open interval `(a, a+d)` admits no interaction with the job:
fused rules are uninterruptible by construction. (b) *Fission.* Replacing
`fused = In ⊸ {Out}@d` by `start = In ⊸ {J}@0`, `end = J ⊸ {Out}@d` (J
fresh) is observationally equivalent on J-free observables with identical
stamps: `start; end` composes by graded μ (`0 + d = d`), and fusion is cut
elimination on J — the grade `@d` is what remains of the cut.
(c) *Corollary.* An interruptible process **must** be fissioned: the
mid-flight resource (`constructing(house)`) is the honest model of a job
the world can touch. Observability never requires fission — the job is
visible as a node of the trace; only *interaction* does. ∎ (THY_0018
Thms. 3+5, merged; the isolation argument of (a) is the proof technique
for the headline law (b).)

**Read arcs.** `read A` joins the activation max, consumes nothing, and
re-emits the token bit-identically with its original stamp; in
conflict-free activation-ordered executions original-stamp and
activation-stamp conventions are observationally equivalent (a scheduler
property transferring to the logic through Theorem 6.1), and the
original-stamp choice makes re-emission a state no-op. Concurrent
same-instant reads do not conflict — a consume-and-reproduce encoding would
falsely serialise them.

**Trace ≅ term (observation, with an engineering corollary).** The flat
step log (rule, θ, a, d in firing order) and the CLF monadic proof term
(the let-chain) are two presentations of one object; the stamps make the
concurrency partial order explicit, and the log is its canonical
policy-fixed linearisation. This identification is CLF's design; what is
new is only the per-node stamp and the canonicality inherited from
Theorem 5.2. *Corollary (engineering level, presented as such):*
reassociating the term as an event snoc-list lets a running system prune
the settled past into a hash accumulator `Hₖ = hash(Hₖ₋₁, evₖ)` — O(1)
history storage that still cryptographically commits to the full trace;
what pruning preserves is exactly the commitment, nothing else.

---

## 8. Implementation and evaluation

### 8.1 The artifact

till is implemented in CALC, a proof-calculus sandbox with a
content-addressed formula store (formulas are hashes; O(1) equality).
Components: the backward focused prover over the declarative rule file
(template rules with theory premises; the arithmetic theory is itself a
logic program over exact rationals, with an FFI decision-procedure face as
an optimisation — *theory is semantics, FFI is optimisation*: every FFI
predicate has clause definitions, and a no-FFI mode runs the entire test
surface on the clause face alone); the independent proof-checking kernel
(re-derives every step including theory premises, re-threads linear
resource accounting, rejects context-leaking forgeries; oracle and
eigenvariable steps disclosed in an `unverified` report); the timed
scheduler (branch-and-bound minimal-activation matching, stateless PRF
chooser); and a TTY shell for live timed programs.

### 8.2 Executable metatheory

- **Provability grid**: the §4 fragment as ~90 pinned provable/refuted
  sequents, every proof kernel-verified with zero unverified steps.
- **Adequacy suites**: executable specifications whose `#expect` gates are
  wrapped as sequents (Theorem 6.1 soundness + refutations; Theorem 7.1 as
  (under)derivability); the pure work-adequacy suite (Theorem 6.3/6.4, no
  oracle in any proof path, oracle column cross-checked against a
  from-the-spec reference implementation).
- **Differential fuzzing**: (1) grade arithmetic three ways — FFI ∥ clause
  resolution ∥ BigInt reference — including residual definedness; (2)
  scheduler vs the executable reference semantics; (3) random monad towers
  `{…{a}@d₁…}@dₙ ⊢ {a}@f` against the Σd oracle, plus retiming and
  production-claim exactness on random one-rule programs — every success
  kernel-verified. The exactness clause of Theorem 6.1 was *corrected by
  this harness* (an earlier sketch wrongly admitted production-stamp
  weakening; the fuzzer found the counterexample) — we consider this the
  strongest argument for executable metatheory as a paper artifact.

### 8.3 Case studies and benchmarks

Two case studies exercise the full surface: a delay-scheduled economy
(activation windows, spoilage races, counted parcels) and a weighted duel
(the probabilistic axis, out of scope here). The internal baseline and the
measurement protocol (state sizes, horizon sweeps, match-search stress with
coupled guards) are fixed in the artifact; the cross-system table against
Real-Time Maude, CPN Tools, and Ceptre requires those tools' hosts and is
**pending** — reviewers should read §8 as artifact-functionality evidence,
not comparative performance claims, until that table lands.

---

## 9. Related work

| ingredient | nearest neighbour | delta |
|---|---|---|
| lax modality, sequent rules, cut elim | Fairtlough–Mendler 1997; Pfenning–Davies 2001; CLF; **Iemhoff 2024** (cut elim + uniform interpolation, ungraded) | ungraded — we add the grade and keep the shape; Thm 4.2 is the graded extension of the 2024 result |
| graded monads (semantics) | Katsumata 2014; Fujii–Katsumata–Melliès 2016 | categorical; no sequent calculus |
| graded NECESSITY, sequent proof theory | BLL 1992; Moon–Eades–Orchard 2021; **Vollmer–Marshall–Eades–Orchard CSL 2025** (mixed linear/graded sequent calculus, graded comonad); Hanukaev–Eades CSL 2025; GRASS 2026 | all grade `!_r`; no graded lax/possibility sequent calculus anywhere |
| graded POSSIBILITY | Granule's `◇_r` (ICFP 2019) | type system only; the proof theory of `{S}@d` is precisely the missing piece |
| effect–coeffect interaction | Gaboardi et al. 2016 | our pair is their trivial case; the timed content is the `⊳` action inside promotion |
| timestamps in MSR | Kanovich et al. FORMATS 2016 (+ 2024 resilience line) | global clock fact + Tick; no max-plus activation, no in-flight representation; their progressing condition ≈ our Zeno guard, globally where ours is cycle-local |
| metric time, labelled sequents | **IMTL, de Sá–Toninho–Pfenning PPDP 2023** | the labeled/absolute pole: interval labels `A^[a,b]`, constraint store Ω, delay/□/◇ rules compute labels **additively** (`[a+∂₁, b+∂₂]`; fresh constrained variables for uncertainty — verified against §2.4–2.6 of the paper) and **no rule computes a residual**. till is the graded/relative pole: label-free judgments, one partial `⊖`. The axis is *residuation vs accumulation* — residuation is the price of internalising time as grades (THY_0022) |
| timed tokens, arc delays | CPN Tools; timed-arc / time Petri nets; timed automata | identical operational surface, no proof theory; our windows need no clocks because the timeline lives in the stamps |
| time in linear type systems | Das–Hoffmann–Pfenning ICFP 2018 | discrete `◯` on channel types for complexity; no graded lax modality over multisets, no ℚ delays, no tropical activation |
| (max,+) systems theory | Baccelli et al. 1992 | the algebra and its eigenvalue theory, imported; not connected to logic |
| in-flight = proof-term node | event structures (NPW 1981) | the let-node identification and atomicity-as-theorem are ours |
| constraint side conditions | Lassez–McAloon 1990; Negri–von Plato 1998; Ohlebusch 3-CTRS; Twelf constraint domains; deduction modulo | see §3.4 — object-level decidable theory premises with functional output binding in dynamic assumptions; unconditional cut elim |

Novelty was stress-tested adversarially (three sweeps, 30+ papers, the
last on 2026-08-21 covering CSL/LICS/POPL/FSCD/ESOP 2024–26): no published
system gives a sequent calculus with cut elimination for a graded lax,
monadic, or possibility modality; no system embeds max-plus activation in a
promotion rule; no graded modal system has operationally partial grade
subtraction (Granule's subtraction exists only inside static SMT
constraints — failure is a type error, never rule inapplicability). The
claims are stated with these boundaries.

---

## 10. Conclusion

Grading CLF's lax monad by a tropical delay yields a sequent calculus where
scheduling *is* proof search structure: durations compose in the graded
bind, synchronisation is a promotion side condition, in-flight work is a
proof-term node, and the scheduler is a sound, deterministic,
frame-rate-independent oracle. The metatheory is done on paper in full —
cut admissibility, identity expansion, exact adequacy, and a separation
theorem showing the grade alone measures cost while stamps alone contribute
scheduling.

**Future work.** Mechanisation of §4 (the rules must carry the
theory-premise form). The probabilistic weight grade (weighted additive
disjunction) needs its own judgment — a second paper. Symbolic timed
exploration (metavariables in both pattern and state) and the ω-exponential
× time interaction remain open. The cross-system benchmark table is pending
a controlled host.

---

## Acknowledgments / provenance

Drafted from THY_0018/0019/0022/0023 and the TODO_0265/0272/0273 audit
trail; adversarial referee passes are recorded in the project's research
log (rounds 13–15 and the 2026-08 audits).
