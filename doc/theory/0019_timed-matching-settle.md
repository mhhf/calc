---
title: "Timed Matching and the Settle Scheduler"
created: 2026-08-18
modified: 2026-08-18
summary: "The operational metatheory of till (THY-B to THY_0018's THY-A): timed multiset matching with stamp patterns, activation windows and count-grade parcels; the min-activation match order (NOT lexicographic-first — a counterexample forces branch-and-bound); the settle scheduler with its composability law settle(settle(S,T1),T2) = settle(S,T2); determinism via a stateless content-derived PRF chooser; termination = per-instant quiescence + positive-delay cycles (Zeno guard)."
tags: [till, forward-chaining, time, tropical, scheduling, matching, determinism, engine, proof-theory]
category: "Timed Rewriting"
unique_contribution: "Three results not in the literature: (1) the observation that in timed matching with cross-pattern guards, per-rule FIFO-lexicographic-first matching is UNSOUND for nondecreasing-activation scheduling (explicit counterexample) — the rule's match must be the activation-MINIMAL valid assignment, computable by branch-and-bound with sound pruning because activation is monotone in partial assignments; (2) the settle composability law as the frame-rate-independence theorem for a logic-based game/economy engine, proved from min-activation firing + a stateless content-derived PRF whose choices are invariant under horizon splitting; (3) whole-cohort grade binding !_W with at-firing-time semantics obtained for free from recompute-only match caching (bindings are never stored, so no staleness class exists)."
references:
  - "THY_0018 — The Delay-Graded Lax Monad (THY-A; the logic this schedules)"
  - "TODO_0265 — timed graded rewriting (D4, D8, D12, D17; Pseudocode P1–P5)"
  - "Kanovich, Kirigin, Nigam, Scedrov & Talcott (2016). Timed Multiset Rewriting... FORMATS."
  - "Jensen, Kristensen & Wells (2007). Coloured Petri Nets and CPN Tools... STTT."
  - "Bolognesi, Lucidi & Trigila (1990) / Hanisch (1993) — timed-arc Petri nets (token ages, arc windows)."
  - "Merlin & Farber (1976). Recoverability of Communication Protocols. IEEE ToC."
  - "Alur & Dill (1994). A Theory of Timed Automata. TCS."
  - "Baccelli, Cohen, Olsder & Quadrat (1992). Synchronization and Linearity. Wiley."
---

# Timed Matching and the Settle Scheduler

THY-B of TODO_0265. THY_0018 gives the logic (`A@t`, `{S}@d`, the `@fire` promotion
rule); this document gives the operational layer that a sound engine must implement:
WHICH match a rule contributes, in WHAT order matches fire, and why the result is a
deterministic, horizon-split-invariant function of the state. The reference
implementation is `tools/till-oracle.mjs`; every theorem here has a corresponding test
in `tests/engine/till-oracle.test.js`.

## 1. States, patterns, matches

**State.** A timed multiset: a finite map from (atom, stamp) to a positive count. A
(atom, stamp) pair with its count is a COHORT — the merged normal form of the graded
parcels `!_n A@t` (TODO_0265 D4): same-stamp copies merge; distinct stamps are distinct
cohorts, never merged (the stamp axis is non-collapsing).

**Patterns** (per rule antecedent atom):

| pattern | matches | binds |
|---|---|---|
| `A` | any cohort of `A` | anonymous stamp (joins activation) |
| `A@Q` | any cohort | its stamp to `Q` |
| `A@c` (ground) | exactly the stamp-`c` cohort | — |
| `!_k A` | k copies across ANY cohorts, sampler order | — (newest taken stamp joins activation) |
| `!_k A@Q`/`@c` | ONE cohort with count ≥ k | splits `k` off it; `Q` := its stamp |
| `!_W A` | ALL copies of `A` | `W` := the TOTAL, at firing time |
| `!_W A@Q`/`@c` | ONE whole cohort | `W` := its count, `Q` := its stamp |
| `read A[@…]` | as above | nothing consumed; stamp joins activation |

**Binding discipline decides cohort discipline** (D4 revised, with TODO_0011):
an unstamped counted pattern binds no stamp, so the stamp axis must be
unobservable through it — the erasure argument: `!_k A` untimed means "k copies
of A", and the timed semantics refines that reading rather than restricting it
to same-stamp copies. The spread takes cohorts in sampler order (oldest-first
under `fifo`), which is the activation-minimal choice by construction since
activation joins the newest taken stamp. Writing `@T` (even with `T` otherwise
unused) opts back into cohort-locking: one stamp variable, one cohort — same-age
batches become an explicit, purchasable discipline instead of a default leak.

Plus rule-level annotations: guards (ordinary provable propositions over bindings),
`after E` and `before E` windows (`E` a rational expression over bound stamps), and the
delay term `@D` (ground after substitution; mode-checked at compile).

**Match.** An assignment `m` of one cohort (with a take-count) to each pattern atom,
injective on takes (reservations within the candidate), satisfying guards. Its
**activation** is the max-plus linear form

```
a(m) = max( selected stamps  ∪  { E : after E } )
```

and `m` is **valid** iff `a(m) < min{ E : before E }` (empty min = ∞). Firing consumes
the takes at `a(m)` and produces each output `B` under `{·}@d` as `B@(a(m)+d)`.

## 2. The match order: minimal activation, FIFO tie-break

The scheduler's contract (THY_0018 §6) is: fire enabled matches in NONDECREASING
activation. So the match a rule contributes must be its activation-minimal one.

**Proposition 1 (lexicographic-first is unsound).** Enumerating candidate cohorts
oldest-first per pattern and taking the first valid assignment (FIFO-lexicographic with
backtracking) does not compute the minimal activation when guards or windows couple
patterns. *Counterexample.* State `A@0, A@3, B@3, B@9`; a guard rejecting exactly the
pair `(A@0, B@3)`. Lexicographic-first finds `(A@0, B@9)` with `a = 9`; the minimal
valid match is `(A@3, B@3)` with `a = 3`. A scheduler firing the `a = 9` match ahead of
another rule's `a = 5` match violates nondecreasing activation — and with it Theorem 4
below. ∎

**Definition (rule match).** The match a rule contributes is the valid assignment with
MINIMAL `a(m)`; among equal-activation assignments the FIFO-lexicographic least (oldest
cohorts, pattern order) — FIFO is a tie-break, not the search order's semantics.

**Proposition 2 (branch-and-bound is sound and complete).** Depth-first search over
pattern atoms with cohorts enumerated in ascending stamp order, carrying the partial
activation `a₀ = max` of the stamps selected so far, and pruning any branch with
`a₀ ≥ a(best-so-far)`, returns exactly the Definition's match. *Proof.* `max` is
monotone in extensions: any completion of a partial assignment has activation ≥ a₀, so
pruning discards only non-improving matches (completeness); the strict `<` update keeps
the first-found — and DFS order visits equal-activation assignments in FIFO-lexicographic
order, so first-found = the tie-break (canonicality). ∎

**Proposition 3 (fast path).** If a rule has no `before` window and no guard relating
bindings of two different pattern atoms, greedy oldest-per-pattern IS the minimal match,
in one pass. *Proof.* Without coupling, validity of a cohort choice for one pattern is
independent of the others, so the coordinate-wise minimal choice minimises each stamp,
and `max` of coordinate-wise minima is the minimum of `max`. ∎ (This is why the common
case costs what untimed matching costs; the search runs only for coupled rules.)

**Count grades.** `!_W A@T` binds the matched cohort's count AT FIRING TIME
(unstamped `!_W A` likewise binds the live TOTAL). In this design
that property is free, not enforced: matches are recomputed from the live state whenever
a rule's inputs may have changed and bindings are never stored across state changes
(TODO_0265 round 9 — the only cache is rule-granular dirty marking; a per-match plan
cache would need an addition-invalidation trigger and is exactly what we do not build).
A same-instant parcel addition racing a whole-cohort bind is an ordinary equal-activation
conflict, resolved by the chooser (§3).

## 3. The scheduler

```
settle(S, T):  while some rule has a valid match m with a(m) ≤ T:
                 among the matches with globally minimal a(m): if several, chooser;
                 fire it (consume at a(m), produce at a(m)+d);
               return S            -- quiescent at horizon T; future stamps pending
```

`nextActivation(S)` is the same computation without firing. There is NO clock, no tick,
no watermark: stamps are monotone (an output's stamp ≥ its event's activation), so after
`settle(T)` every remaining match has activation > T and a later call resumes correctly
with no memory of T.

**Chooser (D17).** Equal-activation conflicts are resolved by a STATELESS content-derived
PRF: `choice = mix(seed ⊕ hash(state) ⊕ hash(candidate set))`, candidates ordered by a
deterministic key. No RNG state exists in engine or state; "seeded" means this config
value.

**Theorem 4 (composability / frame-rate independence).** For `T₁ ≤ T₂`:
`settle(settle(S, T₁), T₂) = settle(S, T₂)` — states, traces, and stamps all equal.
*Proof sketch.* Induction on the fired-event sequence of the right-hand side. While the
next event's activation is ≤ T₁, both sides select the same match: minimal activation is
a function of the state only, and the chooser's PRF reads (seed, state, candidate set) —
none of which mentions the horizon. When the next activation exceeds T₁ the inner settle
returns without firing, changing nothing; the outer settle continues the same sequence.
The horizon GATES the loop but never influences a selection — that is the entire proof
obligation, and the design discharges it by construction (no watermark, no horizon-
dependent state, stateless chooser). ∎ Idempotence (`T₁ = T₂`) is the base case.
This law is what makes a game host frame-rate independent and offline catch-up exact:
`settle(now)` after any gap replays exactly the history the small-stepped host would
have produced (worked example: TODO_0265 Matching spec, the eat/spoil race).

**Theorem 5 (determinism).** `settle` is a function of (state, horizon, seed, policies).
*Proof.* Every choice point is either the minimal-activation selection (deterministic by
Proposition 2 + the FIFO tie-break) or the PRF (deterministic by statelessness). ∎

**Theorem 6 (termination).** `settle(S, T)` terminates iff the execution has finitely
many events with activation ≤ T. A sufficient static condition: every cycle in the
rule-dependency graph has positive total delay — then events at or below any horizon are
finitely many (each cycle traversal advances activation by at least its total delay).
*Zeno counterexample:* `ping: a ⊸ {a}@0` from `a@0` fires at 0 forever — logical time
never passes 0. With `@1` the same rule is productive (events at 0,1,2,…) — the
guardedness reading of the delay grade (THY_0018 §9). Operationally the engine carries a
`maxSteps` guard; the static condition is the productivity lint. Role-wise this matches
Kanovich et al.'s "progressing" condition (FORMATS 2016, Def. 3: balanced rules with at
least one strictly-future output, whence their Prop. 2 bounds actions per time unit);
ours is the weaker cycle-local form — only CYCLES need positive total delay, zero-delay
rules off-cycle are fine. ∎

## 4. Windows on one logical timeline

`after E` joins the activation max; `before E` is a validity deadline. Both are read by
the matcher — there is no ambient `time(T)` fact and no clock-test predicate, so a
spoilage rule races its consumers in exact stamp order REGARDLESS of how far the host
jumps the horizon (the eat/spoil example; test: "windows and spoilage"). Hard expiry is
the `before` window on consumers (stale cohorts are skipped — the FIFO tie-break then
takes the next-oldest FRESH cohort, Proposition 2's search doing this for free);
soft expiry leaves the race to the chooser. Literature anchors: token ages with arc
windows are timed-arc Petri nets; firing intervals are Merlin–Farber time Petri nets;
guard/invariant clocks are timed automata — our windows need no clocks because the
timeline lives in the stamps.

## 5. Read arcs

`read A` matches like a linear pattern, joins the activation max (nothing is read before
it exists), consumes nothing, and leaves the token bit-identical (original stamp) — the
contextual-net test arc. Concurrent same-instant reads do not conflict; a `$`-based
encoding would falsely serialise them (test: "read arcs"). The observational
justification for original-stamp re-emission is THY_0018 Theorem 4.

## 6. What remains open

The two-sided unification problem for `@`-patterns (metavariables in BOTH the pattern
and a symbolic state, as `explore()` over symbolic timed states would need) is not
treated here — matching in this document is one-sided against ground states, which is
what `settle` needs; decidability is immediate (finite search), and Propositions 1–3
settle principality for the ground case. The symbolic case, and the formal boundary of
timed `explore()`'s branch-only-on-conflicts criterion (THY_0018 Theorem 2's boundary),
are the remaining THY-B items, deferred until the engine phase that needs them
(TODO_0265 open questions 1–2).
