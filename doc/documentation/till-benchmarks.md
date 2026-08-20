# till Benchmarks and Cross-System Comparison

The till scheduler (`lib/engine/timed/`) has an internal benchmark harness and a
*planned* comparison against the three systems a POPL/LICS reviewer will expect
(THY_0018 novelty ledger names them). This document records the internal
baseline and specifies the comparison protocol; the cross-system numbers are
future empirical work — Real-Time Maude, Celf, and CPN Tools are not installed in
this repo's environment, and running them fairly requires a controlled host.

## Internal harness

```bash
npm run bench:till          # bun benchmarks/engine/till-bench.js
```

Five scenarios (source: `benchmarks/engine/till-bench.js`), baseline on the
development host (2026-08-20, indicative — re-run locally; use `bench:diff` for
regressions, not these absolute numbers):

| Scenario | What it stresses | ms/op |
|---|---|---:|
| `economy` | 10/10/10 resources, settle to T=1 (7 firings) | ~1.0 |
| `economy-XL` | 100/100/100, settle to T=10 (~150 firings, deep schedule) | ~53 |
| `duel` | 8v8 weighted duel to quiescence (woplus PRF draws) | ~0.26 |
| `duel-explore` | 3v3 exhaustive `settleExplore` (weighted tree, 100+ leaves) | ~0.64 |
| `coupled` | x*y over 24×24 distinct-stamp cohorts (branch-and-bound match) | ~1.9 |

These are *microbenchmarks* — settle-to-quiescence wall-clock for one program.
They exist to gate the Phase-7 fingerprint/strategy work (measure before
optimising), not as a headline result.

## The two case studies for cross-system comparison

The audit ("at least two case studies") is satisfied by two of the scenarios
above, chosen because each isolates one of till's two novel gradings and each has
a faithful idiom in a comparable system:

### Case study A — timed resource scheduling (`economy` / `economy-XL`)

Pure delay grading: resources with availability stamps, rules `In -o {Out}@d`
firing at `max(inputs)+d`. This is the `till` core (THY_0018 delay monad).

- **Real-Time Maude** (Ölveczky–Meseguer): the natural competitor. till's
  `@fire` activation `a = max(tᵢ)` is Real-Time Maude's tick/mte over a state of
  timed resources. Comparison: encode `economy-XL` as a real-time rewrite theory
  with the same resource multiplicities; measure time to reach the T=10 stable
  state. till's edge to test empirically: activation is a max-of-stamps computed
  per firing (event-driven), where a naive tick discretisation pays per time
  unit. **Hypothesis:** till is asymptotically insensitive to the horizon `T`
  (event-count-bound), Real-Time Maude with fixed tick is `O(T)`.
- **CPN Tools** (timed coloured Petri nets): resources = timed tokens, rules =
  timed transitions, `@d` = the transition's `@+d` time inscription. Same
  `economy` net; measure simulation-to-quiescence. This is the closest
  operational mirror (till's fact multiset ≈ a marking).

### Case study B — weighted/probabilistic branching (`duel` / `duel-explore`)

Pure weight grading: `woplus 3/4 rock sci` (THY_0021). Two sub-questions:
`settle` (Monte-Carlo sample) and `settleExplore` (exact rational distribution).

- **Ceptre** (Martens): probabilistic rule selection. Encode the RPS duel as a
  Ceptre stage with weighted rules; compare sampled win-frequency convergence
  (Ceptre samples rule choice; till samples a woplus branch — Theorem 3 of
  THY_0021 says both are unbiased estimators of the same distribution).
- **Exact distribution** has no direct competitor: `settleExplore` computes the
  9/16 win probability in exact ℚ by enumerating the weighted derivation forest
  (THY_0021 §5). The comparison here is *correctness against the combat DP*
  (`winProbDP`, already tested), and *cost* against a hand-rolled absorbing-Markov
  -chain solver — till's tree is the chain unfolding, so it is at best constant-
  factor off the DP and at worst exponential in un-memoised paths (Phase-7 subtree
  memo closes the gap; this is the honest limitation to report).

## Comparison protocol (for when the tools are available)

1. **Same case study, three encodings.** economy-XL in {till, Real-Time Maude,
   CPN Tools}; the RPS duel in {till, Ceptre}. Keep resource multiplicities and
   weights identical; verify each reaches the SAME final state / distribution
   before timing (correctness gate first).
2. **Metric.** Wall-clock settle-to-quiescence, warm (discard first run), median
   of ≥ 10, on one pinned host. For the exact-distribution study, also report the
   leaf count and whether the competitor can produce an exact rational at all.
3. **Scaling axis.** Sweep the horizon `T` (case A) and the army size (case B) to
   expose the event-driven-vs-tick and enumerate-vs-solve asymptotics the
   hypotheses above predict — the shape matters more than the absolute constant.
4. **Report honestly.** till's forward engine is a research prototype in JS;
   absolute constants against a mature C++/Maude engine are not the point. The
   claims to substantiate are *asymptotic* (horizon-insensitivity) and
   *qualitative* (exact rational distribution; two gradings in one framework),
   not "till is faster".

## Status

- Internal harness: **runnable** (`npm run bench:till`), 5 scenarios green.
- Cross-system numbers: **not yet collected** — needs Real-Time Maude / CPN Tools
  / Ceptre installed on a controlled host. This document is the protocol and the
  baseline; the empirical table is the remaining work (it is a POPL-submission
  task, tracked with the THY_0018/THY_0021 write-up, not an engine change).
