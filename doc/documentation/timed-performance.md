# Timed-Settle Performance Architecture (TODO_0277)

How `settle` stays O(live distinct facts) per tick and O(1) in elapsed
time. All features are OPT-IN settle options; the exact-stamp gate suites
run with everything off.

## The stack

| Layer | Where | What it does |
|---|---|---|
| Run-length FactSet | `lib/engine/fact-set.js`, `policy.runLength` | Multiplicity as parallel count arrays — a `!_10^6` parcel is one entry. Zobrist hashes bit-identical to the classic representation. |
| Per-atom-name groups | till `factSetPolicy.groupKey` | Each atom head files in its own group (fixed-base id registry; FactSet tables grow on demand) — candidate enumeration never scans the population. |
| Float stamp order | till `factSetPolicy.cmp` / `grades.availability.cmp` | Cached correctly-rounded doubles; monotone rounding makes float order sound, ties and ≥2^53 operands fall back to exact rational compare. |
| Coalescing | `lib/engine/timed/coalesce.js`, `{ coalesce: true }` | Arrived facts whose stamp no rule can observe re-stamp to the unit and merge. Exclusion set DERIVED per rule: stamp-binding patterns (`A@Q`, `!_k A@T`), every pattern of a `before`-window rule, possessed lolis; wildcards bail. Mid-run bound: last fired activation (strict); at return: the horizon. |
| Incremental state | `{ raw: true }` | Returns the live FactSet State; `normalizeTimedState` passes an already-policy-indexed State through. Chained ticks skip the rebuild. Ownership transfers. |
| Dirty scheduler (default) | `timed.js _makeDirtySched` | Per-rule activations in a lazy-invalidation min-heap; per-step cost O(#dirty·match + log #rules). Trace-identical to `scheduler: 'rescan'` (P3/D13 suite). Survives across raw-mode calls via FactSet mutation counters. |
| Acceleration | `lib/engine/timed/accel.js`, `{ accelerate: true }` | Exact-signature periodic-orbit detection at adaptive checkpoints → jump n periods in O(state). Abstractions: sinks (reachability-dead consumers), capped stocks (bounded takes, interval-minima validated), frozen fixtures (excluded only by call-dead rules). Nondet guard: genuine conflicts / woplus draws invalidate the window. Events inside jumps are elided — `result.accelerated` reports them. |
| Rebase | `{ rebase: true }` (requires coalesce) | Integral shift of the time origin at exit (`result.rebase`); caller accumulates the base and passes rebased horizons. Keeps the reachable stamp vocabulary finite → the content-addressed Store stops growing. |

## Contracts

- Coalescing/rebase change cohort identity and state hashes → future PRF
  tie draws may differ (any draw is a valid world — settleExplore's
  contract). Acceleration is differential-pinned state-IDENTICAL.
- Raw pipelines: the same State object flows through consecutive settles;
  mutating it elsewhere invalidates the cached scheduler automatically
  (mutation counters), never silently.

## Benchmarks

`node benchmarks/engine/timed-settle-bench.js [--only B1,B2,B3,OR,OF,OT]
[--coalesce] [--accel] [--ticks N] [--b3ticks N]`

- B1 PP2 tick loop: per-tick ms + live entries flat at any T
- B2 magnitude: `!_10^k` settle flat in k (0..6)
- B3 memory: 100k chained ticks, Store/RSS plateau
- OR rules: warm chained tick flat in #rules
- OF cohorts: warm settle vs inert population
- OT deep time: settle 0→T flat in T (acceleration)

Consumers: the PP2 game bridge and `tools/till-shell.js` run
`{ coalesce: true }` (+ periodic `rebase`). Measured history: TODO_0277
progress log.
