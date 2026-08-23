# Timed-Settle Performance Architecture (TODO_0277)

How `settle` stays O(live distinct facts) per tick and O(1) in elapsed
time. The representation/index/scheduler layers are default-on and
bit-identical; the state-rewriting layers (coalesce, accelerate, rebase)
are OPT-IN settle options — the exact-stamp gate suites run without them.

The three opt-ins are state morphisms with stated laws:

    normalize (coalesce) : State → State   idempotent; preserves every
                                           pending activation and the
                                           reachable-worlds semantics
    shift_B (rebase)     : State → State   shift_0 = id; requires the
                                           program translation-covariant
    jump_n (accelerate)  : State → State   = settle^n on a certified
                                           periodic orbit; state-identical

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

## Translation covariance (audit hardening)

`lib/engine/timed/covariance.js` assigns every rule position a SHIFT
DEGREE — how its value moves when all matched stamps move by B: window
bounds must be degree 1 (absolute time points), delay/weights/counts
degree 0 (durations/scalars), and degree-1 vars may not leak into inner
terms or opaque goals. Degrees derive from binding sites (stamp positions
= 1) and combine through the calculus' `shiftOps` q-op table. This is the
timed-automata diagonal-constraint exclusion, mechanized: `before (Q1+Q2)`
has degree 2 and is refused, `after 3` has degree 0 and is refused,
`after (Q+20)` has degree 1 and passes.

- **rebase** requires full covariance — loud refusal at settle entry for
  static rules, no-op shift (`result.rebase = 0`) when the STATE carries a
  windowed possessed rule or menu.
- **accelerate** needs only the `before`-bound leg: `after` bounds pin
  activations (frontier-relatively visible in the checkpoint signature —
  they can never alias two sightings), but a `before` bound is a silent
  filter a recurring cycle can drift past. Covariant deadlines move with
  the cycle; ground deadlines cap the jump strictly below themselves
  (normal firing carries the crossing; the expired rule then counts as
  call-dead — durable, time is monotone — and the post-deadline regime
  re-certifies); opaque deadlines refuse certification.

## Orbit certificates (TODO_0278 A1)

A settle that certifies an orbit and exits inside it MINTS the proof:
`result.certificate = { v, fingerprint, sigKey, period, sinkDelta,
cycleEvents }` (JSON-safe, ~0.5 kB). A later `settle(state, T,
{ certificate })` revalidates it at the current frontier — same probe as
an in-run checkpoint (sink/cap/aliveness classification, deadline caps,
exact signature equality) — and applies the elapsed cycles as ONE jump.
`certificate:` implies `accelerate:`; a resumed settle re-mints at its own
exit, so chained saves keep working.

- **Fingerprint pin**: `sigKey`/`sinkDelta` use raw Store hashes, only
  meaningful against the bit-identical loaded arena. The certificate
  carries engine version + arena-prefix mark + content digest
  (`Store.prefixDigest`); a resume whose arena does not extend that exact
  prefix refuses. Program update ⇒ proof invalid — required semantics,
  not just hygiene.
- **Phase independence (the lemma behind exit-phase minting)**: the
  in-run proof certifies recurrence at checkpoint phase t₀:
  `state(t₀+p) = shift_p(state(t₀))` with no draw-sensitive tie in the
  window. Firing is deterministic outside such ties, and tie
  draw-SENSITIVITY is translation- and sink-invariant, so determinism
  propagates: `state(t+p) = shift_p(state(t))` for every t ≥ t₀. The exit
  phase therefore inherits the proven period, per-period sink growth, and
  per-period event count. Mint refuses if a draw fired after the proving
  sighting or a ground deadline was crossable within the horizon (regime
  change — the period would be stale).
- **Failure = fallback**: any mismatch (fingerprint, signature,
  classification, deadline) silently falls back to in-run re-detection;
  a stale certificate can never mis-fire.
- **`certificateMode: 'verify'`**: belt-and-braces — instead of trusting
  the saved periodicity, the certificate is planted as a prior sighting
  and the natural checkpoints re-prove one period live (interval minima
  included) before jumping. O(one cycle) honest re-proof.

Pins: `tests/engine/till-accel-resume.test.js` (mint conditions, E5
save/resume exactness with full event accounting, tamper/fingerprint
fallback, deadline caps, rebased frames, verify mode).

## Catch-up at scale (TODO_0278 A2)

Three mechanisms let a settle cross weeks of elapsed time even when the
orbit does NOT certify (tie-poisoned states — any built kiln, until A3a):

- **Zeno guard redefined (D16).** True Zeno is no time progress. The guard
  counts firings at ONE instant (`maxInstantSteps`, default 100000) and
  resets whenever the frontier advances — a dense-but-finite catch-up runs
  to completion regardless of total event count. Flat `maxSteps` is now an
  OPT-IN total hard cap (off by default): the recourse for untrusted
  programs whose divergence advances the frontier every step (a
  delay-shrinking convergent schedule), which no finite-observation
  per-instant test can detect. The load-time productivity lint stays the
  static complement.
- **Event suppression.** `{ events: false }` skips the events array — the
  week-scale OOM was 24 M event records as much as the unroll. The result
  carries `events: null` (loud on accidental `.length`) plus
  `eventTotals { rule: count }`; `onEvent(record)` streams the full record
  per firing independently, so nothing is lost, only unrequested retention.
- **`settleChunked(S, T, { chunk, onChunk, ...settle opts })`.** Bounded
  slices, each covering (prev horizon, next-activation + chunk] — anchored
  at the pending schedule, so idle spans cost one slice. Soundness is E5:
  `settle(settle(S,T₁),T₂) = settle(S,T₂)`, and the PRF chooser is
  horizon-split invariant, so even weighted draws replay identically in
  exact mode (under coalesce the usual cohort-identity contract applies).
  Drop-in result contract: `next`/`rebase` in the caller's frame,
  `certificate` from the final slice, `maxSteps` a TOTAL budget, `chunks`
  added. Certificates thread — the input certificate seeds slice 1, each
  slice's mint feeds the next, so a proven idle orbit costs one validated
  jump per slice and the app still gets its `onChunk` progress ticks.

Measured (PP2 shell + kiln, the tie-poisoned motivator): 3-week catch-up =
24 M events unrolled in bounded memory with day-sized chunks — formerly a
`maxSteps` throw at ~1 day, an OOM at week scale. Pins:
`tests/engine/till-chunked.test.js`.

## Contracts

- Coalescing/rebase change cohort identity and state hashes → future PRF
  tie draws may differ (any draw is a valid world — settleExplore's
  contract). Acceleration is state-identical TO THE COALESCED RUN
  (differential-pinned; fuzz arm on deterministic programs).
- Raw pipelines: the same State object flows through consecutive settles;
  mutating it elsewhere invalidates the cached scheduler automatically
  (mutation counters), never silently. With `rebase`, a raw result's
  `state` is NOT re-serialized — the caller reads `result.rebase` and owns
  the accumulated base; a nonzero shift drops the cached scheduler.

## Benchmarks

`node benchmarks/engine/timed-settle-bench.js [--only B1,B2,B3,OR,OF,OT]
[--coalesce] [--accel] [--ticks N] [--b3ticks N]`

- B1 PP2 tick loop: per-tick ms + live entries flat at any T
- B2 magnitude: `!_10^k` settle flat in k (0..6)
- B3 memory: 100k chained ticks, Store/RSS plateau
- OR rules: warm chained tick flat in #rules
- OF cohorts: warm settle vs inert population
- OT deep time: settle 0→T flat in T (acceleration)

Consumers: the PP2 game bridge runs `{ coalesce: true, accelerate: true,
events: false }` (+ periodic `rebase`) and threads orbit certificates
through its `certificate()`/`resume()` API; `tools/till-shell.js` runs
`{ coalesce: true }`. Measured history: TODO_0277 progress log.
