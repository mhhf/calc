# till — Timed ILL

Timed graded rewriting: ILL's multiplicative core + time as a tropical grade.
Calculus package: `calculus/till/` (till.calc, calculus-config.js, prelude/rat.ill,
tests/forward/*.ill). Engine: `lib/engine/timed{,-game,-views,-lint}.js` (generic, config-driven).
Design/decisions: hq todo 0265; reference semantics: `tools/till-oracle.mjs`.

## Model

- **Stamp** `A@t` — availability: the token exists from logical time `t` (exact
  rational; canonical `ratlit`/`binlit` hash). Unstamped facts in an initial
  state default to stamp 0. Unstamped LHS *patterns* are stamp wildcards.
- **Duration** `{B}@d` — the graded lax monad (`monad(d, body)`, till-local tag):
  outputs materialize `d` after the rule fires. `{B}` = delay 0. `d` may be a
  term (`@D` with `!qdiv 10 N D` — E7.1): it must be a ground rational after
  matching (compile checks the variable is antecedent-bound).
- **Firing**: a match `m` activates at `a(m) = max(selected stamps, after-bounds)`;
  inputs are consumed at `a(m)`, each output `B` appears as `at(B, a(m)+d)`.
  Tropical reading: ⊗-of-inputs ↦ max (synchronise), sequencing ↦ + (delay).
- **Windows** (matcher guards, not predicates): `after E` bounds `a(m) ≥ E`;
  `before E` demands `a(m) < E`. `E` is a rational, a bound stamp variable, or
  arithmetic (`after (Q+2)`), lowered at load to persistent `!qplus/...` goals.
  Windows are WEAK semantics (TAPN terminology): `before` invalidates a match
  past the deadline but never FORCES a firing — hard real-time urgency is
  deliberately out of scope.
- **`$A`** occupy (timed single server: consumed, re-emitted at `a(m)+d`);
  **`read A`** test arc (never consumed, original stamp; its stamp joins the
  activation max; concurrent reads don't conflict).
- **Count grades** (D4): `!_k A` splits `k` off one cohort; `!_W A` takes the
  whole matched cohort, binding `W` (a `binlit`) to its size at firing time;
  `!_Y B` in a consequent produces `Y` copies. `!`/`!_0` keep their SELL
  meanings (persistent / compile-time); persistents are timeless — no stamp
  anywhere under `!` (D15).
- **Weighted choice** (Phase 4b): `woplus Q A B` in consequents — branch `A`
  with probability `Q` (ground rational in [0,1]), `B` with `1−Q`; prefix
  form, nests and tensors (weights multiply, always summing to 1). `settle`
  samples the branch through the same stateless PRF as the conflict chooser
  (seed-reproducible, horizon-split invariant; the draw is a 32-bit uniform,
  so sampled branch frequencies match the weights to within 2⁻³² — the
  explore tree is exact); `settleExplore` expands both with the weight on
  the edge — the tree IS the exact outcome distribution (leaves carry
  `weight`, exact `[num, den]` path products).

## Scheduler (lib/engine/timed.js)

Semantics is earliest-activation-first (D12 — not a knob): `settle(state, T)`
repeatedly fires an enabled match with globally minimal `a(m)` while
`a(m) ≤ T`. Per-rule matching is a branch-and-bound over stamp-sorted cohorts
(oldest first = FIFO; minimal activation, FIFO tie-break — P1). Within an
activation instant, the **conflict chooser** decides: `random` (default) is a
stateless content-derived PRF over (seed, state hash, candidate set) —
replay-identical and horizon-split invariant; `deterministic` and custom
functions are pluggable, as is the **cohort sampler** (`fifo`/`lifo`).
Composability law (tested): `settle(settle(S,T₁),T₂) ≡ settle(S,T₂)`.
Zero-delay cycles trip a maxSteps Zeno guard (D16). Two schedulers, verified
trace-identical: full rescan (default) and rule-granular dirty tracking
(`scheduler: 'dirty'` — per-rule activations recomputed lazily via
triggerPreds; bindings are never cached).

State: ordinary linear FactSet under till's index policy (`factSetPolicy`:
`at(A,t)` groups under A's predicate, ordered by stamp then hash). The index
is optimization, the multiset is semantics — policies may not change which
matches exist. Rules carrying windows/durations/count grades are loudly
rejected by the untimed engine (`calc.exec`); the timed matcher owns them.

## API (calc objects loaded with till's calculusConfig)

```js
import tillConfig from 'calculus/till/calculus-config.js';
const calc = mde.load(file, { calculusConfig: tillConfig });

calc.settle(state, T, opts)      // → { state, quiescent, steps, events, next }
calc.nextActivation(state)       // earliest pending activation (hash) | null
calc.settleExplore(state, T)     // → { tree, leaves } — branch ONLY on genuine
                                 //   conflicts: shared consumed cohort, read
                                 //   starvation, or instant-feeding (a tied
                                 //   zero-delay rule producing into any rule's
                                 //   antecedent — ample-set condition, round 13);
                                 //   covers all chooser-reachable outcomes;
                                 //   woplus forks weighted; leaves = { state,
                                 //   weight: [num, den], next? }. Leaves are
                                 //   PATH-indexed, not outcome-unique: two
                                 //   orderings converging on one state yield
                                 //   two identical leaves (dedup/subtree memo
                                 //   = Phase 7)
calc.observable(state, T)        // stamp ≤ T slice: { innerHash: count }
calc.pending(state, T)           // future facts [{fact, stamp, count, remaining}]
calc.inFlight(events, T)         // running jobs [{rule, activation, done, remaining}]
```

`T`: integer Number, exact string (`"1/2"`, `"0.7"`), or `{ stamp: hash }`.
`opts`: `maxSteps`, `seed`, `chooser`, `cohort`, `scheduler`, `rules`,
`useFFI: false` (clause-only arithmetic — FFI principle: identical results),
plus the standard hooks (`onStep` gains `activation`/`delay`).
`events` is the completion queue (E7.3): processes are trace nodes — rule
name = process kind, `(done − T)` = remaining; no job tokens in the model.
Each event records `{ rule, activation, delay, done, theta, consumed,
reserved, produced, alt? }` — `produced` feeds provenance (`#why`), `alt`
the sampled woplus branch.

## Debugging (Phase 4c)

`node tools/debug-till.js <file.ill>` runs timed observation directives —
each takes `(settle: T)` and optionally `query: <kind>` pointing at a shared
`#run` scenario (see `calculus/till/tests/debug/chopbuild.ill`):

- `#trace_*` — log view: `[activation] rule: consumed [read r] → produced @+d`
- `#timeline_*` — jobs lane (`rule [a→done]`) + per-predicate token
  lifetimes (`born→consumer@a` or `born→…` if alive)
- `#why_*` — provenance: per-instance producer chain of the body fact
  (`hut@7 ← build @4 +3 ← wood@4 ← chop @0 …`)
- `#why_not_*` — why the named rule isn't firing: pending activation beyond
  the horizon, a killing `before`-window, an unprovable goal, or the
  missing input pattern (best failed candidate, from the matcher's
  diagnostic mode)

The renderers are pure functions in `lib/engine/timed-render.js` (golden
tests exercise them verbatim). `settle` events carry `produced` facts and
serialize as `forward-trace/v2` steps with `activation`/`delay` pool refs
(`lib/prover/serialize-trace.js`). Graded monads render faithfully —
`{B}@g` unless `g` is the unit — via `buildRenderer(constructors,
{ gradeUnit })`; browser bundles re-supply the hook at hydration:
`initFromBundle(bundle, { parserOpts: { gradeUnit }, rendererOpts: … })`.

## Tests

- `npm run test:till` — executable specs in `calculus/till/tests/forward/`
  (`#expect_* (settle: T) S => P`; unstamped `P`-facts are stamp wildcards).
  Each spec file is its own program (file-local rule sets).
- `tests/engine/till-settle.test.js` — composability, scheduler equivalence,
  chooser/PRF, explore conflicts, samplers, delay terms + FFI-off agreement,
  guards, Zeno, differential vs `tools/till-oracle.mjs`.
- `tests/engine/till-oracle.test.js` — the reference scheduler's own suite.

## Not in v1 (tracked in todo 0265)

Grade-0 content in till (compose.js ILL-tag hardcodes); ℚ-valued parcels;
flowrate catch-up (E6); a till UI bundle (libexec/calc-bundle hardcodes
loadILL — the browser gradeUnit hook is ready); backward sequent rules
(`till.rules`/`till.family` — todo 0265 Phase 6b: the graded fragment needs
a rule-DSL side-condition extension, the timed judgment is gated on
THY-A/THY-B; stamps are judgment structure, not a connective).
