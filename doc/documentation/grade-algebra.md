# Grade Algebra — the pluggable-grade engine contract

What a grade algebra must provide so the timed engine (`lib/timed/`) can be
scheduled by it, and which algebraic laws license which engine behaviors. This is the
contract TODO_0284 P1 refactors *toward*; the executable form is
`tests/engine/grade-conformance.test.js`. Calculus-agnostic: instances live in calculus
configs (`cc.grades`), never in engine code.

## Signature

```js
// carrier: opaque value V (till: normalized BigInt pair [n, d] — an exact rational)
const GradeAlgebra = {
  unit,                       // 1̄ : V            — ⊗ identity (time 0, dist 0, weight 1)
  compose:  (a, b) => V,      // ⊗ : V×V → V      — sequential accumulation along ONE derivation
  residual: (a, b) => V|null, // ⊗-left-residual  — the h with compose(b, h) = a; null outside the fence
  cmp:      (a, b) => -1|0|1, // ≤ : total order  — order class only (index + B&B direction)
  merge:    (a, b) => V,      // ⊔ : V×V → V      — inputs co-consumed by ONE rule firing
  aggregate: {                // ⊕ : how ALTERNATIVE derivations combine (the semiring sum)
    class: 'order' | 'measure',
    realizations: [...],      // order ⇒ ['prune'] · measure ⇒ ['sum', 'sample']
  },
};
```

The ⊕ order-prune is **not a slot** (0284 audit): under C2+C3, `cmp(partial, best)
>= 0` is the *unique* sound B&B cut — a weaker cut is behavior-identical (the leaf
keeps strict `<` anyway), a stronger one unsound — so the StampTable fixes it and a
declared `prunes` throws at table construction. A measure algebra never prunes at
all (mass conservation, below).

An engine-facing value algebra may declare the canonical ⊔ realization SYMBOLICALLY —
`merge: 'join'` (max by cmp) — instead of supplying the function; the StampTable
id-lift recognizes the name and runs it on its cached-float cmp fast path (see
"Realization in till" below).

## Two operators, two roles

The critical distinction (TODO_0284 v3 audit): grade combination WITHIN one derivation
and aggregation ACROSS alternative derivations are different operators, and the engine
realizes them at different sites.

| role | operator | engine site (timed.js, drift-prone — roles are the contract) |
|---|---|---|
| ⊗ sequential | `compose` | rule delay: `done = stamps.compose(activation, delay)` (fire) |
| ⊔ tensor-merge | `merge` | after-window join `:211`; counted-spread `:308`/`:323`; single-row `:368` — activation = merge of all consumed stamps |
| ⊕ aggregate | `aggregate` | order: B&B prune `:247` + strict-`<` best keep `:224` · measure: mass sum / PRF sample (`prf.js sampleIndex` — will/0292) |

For time, `merge = max` (the conclusion waits for the LAST input) and ⊕ is realized as
min-prune (fire at the least enabling stamp). For weight, `merge = ·` (co-consumed
independent premises multiply — the ⊗-as-independence reading, THY_0026 §6 T4-d) and ⊕
is `+` (mass sum), realized exactly or by sampling. Time and distance differ only in
physical reading; weight differs in *class*.

## Condition families

The conformance harness selects the family by `aggregate.class`.

### Order class (`'order'` — time, distance, usage)

- **C1 total order**: `cmp` is reflexive, antisymmetric, transitive, total.
- **C2 monotone ⊗**: `a ≤ a' ∧ b ≤ b' ⟹ compose(a,b) ≤ compose(a',b')`.
- **C3 inflationary ⊗**: `unit ≤ a` and `a ≤ compose(a,b)` — grades only grow.
- **C4 merge = join**: `a ≤ merge(a,b)`, `b ≤ merge(a,b)`, and merge is the least such
  (for a total order: merge = max by `cmp`).
- **C5 termination**: a finite reachable-stamp bound per program (operationally: the
  Zeno guard + horizon — honest scope, not clean well-foundedness).
- **Residual fence**: when `residual(a,b) ≠ null`, `compose(b, residual(a,b)) = a`;
  null exactly when no fenced solution exists (grades are ℚ≥0 — no signed escape).

C2+C3 are what make the B&B prune *sound*: every completion of a partial match has
grade ≥ the partial, so `prunes = cmp ≥ 0` never discards a better completion. These
are the known Dijkstra-optimality conditions (Mohri '02 k-closedness at k=0; Sobrinho
'02 isotonicity ⟺ optimality; Höfner–Möller '12) — cited, not claimed (0284 R1).

### Measure class (`'measure'` — weight, ℚ≥0 with ⊗ = ·)

The unnormalized measure semiring (THY_0026): grades are masses, never normalized
in-logic, aggregation is `+`. No `cmp`-based pruning exists.

- **M1 mass conservation**: at every choice point, parent mass = Σ child masses.
  Realization `'sum'` must enumerate alternatives exhaustively — pruning is unsound
  (a discarded branch is lost mass, a silently wrong denominator).
- **M2 recursion as ω-chain**: depth-bounded mass is monotone nondecreasing in the
  bound; total mass = its least upper bound; finite ⟺ subcritical recursion
  (THY_0026 T2, Chi–Geman). Depth-bounding is a sound *approximation from below*.
- **M3 exact sampling**: realization `'sample'` draws each alternative with exactly
  its renormalized enumerated weight (PRF-seeded; unbiased — THY_0026 T1/T3).
- **⊗ laws still hold**: compose (·) is monotone on ℚ≥0 and unit (1) is its identity,
  but ⊗ is NOT inflationary (weights < 1 shrink) — which is precisely why order-class
  pruning is unavailable and the class split exists in the signature.

## Behavior → law table

| engine behavior | licensed by |
|---|---|
| B&B prune of partial matches | order: C1 + C2 + C3 |
| FIFO tie (first match at equal grade wins) | order: C1 totality (the `>=`/`<` invariant pair) |
| activation = merge of consumed stamps | C4 (order) / ⊗-independence (measure) |
| delay/weight accumulation on fire | ⊗ monotone; fence: order C3, measure ℚ≥0 closure |
| `{}@`-subtraction rules | residual fence |
| exhaustive mass sum (settleExplore) | measure: M1 |
| PRF sampling of alternatives | measure: M1 + M3 |
| depth-bounded approximation | measure: M2 (+ subcriticality for finiteness) |
| finite settle | order: C5 · measure: M2 subcriticality |

## Instances

| instance | carrier | ⊗ compose | ⊔ merge | class / ⊕ | status |
|---|---|---|---|---|---|
| `tillGrades` (time) | ℚ≥0 | `+` | `max` | order / min-prune | live — `calculus/till/calculus-config.js` |
| `distGrades` (distance) | ℚ≥0 | `+` | `max` (unused single-input, R2) | order / min-prune | live — `calculus/gill/calculus-config.js` (P3) |
| usage | ℕ | `+` | `+` (consumption, R2) | order | future |
| `weightGrades` (weight) | ℚ≥0 | `·` | `·` | measure / sum \| sample | live — `calculus/gill/calculus-config.js` (P3b); the 0292/will handoff |

`weightGrades` (P3b) is the shipped measure instance and the 0292/will handoff:
`values.add` is its ⊗ (·), `values.sub` its ⊖ (exact ÷, null at mass 0), merge a
value-level FUNCTION slot (non-idempotent ·), and NO scheduler boundary slots
(`parseStamp` etc.) — `buildTimedConfig` rejects it at the class fence, for WHAT
it is. will's decimation loop consumes exactly this record plus
`prf.js sampleIndex`.

Time and distance are the SAME tropical algebra under different physical readings
(stamp = availability instant vs accumulated haul cost) — that identity is the
central audit result: shortest path needs no join swap, the scheduler's ⊕ order
realization (min-activation firing + B&B) IS Dijkstra on one-shot-edge programs
(`tests/engine/gill-dist.test.js` property-tests settle ≡ exact Dijkstra). gill
keys its algebras BY GRADE SORT (`gradeRegistry.bySort`: delay → time, dist →
distGrades; `gradeAlgebraFor(conn)` routes by the connective's grade argument —
haul `!!_d` → dist, monad `{}@d` → delay); D1 single-axis: `cc.grades` stays the
one active scheduling axis per run.

## Realization in till

Since the 0284 audit, `tillGrades` IS the canonical flat shape: a `values` face (the
label value algebra over `[n,d]` BigInt pairs — THY_0024) plus boundary slots
(`isStamp`/`parseStamp`/`canonStamp`) and the algebra-wide `aggregate = { class:
'order', realizations: ['prune'] }`. The stamp-HASH faces (`availability.cmp`,
`effect.{unit,compose,residual}`) are no longer hand-written: `buildTimedConfig`
DERIVES them from `values` (`cmp ∘ parse`, `reify ∘ add ∘ parse`, fenced `sub`) —
coherence by construction, used only by boundary consumers (views, game, lint,
chunked slices, the prover bridge). Canonical mapping:

```js
unit     = values.unit            compose = values.add
residual = fenced values.sub      cmp     = values.cmp
```

Slots operate on VALUES; the match loop operates on stamp IDS. The StampTable
(`lib/timed/labels.js`) is the id-level face: `stamps.merge` lifts the ⊔ slot to
ids and `stamps.prunes` is the contract-fixed ⊕ cut (cmp ≥ 0 — `>=` keeps the
FIRST match at equal grade, the FIFO half of timed.js's invariant pair); timed.js
routes the audited sites through both. The symbolic `merge: 'join'` names the
realization the table runs on its cached-float id cmp — the exact pre-P1 code path,
so declaring it costs nothing (a cmp-derived realization at the value level would
trade the float cache for exact BigInt cmp per call, a measured ~20-30% settle
regression). A FUNCTION slot is a custom value-level realization (usage `+`, weight
`·`): an argument returned by reference keeps its id, a created value interns — and
it runs even at EQUAL ids (the `a === b` identity shortcut belongs to the join
realization only; a non-idempotent merge has w ⊔ w = w², the P3b weight instance
caught this). An absent merge defaults to `'join'`; any other slot value — and any
declared `prunes` — throws at table construction. The conformance harness
canonicalizes the symbolic slot back into a function for property-checking and
smoke-tests the derived hash faces.

## Aggregation-policy routing (P1b)

The ⊕ policy is routed, not assumed. `buildTimedConfig` reads `grades.aggregate`
(absent = order/prune, the pre-contract default) and accepts only `class: 'order'` —
the timed scheduler IS the order-class realization (min-activation firing + B&B prune),
and running a measure algebra on it would silently discard mass (M1), so the fence is
loud. Measure-class aggregation over whole derivations is an execution mode, not a
scheduler policy; it arrives with will/0292.

The `'sample'` realization is `lib/engine/prf.js`: the stateless PRF family (D17 —
`mix32`/`thetaHash`/`strHash`, moved verbatim from timed.js; the settle-determinism
pins depend on the exact mixes) plus `sampleIndex(u32, n, weightAt, total)` — the
exact-rational cumulative-interval draw. Interval lengths are renormalized masses
(unbiased, THY_0026 T3); a zero-mass alternative has an empty interval; `total =
[1n, 1n]` keeps evaluation lazy for validated distributions (timed woplus fire-time
weights). The timed conflict chooser and `_sampleAlt` compose their draw inputs from
this family, and will's decimation loop consumes the same module — one draw semantics,
two hosts. The harness's M3 check runs sampling through `sampleIndex` itself, so the
conformance case exercises the realization the engine actually ships.

## Links

TODO_0284 (phases; this doc = P0) · TODO_0292/`will` (the measure-class consumer) ·
`doc/paper/settle-optimality.md` (the theorem this contract's conditions license — T1/T2,
the choice-freedom/contention-freedom split, termination) ·
RES_0137 (graded modal theory) · RES_0138 (prior art + settle-optimality scoping note) ·
THY_0026 (∃_ρ, measure semiring, T1–T4) · THY_0022 (fenced grade algebras) ·
`doc/documentation/till.md` · harness: `tests/engine/grade-conformance.test.js`.
