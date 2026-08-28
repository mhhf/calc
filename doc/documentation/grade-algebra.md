# Grade Algebra — the pluggable-grade engine contract

What a grade algebra must provide so the timed engine (`lib/engine/timed/`) can be
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
  prunes: (partial, best) => bool,  // order class ONLY; default cmp(partial, best) >= 0
};
```

`prunes` is undefined for `class: 'measure'` — a measure algebra never discards an
alternative (mass conservation, below).

An engine-facing value algebra may declare a canonical realization SYMBOLICALLY —
`merge: 'join'` (max by cmp) and `prunes: 'geq'` (cmp ≥ 0) — instead of supplying the
function; the StampTable id-lift recognizes the names and runs them on its cached-float
cmp fast path (see "Realization in till" below).

## Two operators, two roles

The critical distinction (TODO_0284 v3 audit): grade combination WITHIN one derivation
and aggregation ACROSS alternative derivations are different operators, and the engine
realizes them at different sites.

| role | operator | engine site (timed.js, drift-prone — roles are the contract) |
|---|---|---|
| ⊗ sequential | `compose` | rule delay: `done = stamps.compose(activation, delay)` (fire) |
| ⊔ tensor-merge | `merge` | after-window join `:211`; counted-spread `:308`/`:323`; single-row `:368` — activation = merge of all consumed stamps |
| ⊕ aggregate | `aggregate` | order: B&B prune `:247` + strict-`<` best keep `:224` · measure: settleExplore mass sum / PRF sample |

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
| `distGrades` (distance) | ℚ≥0 | `+` | `max` (unused single-input, R2) | order / min-prune | P3 — gill prelude |
| usage | ℕ | `+` | `+` (consumption, R2) | order | future |
| `weightGrades` (weight) | ℚ≥0 | `·` | `·` | measure / sum \| sample | P3b — gill prelude; harness fixture today |

## Realization in till

`tillGrades` predates this contract and exposes three faces, not the canonical flat
shape: `availability`/`effect` (stamp-hash face, the boundary/theory side) and `values`
(the label value algebra over `[n,d]` BigInt pairs — THY_0024). The *runtime* algebra
is `values`, and since P1 it carries the named slots: `values.merge = 'join'` and
`values.prunes = 'geq'` — SYMBOLIC declarations of the canonical order realizations
(max by cmp / cmp ≥ 0), plus algebra-wide `tillGrades.aggregate = { class: 'order',
realizations: ['prune'] }`. Canonical mapping of the remaining slots:

```js
unit     = values.unit            compose = values.add
residual = fenced values.sub      cmp     = values.cmp
```

Slots operate on VALUES; the match loop operates on stamp IDS. The StampTable
(`lib/engine/labels.js`) is the id-level face: `stamps.merge`/`stamps.prunes` lift the
slots to ids, and timed.js routes the audited sites through the lifts. A symbolic slot
names a realization the table runs on its cached-float id cmp — the exact pre-P1 code
path, so declaring `'join'`/`'geq'` costs nothing (this is why the slots are symbolic:
a cmp-derived realization at the value level would trade the float cache for exact
BigInt cmp per call, a measured ~20-30% settle regression). A FUNCTION slot is a custom
value-level realization (usage `+`, weight `·`): an argument returned by reference
keeps its id, a created value interns. Absent slots default to `'join'`/`'geq'` —
parity for algebras predating the contract; any other slot value throws at table
construction. The conformance harness canonicalizes symbolic slots back into functions
for property-checking. Coherence between the hash face and the value face
(`effect.compose` ≡ `reify ∘ add ∘ parse`) is checked by the harness.

## Links

TODO_0284 (phases; this doc = P0) · TODO_0292/`will` (the measure-class consumer) ·
RES_0137 (graded modal theory) · RES_0138 (prior art + settle-optimality theorem) ·
THY_0026 (∃_ρ, measure semiring, T1–T4) · THY_0022 (fenced grade algebras) ·
`doc/documentation/till.md` · harness: `tests/engine/grade-conformance.test.js`.
