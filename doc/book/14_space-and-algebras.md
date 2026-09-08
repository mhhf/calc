---
title: "Swappable Algebras, and Space: gill and sill"
part: 3
partTitle: Time and Space
chapter: 14
summary: How gill makes the grade algebra itself a swappable parameter, and how sill adds place-indexed facts whose frame property comes for free from the multiset semantics.
---

Chapter 12 added time to linear logic through availability stamps and delay grades.
This chapter asks two follow-on questions: can the same scheduling machinery run over a *different* algebra — distances instead of times?
And can resources live at *named places*, so that acting at one cell never touches another?
The answers are **gill** (Graded ILL, swappable algebras) and **sill** (Spatial ILL, located facts).

## gill — the grade algebra as data

### Same engine, different numbers

In till, every resource carries a rational time stamp $t \in \mathbb{Q}_{\geq 0}$.
The scheduler fires the rule with the earliest activation: $a = \max(t_1, t_2, \ldots)$ over its inputs, then outputs arrive at $a + d$.
This is the **(max, +) tropical semiring**.

Now suppose the stamp is a *transport cost* instead of a time.
Shipping two crates to a city requires both to arrive, so you still take the $\max$ of their costs.
But edges along a route *add* their costs, and you want the cheapest route — so across alternatives you pick $\min$.
This is the **(min, +) semiring** — Dijkstra's algebra.

Both algebras share the same shape: "wait for the last input, accumulate an edge cost."
**gill** turns this shape into a parameter.
The rules and the engine are identical; only the algebra changes.

### Grade sorts and the by-sort registry

gill declares **grade sorts** — named sub-kinds of the single `grade` type.

| Sort | Domain | Algebra | Usage |
|------|--------|---------|-------|
| `delay` | $\mathbb{Q}_{\geq 0}$ | (max, +) — time | till's production delays |
| `dist` | $\mathbb{Q}_{\geq 0}$ | (min, +) — transport cost | shortest-path routing |
| `count` | $\mathbb{N}$ | counted parcels | `!_3 wood` (three copies) |
| `weight` | $[0,1]$ | static annotation | weighted choice `A +[0.3] B` |

A **by-sort registry** maps each grade sort to its own algebra: `delay → tillGrades`, `dist → distGrades`.
Writing `{B}@d` with a `delay` value `d` schedules by time; writing `!!_d A` with a `dist` value `d` routes by transport cost.
The sequent rules are shared — the algebra is the only difference.

```
!!_5 cargo
```

This reads: "cargo reachable within haul-cost 5."
The `!!_d` comonad is gill's spatial dual of the time monad: `{A}@d` means "A achievable within duration d", `!!_d A` means "A reachable within cost d".

### Shortest-path routing in the depot

The `depot.gill` example is a shortest-path problem.
Cities are connected by roads with distance costs.
A package at city A needs to reach city D; the scheduler picks routes in increasing-cost order — exactly Dijkstra's algorithm.

```{game gill}
file: calculus/gill/tests/forward/depot.gill
title: Depot — shortest-path routing by distance grade
```

Watch the **pending** column.
Each entry shows a city name and its distance stamp.
The engine fires whichever pending delivery has the smallest accumulated distance — minimum first, because `dist` grades use the (min, +) algebra.

```{quiz, id=ch14-q1}
Q: In gill's depot, the scheduler fires deliveries in what order?
- [ ] Arbitrary — it is a multiset, order does not matter.
- [x] Increasing distance — the dist algebra picks the minimum-cost route first.
- [ ] Time order — distance grades are silently converted to timestamps.
- [ ] The order rules appear in the source file.
explanation: The dist algebra uses (min,+): pending entries are ordered by accumulated distance, and the scheduler fires the minimum-distance candidate first. This is Dijkstra's algorithm expressed as timed rewriting with a different grade sort.
```

## sill — resources live at places

### A located zone in the sequent

till and gill resources are unlocated: two `food` tokens are interchangeable.
**sill** (Spatial ILL) adds a third zone to the sequent — the **located zone** — and a new notation:

```
farm @@ l00
```

This is a `farm` resource at place `l00`.
It is completely distinct from `farm @@ l01`.
Place is part of the fact's identity, so per-cell linearity is automatic: consuming a token at `l00` cannot consume the one at `l01`.

### Rules act at a place

Here are two rules from a 2×2 grid farming simulation:

```
build: (free @@ L) * !land L -o { farm @@ L }.
gather: $(farm @@ L) * (crop @@ L) -o { good @@ L }.
```

The place variable `L` acts as a pattern: `build` fires only when the `free` token and the `land` persistent fact agree on the *same* location.
A `build` targeting `l00` consumes `free @@ l00` and produces `farm @@ l00`; nothing at any other cell is touched.
In `gather`, the `$` prefix preserves the farm (re-produced on the right), and the crop at `L` is consumed to yield a good — again, all at the same cell.

```{exercise, title=Trace the build rule}
Before building at l00 the state contains `free @@ l00` and the persistent fact `!land l00`.
After `build` fires, what tokens are in the state?
```

```{solution}
`farm @@ l00` — the `free @@ l00` token was consumed and replaced by `farm @@ l00`.
The persistent `!land l00` is never consumed (bang rules are reusable), so it remains available.
```

### The frame property is free

What happens to `free @@ l01` when you build at `l00`?
Nothing at all.

The `build` rule lists `free @@ L` in its antecedent.
Matching `L = l00` consumes `free @@ l00`.
The multiset still contains `free @@ l01`; no rule touched it.

This is the **frame property**: acting at one place leaves every other place untouched.
It requires no special axiom — it is the multiset semantics.

```{game sill}
file: calculus/sill/tests/forward/grid.sill
init: expect_frame
title: Grid farm — frame property in the 2×2 grid
```

The initial state shows `farm @@ l00` (already built) and `free @@ l01` (untouched).
Building at `l00` left `l01` intact.
No rule is currently enabled, because there is no `crop` in the state yet.

```{quiz, id=ch14-q2}
Q: In sill, why does building at l00 leave `free @@ l01` unchanged?
- [ ] A frame axiom explicitly prevents cross-cell effects.
- [ ] Located facts are protected by a type-level permission check.
- [x] The `build` rule's antecedent names `free @@ l00`; the multiset operation consumes only that element, leaving `free @@ l01` untouched.
- [ ] sill treats different places as different types and the type checker blocks cross-cell rules.
explanation: The frame property is not machinery — it is the multiset semantics. A rule consumes exactly the tokens it names. `free @@ l00` and `free @@ l01` are distinct multiset elements; consuming one does not touch the other.
```

```{quiz, id=ch14-q3}
Q: What is the sill notation for "a crop resource at cell l10"?
- [ ] `crop(l10)`
- [ ] `crop * l10`
- [x] `crop @@ l10`
- [ ] `@l10 crop`
explanation: sill uses the `A @@ L` syntax for located facts. `crop @@ l10` is a crop token whose identity includes the place l10.
```

## Product stamps: time and distance together

sill resources carry **product stamps** — pairs $(t, d)$ combining a time and a distance.
The scheduler uses **lexicographic order**: time is primary, distance breaks ties.
A resource stamped $(4, 10)$ fires before one stamped $(5, 2)$ because $4 < 5$, regardless of distance.
When two resources have equal time stamps, the one with the smaller distance fires first.

This lets a model encode both "when" and "how far" in a single stamp without conflating the two axes.

```{quiz, id=ch14-q4}
Q: sill schedules by lexicographic (time, distance) order. Which stamp fires first: (4, 10) or (5, 2)?
- [x] (4, 10) — lower time wins regardless of distance.
- [ ] (5, 2) — lower distance wins.
- [ ] (4, 10) — because its sum 4 + 10 = 14 exceeds 5 + 2 = 7, so "more combined effort" fires first.
- [ ] They tie because both encode equal total effort.
explanation: lex order: time is primary. Time 4 < 5, so (4, 10) fires first. Distance only matters when times are equal.
```

### Why conserved quantities cannot ride stamps

One tempting idea: put **fuel** in the stamp so the scheduler automatically enforces a budget.
This does not work, and the reason is fundamental.

Stamps are **cartesian** — when a rule fires with one activation stamp, that stamp is *broadcast* to every output token.
A preserved catalyst (`$machine`) re-emits the stamp unchanged.
Persistent facts (bang) can be used many times without losing their stamp.

But **conservation** is a *linear* property: the total quantity in must equal the total out.
Broadcast violates linearity at the value level — a single stamp value becomes many copies, each carrying the full amount.

The conclusion is clear: **fuel belongs in the state as a linear token**.
The multiset already enforces conservation correctly, at no extra cost.
A stamp is a scheduling coordinate, not a resource counter.

```{quiz, id=ch14-q5}
Q: Why can't a conserved quantity like fuel live inside a stamp?
- [ ] Stamps only support rational numbers; fuel might need integers.
- [ ] The scheduler ignores stamp values when computing activation.
- [x] Stamps are broadcast to every output and catalyst — one input stamp becomes many copies. Conservation requires the total to be preserved, but broadcast duplicates it. Fuel must be a linear token in the state.
- [ ] It can — this is exactly what the `count` grade sort does.
explanation: Stamp values are cartesian (freely copied across outputs). Conservation is linear (sum is preserved). Putting a conserved value in a cartesian slot double-counts at every multi-output rule and every catalyst. Fuel is a resource; keep it in the multiset.
```

## What you learned

- **gill** makes the grade algebra a swappable parameter. `delay` grades use (max, +) time scheduling; `dist` grades use (min, +) distance scheduling. The sequent rules are the same.
- A **by-sort registry** maps each grade sort to its own algebra at run time.
- **sill** adds a **located zone** to the sequent. A fact `A @@ L` is distinct from `A @@ L'` when $L \neq L'$.
- Rules match the place variable `L` across their inputs, so they fire only at a consistent location.
- The **frame property** — acting at one place leaves other places untouched — is a consequence of the multiset semantics. No extra axiom is needed.
- **Product stamps** $(t, d)$ schedule by lexicographic order: time primary, distance tie-break.
- **Conserved quantities cannot ride stamps**: stamps broadcast (cartesian), conservation is linear. Keep fuel in the state.

## Going deeper

- [[theory/0033_routed-zones-product-stamps|THY_0033: Routed zones and product stamps]] — the formal treatment of located zones and (time, dist) product scheduling.
- [[theory/0034_usage-axis-factorization|THY_0034: Usage-axis factorization]] — proof that conserved quantities cannot live in the stamp algebra, and how each usage role maps to existing machinery.
- [[documentation/grade-algebra|Grade algebras in CALC]] — the full by-sort registry and algebra interfaces.
