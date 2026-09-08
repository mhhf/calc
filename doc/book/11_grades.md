---
title: "Counting the Bang: Grades"
part: 3
partTitle: Time and Space
chapter: 11
summary: The plain bang hides a grade — 0, 1, or ω — controlling how many copies a rule consumes. !_k A parcels out exactly k copies; !_W A claims them all at once.
---

Chapter 5 introduced `!P` as an unlimited license: dereliction, copy, and promotion let you use it any number of times.
That "any number" is the grade, and in till it becomes concrete: you can ask for exactly 2 logs, or 5 planks, or all of a cohort.

## Three grades: 0, 1, and ω

Every bang is actually `bang(grade, formula)`.
Plain `!A` is shorthand for grade ω — unlimited.
Two special grades sit at the other end:

| Syntax | Grade | What it means |
|---|---|---|
| `!_0 A` | 0 | **compile-time only** — erased before runtime; used to state rewrite lemmas that the engine folds away |
| `A` (no bang) | 1 | **linear** — consumed exactly once |
| `!A` or `!_ω A` | ω | **persistent** — may be copied and discarded freely |

The partial order is: $0 \leq \omega$ and $1 \leq \omega$, but 0 and 1 are incomparable (you cannot substitute a compile-time hypothesis for a runtime linear one, or vice versa).

## Counted parcels: `!_k A`

Between grade-1 (one copy) and grade-ω (unlimited) lies the counted parcel.

```ill
pair: !_2 log -o { bundle }.
```

This rule **takes exactly 2 logs** — no more, no fewer — and produces one bundle.
It fires as many times as possible on the available stock.

Start with 5 logs and fire `pair` as often as you can:

- fire 1: consume log₁, log₂ → bundle
- fire 2: consume log₃, log₄ → bundle
- 1 log remains — not enough to form another pair

The residual log is not wasted, not an error. The engine simply stops because no rule matches.

### Any ages

`!_k A` binds **no stamp**.
When logs arrive at different times, the engine spreads the take across cohorts oldest-first, so two logs at $t=0$ and $t=1$ can still form one bundle.
The bundle's stamp is the newest of the consumed copies.

```ill
#expect_split_spread (settle: 5)
  log * !_2 log@1 * log@3
  =>
  bundle@1 * bundle@3 .
```

The first bundle pairs the $t=0$ log with one $t=1$ log (activation = $t=1$).
The remaining $t=1$ log pairs with the $t=3$ log to form the second bundle.

## Whole-cohort bind: `!_W A`

The variable form `!_W A` takes **every copy of A that exists at firing time**.
`W` is bound to that count.

```ill
sawmill: $sawmill * !_W wood@T * !mul W 3 T2 * !div T2 2 Y -o { !_Y plank }@10.
```

Line by line:

| Fragment | Role |
|---|---|
| `$sawmill` | preserve the sawmill (consumed and re-produced) |
| `!_W wood@T` | take the **entire cohort** of wood at stamp T; W = cohort size |
| `!mul W 3 T2` | T2 = W × 3 (arithmetic on the bound count) |
| `!div T2 2 Y` | Y = T2 ÷ 2 = ⌊3W/2⌋ planks to produce |
| `{ !_Y plank }@10` | deliver Y planks, 10 time-units later |

When W = 3 the sawmill yields 4 planks; when W = 5 it yields 7.

### The starvation trap

`!_W A` matches in-flight cohorts that a producer **just scheduled**.
A cap rule like

```ill
cap: !_W g * !lt CAP W -o { !_200 g }.
```

re-activates on every new arrival because `W` grows with each incoming `g`.
Under a whole-bind, the rule can fire **before** the system ever stabilises.
A deterministic chooser may service it forever, starving everything else.

**Fix**: use a counted take instead.

```ill
safe_cap: !_201 g -o { !_200 g }.
```

This fires oldest-first, costs exactly 201 copies, and halts cleanly when fewer exist.
Starvation is impossible because each firing strictly decreases the stock.

## Fused sugar

till provides one convenience syntax: a numeral fused to a resource name.

```ill
4wood        % the same as !_4 wood
```

One lexer token, no spaces.
Spaced `4 wood` is juxtaposition (application) and means something different.
`4wood@3` is a **parse error** — write `!_4 wood@3` when you need a stamp.

## Grades in action: the lumber scenario

The file below runs the three patterns from this chapter.
`expect_split_residual` seeds the engine with 5 logs; the `pair` rule fires twice and halts with 2 bundles and 1 remaining log.

```{game till}
file: calculus/till/tests/forward/grades.ill
init: expect_split_residual
title: Parcelling logs into bundles
```

Use the timeline to watch each firing step.
Notice that the engine stops as soon as no rule can match — the leftover log is preserved, not discarded.

## Exercises

```{exercise, title=Dereliction still works at grade ω}
The graded bang at grade ω is the plain `!` from chapter 5.
Prove that a persistent resource still yields a linear copy.
```

```{prove}
goal: !P |- P
title: Grade ω: one use from an unlimited license
hint: Apply dereliction to extract a linear copy of P.
id: ch11-derelict
rules: dereliction, id
```

```{exercise, title=Two copies from one persistent resource}
Grade ω allows contraction — you can take two copies from one bang.
```

```{prove}
goal: !P, !P |- P * P
title: Two copies, one per bang
hint: Absorb each !P, copy once from each, then close the tensor branches.
id: ch11-two-copies
rules: absorption, copy, tensor_r, id
```

```{exercise, title=A pipeline through a reusable function}
A rule `!(a -o b)` acts exactly like a persistent clause: fire it once per `a` you have.
```

```{prove}
goal: !(a -o b), !(b -o c), a |- c
title: Reusable two-step pipeline at grade ω
hint: Absorb the two lolis, copy each, then chain them on a.
id: ch11-pipeline
rules: absorption, copy, loli_l, dereliction, id
```

## Quiz

```{quiz, id=ch11-q1}
Q: You have 7 logs and the rule `!_3 log -o { lumber }`. How many times does the rule fire, and how many logs remain?
- [ ] fires 3 times, 0 logs remain
- [x] fires 2 times, 1 log remains
- [ ] fires 7 times, 0 logs remain
- [ ] fires 1 time, 4 logs remain
explanation: Each firing takes exactly 3 logs. 7 ÷ 3 = 2 remainder 1 — so the rule fires twice (consuming 6 logs) and 1 log is left over.

Q: What does `!_W wood@T` bind?
- [ ] the number of distinct stamps in the state
- [ ] the next wood that will arrive in the future
- [x] the size of the entire wood cohort at stamp T, and W = that count
- [ ] W is always the constant ω
explanation: The variable W in `!_W wood@T` is bound at firing time to the number of wood tokens in the cohort at stamp T. This is the whole-cohort bind.

Q: Why can a whole-cohort bind (`!_W A`) cause starvation?
- [ ] it deletes all copies permanently
- [ ] it converts A to grade 0
- [x] it matches in-flight arrivals and re-activates on every new one, so a chooser may service it forever
- [ ] grade ω rules always take priority
explanation: `!_W A` includes cohorts that have just been scheduled but not yet settled. If a producer keeps adding to the cohort, the rule keeps firing — potentially blocking all other rules. A counted take (`!_k A`) is starvation-free because it strictly decreases the stock each time.

Q: Which syntax is valid fused sugar in till?
- [x] `4wood` (equivalent to `!_4 wood`)
- [ ] `4 wood` (space between numeral and name)
- [ ] `4wood@3` (stamped fused sugar)
- [ ] `!_ω wood` is the same as `4wood`
explanation: Fused sugar `4wood` is a single lexer token meaning `!_4 wood`. Spaced `4 wood` is application juxtaposition. `4wood@3` is a parse error — write `!_4 wood@3` instead.
```

## What you learned

- `bang(grade, A)` is the underlying form. `!A` is shorthand for grade ω.
- **Grade 0** (`!_0 A`): erased at compile time, used for rewrite lemmas.
- **Grade 1** (plain `A`): consumed exactly once — the ordinary linear resource.
- **Grade ω** (`!A`): persistent, copyable, and discardable.
- **Counted parcel** (`!_k A`): takes exactly k copies of A, spread across any stamps oldest-first.
- **Whole-cohort bind** (`!_W A`): takes all copies; W is bound to the count. Risky with arrivals — use a counted take to avoid starvation.
- Fused sugar `4wood` is `!_4 wood` in a single token.

## Going deeper

- [[documentation/sell-graded-modality|SELL graded modality implementation]] — how `bang(grade, A)` is parsed, compiled, and filtered at runtime
- [[documentation/grade-algebra|Grade algebra]] — the full grade semiring and how arithmetic rules like `!mul` operate on bound counts
- [[theory/0015_graded-indexed-monad|Graded indexed monad]] — the theoretical foundation for indexed and graded exponentials
- [[theory/0018_delay-graded-lax-monad|Delay-graded lax monad]] — how till combines time delays with the graded monad `{ A }@d`
