---
title: "Time as a Grade: till"
part: 3
partTitle: Time and Space
chapter: 12
summary: How timed ILL attaches availability stamps and delay grades to resources, turning production chains into scheduled firing sequences.
---

Chapter 6 showed how CALC searches for proofs automatically.
This chapter adds a new dimension: **time**.
Instead of asking "can this be proved?", we ask "when does each resource become available?".

## The problem with timeless resources

Imagine a sawmill that turns wood into planks.
In pure ILL you write:

```{calc}
sawmill * wood -o plank
```

The rule says: consume a sawmill and a log, produce a plank.
But nothing says *how long* it takes.
Is the plank ready instantly?
After one second?
After an hour?

For games, simulations, and scheduling problems you need answers to those questions.
**till** (Timed ILL) adds exactly that.

## Two new annotations

till extends ILL with two tiny additions.

### 1. Availability stamps: `A@t`

Writing `wood@3` means: *this log becomes available at time 3*.
A fact without a stamp defaults to time 0 — it is available immediately.

You can picture it as a delivery: the log is on its way and arrives at $t = 3$.

### 2. Delay grades: `{B}@d`

The consequent `{ plank }@(1/2)` means: *producing a plank takes 1/2 time unit*.
The curly braces are the **lax monad** from Chapter 8; here the grade `d` is a duration.
`{B}` with no annotation means zero delay.

### Firing arithmetic

When a rule fires, CALC computes the **activation time**:

$$a = \max(\text{stamps of all consumed inputs})$$

You wait for the *latest* ingredient.
Outputs then arrive at $a + d$ (activation plus delay).

This max-then-add structure is the **tropical semiring** — the same algebra used in scheduling theory.

```{quiz, id=ch12-q1}
Q: A rule consumes `wood@3` and `stone@7` and has delay `5`. When does its output arrive?
- [ ] 8 (3 + 5)
- [ ] 12 (7 + 5)
- [x] 12 (max(3,7) + 5 = 7 + 5)
- [ ] 15 (3 + 7 + 5)
explanation: Activation = max of input stamps = 7. Output stamp = activation + delay = 7 + 5 = 12.
```

## The single-server idiom: `$`

A real sawmill can only process *one* log at a time.
The `$` prefix captures this:

```
$sawmill * wood -o { plank }@(1/2)
```

`$sawmill` is sugar for: consume `sawmill` on the left and re-produce it on the right.
So the sawmill token is absent from activation time until $a + d$.
Between $a$ and $a + 1/2$ the machine is **busy** — a second log cannot start.
The machine token comes back only when the job finishes.

This is a single-server queue, expressed as a linear type.

## Time windows: `after` and `before`

Sometimes a rule should only fire within a time window.

- `after E` — the rule cannot fire before time $E$.
- `before E` — the rule is cancelled if it has not fired by time $E$.

A spoilage rule for food that rots 20 time units after it appears uses:

```
food@Q * after (Q + 20) -o I
```

The variable `Q` captures the food's arrival stamp.
The `after` guard ensures the rule fires only once the food is 20 units old.

## settle(T): running the clock to T

`settle(state, T)` repeatedly fires whichever rule has the earliest activation time, as long as that time is $\leq T$.
Think of it as advancing a wall-clock from 0 to $T$ and letting every scheduled event fire in order.

The horizon $T$ is an **observation cursor**, not a resource.
Settling to $T_1$ and then to $T_2$ gives the same result as settling directly to $T_2$:

$$\text{settle}(\text{settle}(S, T_1), T_2) = \text{settle}(S, T_2) \quad \text{for } T_2 \geq T_1$$

## Watching a production chain: the economy demo

The `economy.ill` file models a sawmill and a smith.
The sawmill converts wood into planks (delay $1/2$); the smith forges planks and stone into tools (delay $3/10$).
Both start with ten units of each input.

Run it and step the clock forward:

```{game till}
file: calculus/till/tests/forward/economy.ill
title: Economy — step the clock and watch production
```

At $t = 0$ both machines fire immediately (consuming the first plank, stone, and wood).
Watch the **pending** column: it shows jobs in flight.
Advance to $t = 0.3$ — the smith's first tool lands.
Advance to $t = 0.5$ — the sawmill's first plank lands and the sawmill fires again.
The interleaving is determined entirely by the stamps and delays; no clock token ever enters the state.

```{quiz, id=ch12-q2}
Q: In economy.ill, the sawmill delay is 1/2 and the smith delay is 3/10. Which job finishes first?
- [ ] The sawmill (it has more wood to process)
- [x] The smith (delay 0.3 < delay 0.5)
- [ ] They finish at the same time
explanation: Both fire at t=0. Smith output arrives at 0+0.3=0.3, sawmill output at 0+0.5=0.5. The smith is faster.
```

## A real game: Paragon Pioneers 2

Now for the payoff.
`PP2.till` is a small resource-management game built entirely in till.
You start with raw materials and a **build menu** — a linear choice of which building to construct.

Each menu entry costs space tokens and takes time to complete.
For example, building a farm costs 5 space tokens and takes 20 time units.
Once the farm appears it harvests food automatically.

```{game till}
file: calculus/till/game/PP2.till
init: expect_shell_start
title: Paragon Pioneers 2 — build your economy
```

```{exercise, title=Build a farm and wait for food}
Open the build menu and choose **5 space ⊸ farm (20s)**.
Then step the clock forward past $t = 20$.
You should see a `farm` token appear in the state, and shortly after it starts producing `food` every 6 seconds.
Notice that the farm is a single-server: it is absent while harvesting and reappears when the food lands.
```

```{solution}
Click menu item 0 (the farm option).
Advance the horizon past 20.
The farm token appears at approximately t=20.
At t=26 the first food token arrives.
```

```{quiz, id=ch12-q3}
Q: Why does building a farm consume `space` tokens?
- [ ] Space is a clock resource that advances time.
- [x] Space tokens represent scarce construction capacity; linearity ensures you cannot build two things in the same slot.
- [ ] Space is sugar for the `after` guard.
explanation: `space` tokens are linear resources. Consuming 5 of them to build a farm means those 5 slots are occupied. You only get them back (via reclaim rules) when the building is removed.
```

```{quiz, id=ch12-q4}
Q: What does `settle(state, T)` do?
- [ ] Adds a clock token with value T to the state.
- [x] Fires every enabled rule whose activation time is ≤ T, in earliest-first order.
- [ ] Checks whether all resources arrive before time T.
- [ ] Resets the state to the initial configuration.
explanation: settle runs the timed scheduler up to the horizon T. The horizon is an observation cursor — it does not appear in the state itself.
```

## What you learned

- `A@t` stamps a resource with its **availability time**.
- `{ B }@d` marks an output that takes **d time units** to produce.
- A rule fires at the **maximum** of its input stamps; outputs arrive at activation plus delay.
- The `$machine` idiom enforces single-server behaviour: the machine is absent while busy.
- `after E` / `before E` guard a rule's activation window.
- `settle(state, T)` runs the schedule to horizon $T$, always picking the earliest pending activation.

## Going deeper

- [[theory/0018_delay-graded-lax-monad|THY_0018: delay-graded lax monad]] — the formal semantics of `{B}@d`.
- [[documentation/till|till reference]] — full API, debug tools, count grades, and weighted choice.
