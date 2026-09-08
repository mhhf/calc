---
title: "Weighted Choice"
part: 4
partTitle: Chance
chapter: 15
summary: How oplus gains weights to express probability — woplus lets the producer pick a branch with a declared rational weight, settle samples one outcome, and settleExplore enumerates both with exact rationals.
---

Chapter 10 showed how `oplus` splits a forward run into two separate worlds —
but it gave both worlds equal standing.
This chapter adds **weights**: the producer picks a branch with a declared
probability, and the engine can either sample one outcome or enumerate all of
them with exact rational weights.

## The problem with equal choice

Imagine a coin flip.
You want to model it as a rule: spend a `coin`, get either `heads` or `tails`.
You could write:

```
flip: coin -o { heads + tails }.
```

This says the producer picks one branch — but it says nothing about *how often*
it picks each one.
Is the coin fair?
Loaded?
The `+` (oplus) connective carries no weight information at all.

To model a fair coin you need to declare: "heads with probability $\frac{1}{2}$,
tails with probability $\frac{1}{2}$."
That is exactly what `woplus` does.

## woplus: weighted internal choice

`woplus W A B` is the **weighted** variant of internal choice.

- The producer picks branch `A` with weight $W$.
- The producer picks branch `B` with weight $1 - W$.
- $W$ is a rational number in $[0, 1]$, written as a literal fraction.

```
woplus 1/2 heads tails
```

Read: "heads with weight $\frac{1}{2}$, tails with weight $\frac{1}{2}$."

The rule for a fair coin:

```
flip: coin -o { woplus 1/2 heads tails }.
```

Weights are **ratios**, not probabilities yet.
`woplus 3 rock sci` is invalid — the weight must be in $[0,1]$.
`woplus 3/4 rock sci` says "rock with probability $\frac{3}{4}$, scissors with
probability $\frac{1}{4}$."
Only at the end, when you sum all leaf weights in an exploration tree, do you
normalize — and they sum to exactly $1$ (mass conservation).

```{quiz, id=ch15-q1}
Q: A rule says `woplus 2/3 win lose`. What is the weight of the `lose` branch?
- [ ] 2/3
- [x] 1/3
- [ ] 1/2
- [ ] 0
explanation: woplus W A B gives B the complementary weight 1 − W. Here 1 − 2/3 = 1/3.

Q: You write `woplus 5/4 A B`. What does the engine do?
- [ ] Normalizes the weights to 5/9 and 4/9.
- [x] Rejects it at load time — the weight must be in [0, 1].
- [ ] Silently clamps to 1.
- [ ] Treats it as a uniform choice.
explanation: The weight must be a rational in [0, 1]. An out-of-range value is a loud compile error.
```

## Two ways to run a weighted program

When a rule fires and produces `woplus W A B`, the forward engine has two modes:

**settle (sample):**
Pick ONE branch.
The choice is made by a deterministic pseudorandom function seeded by a number
you supply.
The same seed always gives the same branch sequence — the run is **replay-identical**.
Different seeds give different outcomes.

**settleExplore (exact):**
Expand BOTH branches.
Build a tree where every fork carries its exact rational weight.
Every leaf carries the **product** of all branch weights on its path.
The leaf weights sum to exactly $1$ — the tree IS the distribution.

For a single coin flip, `settleExplore` produces two leaves:
one labelled `heads` with weight $\frac{1}{2}$, one labelled `tails` with weight $\frac{1}{2}$.

```{quiz, id=ch15-q2}
Q: You call settle with seed 7. The coin always lands heads. What does seed 8 return?
- [ ] Also heads, because the rule always chooses the first branch.
- [x] Either heads or tails — different seeds give different sampled outcomes.
- [ ] An error, because seeds must be even.
- [ ] The exact distribution across both branches.
explanation: settle samples ONE branch per seed. Different seeds index different draws from the distribution. The same seed always replays identically.

Q: You call settleExplore on a program with three independent woplus 1/2 choices. How many leaves does the exploration tree have?
- [ ] 2
- [ ] 3
- [x] 8
- [ ] 6
explanation: Each independent woplus doubles the number of leaves. Three independent choices give 2³ = 8 leaves, each with weight (1/2)³ = 1/8. Their sum is 8 × 1/8 = 1 (mass conservation).
```

## A coin-flip widget

The program below has one rule: consume a `coin`, produce `heads` or `tails`
with equal probability.
The `@1` delay means the outcome arrives one time unit after the coin is spent.

```{game till}
file: doc/book/programs/flip.till
title: Fair coin flip
```

When the widget opens you see the outcome already in-flight (the coin was spent
at $t = 0$, the result arrives at $t = 1$).
Click **Settle to 1s** to reveal it.
The settled outcome is determined by the session's default seed; a different seed
gives a different result with probability $\frac{1}{2}$.

## Weights from data: the duel

A richer use of `woplus` is when the weight is **read from the state** rather
than written literally.
The file `calculus/till/game/combat.till` models stochastic combat as a single
rule:

```
duel:
  red(U) * blue(V) * !winprob U V Q
  -o { woplus Q (red(U)  * fellb(V))
                (blue(V) * fellr(U)) }.
```

One unit is picked from each side.
The weight $Q$ is looked up from the persistent fact `!winprob U V Q` — a table
that maps unit-type pairs to win probabilities.
For example, `rock` beats `scissors` with probability $\frac{3}{4}$:

```
winprob rock sci (3/4).
```

The rule fires repeatedly until one side is empty.
Each firing introduces one `woplus` node.
`settle` samples a full battle outcome in one seeded run.
`settleExplore` expands the entire outcome tree: every leaf is one possible
sequence of deaths, and its weight is the product of the per-round probabilities.

The aggregate weight of leaves where `rock` survives equals exactly the
absorbing Markov chain probability — computed in exact rational arithmetic, with
no floating-point drift.
For one rock versus two scissors the probability is $\frac{9}{16}$.

```{quiz, id=ch15-q3}
Q: In the duel, `!winprob rock sci Q` binds Q to 3/4. What does `!` mean on that premise?
- [x] The fact is persistent — it is read but not consumed, so it can be used in every fight.
- [ ] The weight is negated: 1 − 3/4 = 1/4.
- [ ] The fact lives in a separate zone and cannot be matched.
- [ ] It marks the weight as non-deterministic.
explanation: `!` is the bang (exponential) connective. A persistent `!P` fact can be read as many times as needed without being consumed. Here the whole win-probability table is persistent, so every round of combat can look up the same table.

Q: settle runs a 1-rock vs 1-scissors duel 1000 times with different seeds. About how many times does rock win?
- [ ] 250
- [ ] 500
- [x] 750
- [ ] 1000
explanation: winprob rock sci (3/4) declares that rock beats scissors with probability 3/4. Over many independent seeds, about 3/4 of the runs end with rock surviving — just as a fair coin lands heads half the time over many flips.
```

## Weights are exact rationals

One key design decision: `woplus` weights are **exact rational numbers**, not
floating-point.
Both the weights declared in rules (`3/4`) and the path weights accumulated in
`settleExplore` leaves are represented as pairs of big integers.
The leaf weights sum to exactly $1$ — no rounding error, no drift over deep
trees.

This matters when you use `settleExplore` to compute probabilities analytically.
For the 1-rock vs 2-scissors duel, `settleExplore` returns a tree whose leaves
sum the path weights for "rock survives" to exactly $\frac{9}{16}$ — agreeing
with the Markov chain recurrence to the last digit, because they are computing
the same rational number by two different methods.

```{quiz, id=ch15-q4}
Q: A program has two sequential woplus steps: first woplus 1/2, then woplus 1/3. The path that takes the first branch both times has weight ___?
- [ ] 1/2 + 1/3 = 5/6
- [x] 1/2 × 1/3 = 1/6
- [ ] 1/3
- [ ] 1/2
explanation: Independent choices multiply. The path weight is the product of all branch weights on the path from the root to the leaf: 1/2 × 1/3 = 1/6.
```

## oplus vs woplus

`oplus` (`A + B`) and `woplus` (`woplus W A B`) are closely related:

- Both are **internal choice**: the producer decides, not the consumer.
- `oplus` carries no weight — in backward proof search it introduces a branch
  point where either alternative can be proved.
- `woplus` adds a weight grade: the probability of each branch is part of the
  connective's data.

In the **backward prover**, `A + B` has two right rules: prove `A`, or prove
`B`.
`woplus` has no backward rules — it exists only in consequent position inside a
monad body, where it is expanded by the forward engine.

```{prove}
goal: A |- A + B
title: oplus right 1
hint: The resource A proves the left branch of A + B.
id: ch15-prove1
rules: oplus_r1
```

```{prove}
goal: B |- A + B
title: oplus right 2
hint: B proves the right branch.
id: ch15-prove2
rules: oplus_r2
```

These sequents use `oplus` (unweighted).
There is no sequent rule for `woplus` in the backward calculus — it is
exclusively a probabilistic choice in forward programs.

## What you learned

- `woplus W A B` is **weighted internal choice**: the producer picks `A` with
  weight $W$ and `B` with weight $1 - W$, where $W$ is an exact rational in
  $[0, 1]$.
- `settle` **samples** one branch per seeded run — the same seed always
  replays the same sequence.
- `settleExplore` **enumerates** both branches, assigning exact rational path
  weights; the leaf weights sum to exactly $1$ (mass conservation).
- Weights can be **read from data** at fire time (the duel's `!winprob U V Q`),
  not just written as literals.
- `woplus` has **no backward rules** — it lives only in forward consequents.
  Ordinary `oplus` is its unweighted sibling, used in proof search.

## Going deeper

- [[theory/weighted-additive-disjunction|THY_0021: weighted additive disjunction]] — the formal proof theory: probability-graded right rules, mass conservation theorem, and the absorbing-chain correspondence.
- [[theory/0004_symbolic-branching|THY_0004: symbolic branching]] — the unweighted parent `oplus` and how branching worlds arise in exhaustive exploration.
- [[theory/0019_timed-matching-settle|THY_0019: timed matching and settle]] — the PRF sampler, horizon-split invariance, and how `settleExplore` produces the exact distribution tree.
- [[docs/till|till reference]] — the full till calculus documentation including the `woplus` compile fence and the D17 branch-draw PRF.
