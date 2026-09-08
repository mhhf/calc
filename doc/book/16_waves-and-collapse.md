---
title: "Waves and Collapse"
part: 4
partTitle: Chance
chapter: 16
summary: An undetermined value — "exists T: tile_t @w. tile C T" — is a WAVE whose members carry prior weights. The decimation driver draws waves in entropy order and propagates bias constraints, realizing Wave Function Collapse as graded linear rewriting.
---

Chapter 13 showed that settle fires the earliest-enabled rule first.
This chapter asks a different question: what if a rule's output is **not yet decided**?
Sometimes the right value is genuinely unknown and should be chosen probabilistically,
respecting weights we declare in advance.
That is the idea behind a wave.

## A cell that is not yet determined

Imagine a 1D beach with four cells numbered 0–3.
Each cell must be one of three tile types: sea, coast, or land.
But we do not want to assign them all upfront.
We want the system to choose, guided by weights and constraints.

Here is the declaration for one cell:

```
exists T: tile_t @w. tile c0 T
```

Read it as: "there exists a tile type `T` for cell `c0`, drawn with weight."
The `@w` marks this as a **weighted existential** — a wave.

Under plain `settle` this formula is **inert**: no rule fires and no value is chosen.
The wave just suspends, waiting for the decimation driver to open it.

## Priors: declaring member weights

The tile type classifier lists its members and their prior weights:

In `WFC.will` the declarations look like this:

```
tile_t: sort.
sea:   tile_t @w 2.
coast: tile_t @w 1.
land:  tile_t @w 2.
```

Member `sea` has weight 2, `coast` has weight 1, `land` has weight 2.
Weights are unnormalized rationals.
To draw from an open wave, the driver samples proportionally: sea and land
are each twice as likely as coast.

## Entropy: how undetermined is a wave?

Given weights $w_i$ for the live members, the normalized probability of member $i$ is
$p_i = w_i / \sum_j w_j$.
The **Shannon entropy** of the wave is

$$H = -\sum_i p_i \log p_i.$$

An open wave over three equal-weight members has maximum entropy.
A wave where one member has been forbidden — its effective weight zeroed to 0 — has
lower entropy.
A wave with only one live member has entropy 0: it is determined.

The decimation driver always picks the **lowest-entropy wave first**.
This is the min-entropy heuristic: commit to the most constrained choice before the
least constrained one, maximizing the information each draw carries to its neighbors.

```{quiz, id=ch16-q1}
Q: Why does the driver pick the *lowest*-entropy wave first, not the highest?
- [x] The most constrained wave is least likely to cause a contradiction if drawn early; drawing it first propagates the most information to neighbors.
- [ ] Lower entropy means more choices, so there is more to gain.
- [ ] Higher-entropy waves are reserved for later because they are easier.
- [ ] The order does not matter — any wave can be drawn in any order.
explanation: A wave with few live members (low entropy) is already tightly constrained by its neighbors. Drawing it first propagates that constraint outward, often reducing the entropy of adjacent waves before they are drawn. This greedy policy minimizes the risk of later contradictions.
```

## Constraints as bias rules

The WFC beach has one constraint: sea and land may never be adjacent.
We express this as a pair of persistent forbid facts:

```
forbid/sl: forbid sea land.
forbid/ls: forbid land sea.
```

When cell C collapses to tile `T`, a **propagation rule** checks whether `T` forbids
any tile `T'` at the neighbor C'.
If so, it sends a bias fact that zeros out `T'` in C's wave:

```
constrain:
  guard C C' * $tile C T * !forbid T T' * $tile C' X
  -o { !bias X T' 0 }.
```

`guard C C'` is a **linear trigger token** consumed when propagation fires.
Persistent-conclusion rules (those that only produce `!` facts) would loop forever on
the same token; the guard ensures each adjacency edge fires propagation at most once per
collapse event.

The bias fact `!bias X T' 0` reaches the neighbor's wave evar `X` and sets the weight
of `T'` to 0.
The posterior probability of each member is $p_i \propto \text{prior}_i \times \prod \text{bias factors}$.
A member with any zero bias factor drops out of the distribution entirely.

## The decimation loop

The driver repeats four steps until all waves are ground:

1. **Pick** the open wave with the lowest entropy.
2. **Draw** a member — sample proportionally from the remaining weighted members,
   using a pseudorandom function seeded by the run seed.
3. **Substitute** the drawn value and run `settle` — this fires propagation rules,
   sending bias facts to neighbors and potentially lowering their entropy.
4. **Repeat** from step 1 with the updated wave table.

If step 1 finds a wave with **zero total weight** (all members forbidden), that is a
**contradiction**.
No tile is possible — the constraint set is unsatisfiable for this partial assignment.
The driver restarts from scratch with a fresh attempt, keeping the same seed but
exploring a different draw path.

```{quiz, id=ch16-q2}
Q: A wave for cell `c2` has prior weights sea:2, coast:1, land:2. After collapse, `c1` becomes sea. The constraint forbids sea–land adjacency. What is the new effective distribution for `c2`?
- [ ] sea:2, coast:1, land:2 — bias only affects the drawn cell, not its neighbor.
- [ ] sea:2, coast:1, land:0 — land is zeroed out; sea:2/5, coast:1/5 after normalization.
- [x] sea:2, coast:1, land:0 — land is eliminated; probabilities renormalize to sea:2/3, coast:1/3.
- [ ] Everything becomes uniform after a neighbor collapses.
explanation: The propagation rule fires because c1=sea and forbid sea land holds. It sends !bias X land 0 to c2's evar X, zeroing land's weight. The remaining weights sea:2 and coast:1 renormalize. Land can never appear adjacent to sea.
```

## The collapse widget

The widget below runs the WFC beach program with seed 3.
Four cells start as open waves, all with the same entropy ($\approx 1.055$ nats).
The tiles are sea, coast, and land with priors 2:1:2.

Use the **step** button to watch the driver draw one wave at a time.
After each draw, notice how the neighbor menus shrink: a sea neighbor loses land as an
option; a land neighbor loses sea.
Hit **auto** to let the driver finish the entire beach in one go.

```{collapse will}
file: calculus/will/game/WFC.will
seed: 3
title: Beach WFC — four cells, three tiles
```

```{exercise, title=Count the restarts}
Run the widget with seed 3 all the way to a completed beach.
How many draws did the driver make?
Were there any restarts?
Then try seed 7.
Does the final beach differ?
```

```{solution}
With seed 3 the driver makes exactly 4 draws — one per cell — and reaches a valid
assignment without any restarts.
The 1D constraint (sea–land never adjacent) is arc-consistent: after any single
collapse, the remaining waves always have at least one live member.
With seed 7 the beach will look different (a different sequence of draws), but will
also complete without restarts for the same reason.
```

## Inside WFC.will: the key lines

Here is the complete program, with comments pointing to the concepts above:

```
% Members of tile_t with prior weights 2, 1, 2.
tile_t: sort.
sea:   tile_t @w 2.
coast: tile_t @w 1.
land:  tile_t @w 2.

% The constraint: sea and land may not be adjacent.
forbid/sl: forbid sea land.
forbid/ls: forbid land sea.

% spawn: turn each mk token into one suspended wave.
% The @w marks it as a weighted existential — a wave.
spawn: mk C -o { exists T: tile_t @w. tile C T }.

% constrain: when C collapses to T, zero out T' in neighbor C'
% if forbid T T' holds. guard C C' is the one-shot trigger.
constrain:
  guard C C' * $tile C T * !forbid T T' * $tile C' X
  -o { !bias X T' 0 }.
```

That is the whole program.
Two tile declarations, one constraint pair, one wave rule, one propagation rule.
The decimation driver — the part that picks lowest-entropy, draws, and restarts on
contradiction — is built into the engine and needs no program code.

## What makes this Wave Function Collapse

The original WFC algorithm (Gumin 2016) works over a grid of pattern tiles with
adjacency rules derived from a sample image.
It also maintains a set of allowed patterns per cell, picks the cell with the fewest
remaining options, collapses it to one, and propagates the elimination forward.

In CALC's formulation:
- The **cell's wave** is the graded existential `exists T: tile_t @w. tile C T`.
- The **allowed set** is the set of members with positive posterior weight.
- **Arc consistency** is the propagation rule firing on `guard` tokens.
- **Collapse** is a single draw step by the decimation driver.
- **Restart** is M9: a fresh attempt from the same seed when contradiction is found.

No extra machinery is needed — it falls out of the `∃_ρ` surface and the bias discipline.

## What you learned

- A **wave** is a weighted existential `exists T: s @w. A`: a suspended formula whose
  witness will be drawn by the decimation driver.
- **Priors** `c: s @w n.` assign unnormalized rational weights to classifier members.
- **Entropy** $H = -\sum p_i \log p_i$ measures how undetermined a wave is;
  the driver always picks the **lowest-entropy** wave next.
- **Bias facts** `!bias X T' 0` zero out forbidden members in a neighbor wave,
  reducing its posterior distribution.
- The **decimation loop** is: pick min-entropy, draw, settle (propagate), repeat.
- A **contradiction** — a wave with zero total weight — triggers a **restart** (M9):
  a fresh draw attempt with the same seed.
- Wave Function Collapse is exactly this loop, with adjacency constraints as bias rules.

## Going deeper

- [[theory/0026_probability-graded-existential|THY_0026: the probability-graded existential]] — the formal theory behind `∃_ρ`, including the adequacy theorem, subcriticality (almost-sure termination), and the importance-weighted sampler.
- [[theory/0020_refinement-sorts|THY_0020: refinement sorts]] — how `tile_t: sort.` and `sea: tile_t @w 2.` define a datasort whose members are the wave's sample space and whose inside mass is the partition function.
- [[documentation/forward-chaining-engine|forward chaining engine]] — the three-layer (generic / family / calculus) architecture that the decimation driver sits atop, and how `calc.collapse` drives the settle loop from outside.
