---
title: "Sorts, and Conditioning by Restriction"
part: 4
partTitle: Chance
chapter: 17
summary: How refinement sorts give wave binders a precise population to draw from, and why conditioning a wave on an observation means restriction — not renormalization.
---

Chapter 16 introduced the wave — a suspended weighted existential whose
member is drawn by the decimation driver.
This chapter fills in two details that make waves precise: **sorts** say
exactly which values a wave may draw, and **conditioning** says how to
narrow that population when you learn something new.

## Waves need a population

Recall the wave binder from Chapter 16.
Writing `exists T: tile_t @w. tile C T` suspends the choice of `T` until the
decimation driver opens and draws it.
The binder says what sort `T` belongs to: `tile_t`.
But what is a sort, and what are its members?

That is the question this chapter answers.

## Classifiers and membership

A **sort** in till/will is a named classifier — a way to group atomic
propositions into a finite, declared class.
You introduce one with a bare fact:

```
tile_t: sort.
```

Then you declare members:

```
sea:   tile_t @w 2.
coast: tile_t @w 1.
land:  tile_t @w 2.
```

Each line is a persistent fact of the form `member: classifier @w weight`.
The weight `@w 2` is a **constructor prior** — the base mass the decimation
driver assigns to that member before any bias rules fire.

That is all.
`tile_t`, `sea`, `coast`, and `land` are ordinary content-addressed atoms.
The sort machinery is just facts the loader reads; the engine sees no sort
at runtime — sorts are erased after load (proof irrelevance).

```{quiz, id=ch17-q1}
Q: In `sea: tile_t @w 2.`, what is `tile_t` and what is `sea`?
- [x] `tile_t` is the classifier (sort), and `sea` is a member with prior weight 2.
- [ ] `tile_t` is a resource token and `sea` is a transition rule.
- [ ] `sea` is the sort and `tile_t` is the member.
- [ ] `@w 2` is a timestamp meaning "available at time 2".
explanation: `tile_t: sort.` declares `tile_t` as a classifier. `sea: tile_t @w 2.` then asserts that `sea` belongs to `tile_t` with prior weight 2. The `@w` annotation is a constructor prior, not a grade or timestamp.
```

## Subsort edges

Sorts can nest.
The numeric tower in till's prelude is declared as a chain of edges:

```
bin <: q.
```

This means "every binary numeral is also a rational".
The line is sugar for a persistent fact `sedge bin q`.
The loader computes the **reflexive-transitive closure** of all sedge facts
at load time and injects the result as ground `subsort A B` facts:

```
subsort bin q.
subsort bin bin.   % reflexivity
subsort q q.
```

In-logic premises like `!subsort X resource` become ordinary fact lookups —
no recursive clause, no backtracking over a chain.

Subsorts and classifier membership are distinct:

| Declaration | What it says |
|---|---|
| `bin <: q.` | Every value of sort `bin` is also of sort `q` (structural refinement). |
| `sea: tile_t @w 2.` | `sea` is a **member** of the classifier `tile_t`. |

A member declaration says "this atom belongs to this class".
A subsort edge says "this sort refines that sort".
You cannot write `sea <: tile_t` — that would assert a sort-order relationship
between two atoms, not a membership.

```{quiz, id=ch17-q2}
Q: Which declaration would you write to say "every weight is also a rational"?
- [x] `weight <: q.` — a subsort edge from `weight` to `q`.
- [ ] `weight: q @w 1.` — member with prior 1.
- [ ] `q: weight.` — classifier declaration.
- [ ] `subsort weight q.` — but this is a derived fact, not a declaration.
explanation: Subsort edges are declared with `<:`. The `weight: q @w 1.` form would declare `weight` as a *member* of the classifier `q`, which is not the right relationship. The `subsort` predicate is computed by the loader, not declared directly.
```

## The wave binder names a sort

A wave binder `exists T: tile_t @w. body` tells the decimation driver:
"draw a value for `T` from the members of `tile_t`".

The driver's draw policy:

1. Collect all declared members of `tile_t` — `sea`, `coast`, `land`.
2. Weight each by its constructor prior: 2, 1, 2.
3. Apply any active `!bias` facts (constraint propagation from neighbors).
4. Draw proportionally from the remaining distribution.

After a draw, `T` is replaced by the chosen member throughout `body`, and a
`drawn c tile_t` token records the event.

Notice what the sort slot does: it is the **conditioning interface**.
When you name a sort in the binder, you restrict the population.
If instead you wrote `exists T: even @w. body`, the driver would only draw
from members of `even` — a sub-language of the full classifier.

Here is the WFC beach program running live.
Four cells `c0`–`c3` each hold an open wave over `tile_t`.
The constraint `forbid sea land` propagates via bias rules when a neighbor
collapses.
Pick a wave to collapse, or let auto-mode run.

```{collapse will}
file: calculus/will/game/WFC.will
seed: 3
title: Beach — wave function collapse over tile_t
```

```{quiz, id=ch17-q3}
Q: After `c0` collapses to `sea`, the neighbor's wave for `c1` has `!bias X land 0`. What happens to land's draw weight?
- [x] Land's draw weight drops to zero — it is excluded from the remaining distribution.
- [ ] Land's weight decreases by 1 (subtracted, not zeroed).
- [ ] Nothing — bias facts only affect future waves, not the current one.
- [ ] The wave collapses immediately to coast.
explanation: `!bias X land 0` sets land's bias factor to zero, zeroing its draw weight in the posterior. The wave's other members (coast, sea) keep their weights and are renormalized by the sampler. The wave does not collapse automatically; it stays open until the driver draws it.
```

## Conditioning: restriction, not renormalization

Suppose you learn that a cell's tile is not `sea`.
How does that change the wave?

The naive answer is to remove `sea` from the distribution and **renormalize**:
divide every surviving weight by the new total so the probabilities sum to 1
again.

CALC takes a different path: **restriction**.

> Conditioning on an event removes the worlds that contradict it.
> The surviving worlds keep their masses **unchanged**.
> Renormalization happens only in the sampler's output probabilities — never
> inside the mass calculus.

In symbols: if the prior distribution assigns mass $\rho(sea) = 2$,
$\rho(coast) = 1$, $\rho(land) = 2$, and you condition on "not sea", the
restricted state assigns:

$$\rho'(sea) = 0, \quad \rho'(coast) = 1, \quad \rho'(land) = 2.$$

The surviving masses 1 and 2 are untouched.
The **inside mass** of the conditioned state is $m = 0 + 1 + 2 = 3$, down
from 5.
The sampler draws from $\rho'/m = (0, 1/3, 2/3)$, which is the renormalized
probability — but the masses themselves are the original values, not divided.

This single decision has two consequences:

1. **Cut admissibility is inherited for free.** A conditioned derivation is
   just a base derivation whose draws satisfy an extra membership check.
   No new sequent rule, no new conservation argument.
   The proof theory (THY_0027) holds verbatim.

2. **The inside mass is auditable.** Because surviving masses are unchanged,
   the total mass of a conditioned state can be computed from the program's
   declared priors by solving a linear equation system — exactly, in rational
   arithmetic, at load time.
   The sampler's probabilities are then verifiable by substitution.

```{quiz, id=ch17-q4}
Q: Masses are $\rho(sea)=2, \rho(coast)=1, \rho(land)=2$. You condition on "not land". What is the inside mass of the conditioned state?
- [x] 3 — the sea and coast masses (2 and 1) are untouched; land's mass goes to zero.
- [ ] 3/5 — the surviving probability after renormalization.
- [ ] 2 — only the maximum mass survives.
- [ ] 5 — the total is always preserved under restriction.
explanation: Restriction zeroes excluded worlds and leaves survivors unchanged. Sea (2) and coast (1) survive, giving inside mass 2+1=3. The number 3/5 would be the surviving probability share, not the inside mass. Renormalization is the sampler's job, not the mass calculus's.
```

## Two conditioning surfaces

There are two ways to restrict a wave's population.

**Static conditioning** — at the binder.
Name a sub-sort or datasort in the binder directly:

```
exists T: even @w. body
```

The wave is born constrained to the members of `even` (even-length lists, if
`even` is a datasort defined by membership clauses).
The inside mass $m(even)$ is computed at load.

**Dynamic conditioning** — via `!within` facts.
At any point during a run, a rule may derive `!within E S` to narrow the
effective sort of wave evar `E` to the intersection of `S` with its
registered sort:

```
observe: $tile C T * !forbidden T -o { !within E sea }.
```

This intersects the neighbor wave's state with `sea` — shrinking the
population mid-run without touching the binder.
Multiple `!within` facts for the same evar form an **anonymous product state**:
the driver draws from their intersection.

In both cases the mechanism is the same: the sort slot narrows, the mass
calculus restricts, and the sampler renormalizes.

```{quiz, id=ch17-q5}
Q: A wave has registered sort `tile_t` and two active `!within` facts pointing it at `sea` and `coast`. What does the driver draw from?
- [x] The intersection of `tile_t`, `sea`, and `coast` — i.e., members that belong to all three.
- [ ] The union — members that belong to any one of the three.
- [ ] The registered sort `tile_t` — `!within` facts are advisory only.
- [ ] It is an error to have two `!within` facts on the same evar.
explanation: Multiple `!within` facts form an anonymous product state — the effective conditioning state is their intersection. Only members admitted by every constraint can be drawn. If the intersection is empty, the run hits a contradiction and restarts (in `sample` mode).
```

## Datasorts: sorts over structured terms

Membership can be defined not just by listing atoms but by **clauses**.
These are called **datasorts** — sorts over structured terms.

```
even <: lst.
even/n: even nil.
even/c: even (cons H T) <- odd T.
```

`even` declares a language over `lst` — the even-length lists.
The clause `even/n` says `nil` is in `even`.
The clause `even/c` says `cons H T` is in `even` when `T` is in `odd`.

The loader reads these clauses as a top-down deterministic tree automaton
and solves the inside mass equation system once at load time.
For example, if `nil` has prior 1 and `cons H T` has prior 1 for any head H:

$$m(even) = \rho(nil) + \rho(cons) \cdot m(odd), \quad m(odd) = \rho(cons) \cdot m(even).$$

Substituting: $m(even) = 1 + m(odd)$ and $m(odd) = m(even)$ — this system
is critical (the solution diverges).
With concrete priors the numbers work out; if the mass system is singular or
yields a negative entry, the loader rejects the program with an error.

The key design constraint is that each datasort's clauses must form a
**deterministic automaton**: one depth-1 constructor pattern per head,
premises classify immediate subterms only, at most one recursive argument per
head in a strongly connected component.
These fences make the inside mass system linear and exactly solvable.

```{quiz, id=ch17-q6}
Q: Why must datasort clauses follow the "one depth-1 constructor per head" rule?
- [x] It makes the inside mass system linear — solvable in exact rationals at load time.
- [ ] It prevents recursive types, which are unsound in linear logic.
- [ ] The CALC engine cannot pattern-match at depth > 1.
- [ ] It is a style convention, not a correctness requirement.
explanation: The determinism fence (one constructor per head, one clause per (datasort, head)) is what makes the clause set a deterministic tree automaton. The resulting mass system is linear over ℚ≥0 and solvable at load. Violating the fence either makes the system nonlinear (algebraic masses, outside exact rationals) or indeterminate (load error).
```

## What you learned

- A **classifier** is declared with `name: sort.`; members join it with
  `name: classifier @w weight.`. Weights are constructor priors.
- A **subsort edge** `A <: B.` means every member of sort `A` is also a
  member of sort `B`. The loader materializes the closure as ground facts.
- A wave binder `exists T: s @w. body` draws from the members of sort `s`.
  The sort slot is the conditioning interface.
- **Conditioning is restriction**: excluded worlds go to zero, surviving
  masses are unchanged. Renormalization is the sampler's job, not the mass
  calculus's.
- Static conditioning names a sort at the binder; dynamic conditioning uses
  `!within E S` facts during the run.
- **Datasorts** define membership by clauses (tree automata), with inside
  masses solved at load in exact rationals.

## Going deeper

- [[theory/0020_refinement-sorts|THY_0020: refinement sorts]] — the full design: why content addressing forces extrinsic sorts, the materialized closure, classifiers as predicative schemas, and bounded sort variables.
- [[theory/0030_conditioning-by-restriction|THY_0030: conditioning by restriction]] — the proof that conditioned derivations are base derivations with a membership side-condition, the zero-variance identity, and the certification split between solver and checker.
- [[theory/0026_probability-graded-existential|THY_0026: the probability-graded existential]] — the measure-weighted ∃_ρ connective that wave binders desugar to, and the mass calculus that restriction operates on.
