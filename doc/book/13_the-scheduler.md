---
title: "The Scheduler: Earliest-First, and When It Is Optimal"
part: 3
partTitle: Time and Space
chapter: 13
summary: Why settle fires the earliest-enabled rule first, what that guarantees (confluence and global optimality), and exactly where those guarantees break down.
---

Chapter 12 introduced `settle(S, T)` and showed it fires rules in order of
their activation timestamps.
This chapter asks the harder question: **does firing order matter?**
Sometimes it does not — you get the same final state regardless.
Sometimes it does — but earliest-first is still the best possible policy.
And sometimes there is no best policy at all.
Understanding which situation you are in is the core of timed reasoning.

## What settle actually does

`settle` keeps a priority queue of enabled rule instances, keyed by activation
time.
At each step it picks the instance with the **smallest** activation — the one
whose inputs are all available and collectively become ready earliest.
If two instances tie, a deterministic but arbitrary tiebreaker (a content-hash
pseudorandom function) picks one.

This is exactly **Dijkstra's priority-queue loop**, applied to linear multiset
rewriting.
The analogy will sharpen when we look at the routing example below.

```{quiz, id=ch13-q1}
Q: settle has three enabled instances with activations 2, 5, and 2. Which fires next?
- [x] One of the two instances at activation 2 (tiebreaker picks one).
- [ ] The instance at activation 5 (highest priority).
- [ ] All three at once.
- [ ] The one that was enabled first.
explanation: settle always picks the instance with the minimum activation. The tiebreaker is deterministic but arbitrary among tied instances.
```

## T1: Confluence — when order does not matter

In many programs, no two enabled instances compete for the same token.
They are operating on completely separate pieces of state.
In that case, firing them in different orders still produces the same final
multiset — like rearranging independent steps of a recipe.

**Theorem T1 (confluence).**  If at every reachable state, all instances
that are *tied* for the earliest activation are **independent** — meaning their
token demands do not overlap, and neither produces a zero-delay token the other
needs — then settle reaches the same final state no matter which tiebreaker it
uses.

We call this condition **choice-freedom**: choices among tied candidates are
consequenceless.

```{quiz, id=ch13-q2}
Q: A program has two rules. Rule A consumes `flour` and Rule B consumes `eggs`. Both fire at activation 0. Is this program choice-free?
- [x] Yes — flour and eggs are different tokens, so the rules are independent regardless of order.
- [ ] No — any two rules that fire at the same time conflict.
- [ ] It depends on what they produce.
explanation: Choice-freedom requires that tied instances do not share token demands. Here the demands are disjoint, so T1 applies.
```

## Shortest paths as timed rewriting: the depot demo

Before discussing optimality, let us see the scheduler doing real work.
The file `depot.gill` models a delivery problem.
A good must be transported from city A to a depot via a road network.
Two routes exist:

- A → B → depot, costing 3 + 4 = **7** total.
- A → C → depot, costing 5 + 1 = **6** total.

Each road is a **one-shot linear token** — once a route uses the road, it is
gone.
Traversing a road is a rule with that road's cost as its delay.

```{game gill}
file: calculus/gill/tests/forward/depot.gill
title: Depot — two routes, one delivery
```

Watch what happens when you step the clock forward.
At time 0 the traveller is at A.
At time 3 city B becomes reachable (via A→B, cost 3).
At time 5 city C becomes reachable (via A→C, cost 5).
At time 6 the depot is reached via C (cost 5 + 1).
At time 7 the depot would also be reached via B (cost 3 + 4) — but the
`deliver` rule already consumed the `good` at time 6, so the cost-7 arrival
finds nothing to deliver.

The `delivered@6` fact in the final state proves the cheapest route won.

### Why this is Dijkstra

The connection to Dijkstra's algorithm is not a coincidence.

1. **Priority queue** = settle's min-activation firing order.
2. **Relaxation** = each rule fires once per road token (one-shot edges), adding
   the edge cost to the current path cost.
3. **Read arcs on `city_a`** = the traveller's position is *read*, not consumed;
   both routes race in parallel without competing for the starting city.
4. **First arrival = minimum cost** = the frontier is nondecreasing (later
   activations never lower the minimum), so the first time a `depot_reached`
   token appears its stamp equals the shortest-path distance.

The one-shot discipline on road tokens is what guarantees termination: each
edge fires at most once, so the rewriting always halts.

```{quiz, id=ch13-q3}
Q: In depot.gill, `city_a` is a `read` premise (not consumed). Why does that matter for correctness?
- [x] Both routes need to start from A; consuming city_a would let only one route race.
- [ ] Reads are faster than linear matches.
- [ ] It prevents the depot from being reached twice.
explanation: A read premise matches a token without consuming it. This lets both `hop_ab` and `hop_ac` fire, both starting from the same city_a — exactly like Dijkstra exploring all outgoing edges from a node.
```

## T2: Optimality — when earliest-first is globally best

T1 only guarantees the **same** final state; it says nothing about whether
that state is the **best** reachable one.
For optimality we need a stronger condition.

**Theorem T2 (optimality).**  If the program is **contention-free** — meaning
that in its *monotone relaxation* (the version where all tokens are reusable
values, not consumed once), no two firings overlap in their token demands —
then settle's earliest-first policy realizes the **globally optimal** stamps.
Every fact that is reachable at all arrives as early as possible.

Contention-freedom ⟹ choice-freedom (every run pair is a relaxation pair),
so T1 also holds on contention-free programs.

`depot.gill` satisfies T2 because road tokens are used by at most one rule
each — there is no overlap even in the relaxation.

```{quiz, id=ch13-q4}
Q: T2 requires contention-freedom on the *monotone relaxation*, not just on run states. Why is the relaxation the right place to look?
- [ ] The relaxation is easier to compute.
- [x] Two rules can demand the same token at different times so they never compete in any single run — yet one still starves the other by consuming the token first.
- [ ] Run states can never be analyzed statically.
explanation: If we only required independence on run states, programs where competitors arrive at different times would slip through — but the shared token is still spent before the later competitor arrives. The relaxation captures the demand overlap even when the competitors never coexist in the run.
```

## The gap: choice-free but contended

T1 and T2 have different hypotheses.
A program can be **choice-free** (T1 applies) while being **contended** (T2
does not).
The file `contention.gill` pins this gap with a three-line example, E1:

```
r1: a * tok -o { won_a }.
r2: b * tok -o { won_b }.
% initial state: a, tok, b@5
```

`r1` activates at time 0 (both `a` and `tok` are available immediately).
`r2` activates at time 5 (it must wait for `b@5`).
They are **never tied**, so the tiebreaker is never consulted — the run is
completely deterministic.
T1 holds trivially.

But settle fires `r1` at the frontier (time 0), which **consumes `tok`**.
When `b` arrives at time 5, `tok` is gone.
`r2` can never fire.
`won_b@5` is reachable in the monotone relaxation (where `tok` is a reusable
value) but **not** in the linear run.
T2's hypothesis is violated, and its conclusion genuinely fails.

This is the **Dijkstra gap**: greedy earliest-first is optimal when resources
are reusable (the relaxation), but linear consumption can permanently foreclose
better options.

```{exercise, title=The read twin}
The file `contention.gill` also defines a **read twin** of E1.
Replace the consumed `tok` with a read arc `rtok`:

```
m1: a2 * read rtok -o { won_a2 }.
m2: b2 * read rtok -o { won_b2 }.
% initial: a2, rtok, b2@5
```

In this version `rtok` is never consumed, so both rules can fire.
Step through the depot widget above, or reason by hand: what stamps do
`won_a2` and `won_b2` carry in the final state?
```

```{solution}
`m1` fires at activation max(0,0) = 0, producing `won_a2@0`.
`m2` fires at activation max(5, 0) = 5 (the read stamp of `rtok` joins the activation), producing `won_b2@5`.
Both relaxation stamps are realized. The read discipline makes the program contention-free and T2 applies.
```

## A visual summary of the three conditions

Three conditions nest strictly inside one another:

| Condition | What it guarantees | Example |
|---|---|---|
| **Structural conflict-freedom** | No two rules can ever share a token (syntactic) | one-shot edge graph |
| **Contention-freedom** | Relaxation firings never overlap → **T2 optimality** | depot.gill |
| **Choice-freedom** | Tied run instances are independent → **T1 confluence** | most timed programs |
| *(none)* | Scheduler is still deterministic but may be suboptimal | contention.gill E1 |

Each row implies the ones below it.
E1 in `contention.gill` lives in the bottom row: deterministic (no ties), but
suboptimal.

```{quiz, id=ch13-q5}
Q: A program has rules that share a linear `permit` token, but they activate at different times so they are never tied. Which row of the table does it fall in?
- [ ] Structural conflict-freedom — the rules share no token.
- [ ] Contention-freedom — they never fire at the same time.
- [x] Choice-freedom or below — they share a demand in the relaxation, which is contention; the absence of ties puts it in the bottom row.
- [ ] The table does not apply to programs with shared tokens.
explanation: Shared demand in the relaxation violates contention-freedom. No ties means choice-freedom also fails to apply positively — the run is deterministic, but that is a coincidence of timing, not the structural guarantee T1 requires.
```

## What you learned

- `settle` fires the **earliest-enabled instance** first — a priority queue
  over activation times.
- **T1 (confluence):** if tied instances are always independent
  (choice-freedom), the final state is the same no matter how ties are broken.
- **T2 (optimality):** if the monotone relaxation has no overlapping demands
  (contention-freedom), earliest-first produces the globally optimal stamps.
- **The gap:** a program can be choice-free (T1) but contended (T2 fails).
  The deterministic program E1 in `contention.gill` is the minimal witness.
- `depot.gill` is contention-free: one-shot road tokens, read start node,
  Dijkstra's algorithm realized as timed linear rewriting.

## Going deeper

- [[theory/0019_timed-matching-settle|THY_0019: timed matching and the settle scheduler]] — the formal operational metatheory: min-activation match order, composability law, termination analysis.
- [[theory/0023_till-metatheory|THY_0023: till metatheory]] — the proof-theoretic account of timed sequent rules and focused derivations.
- [[documentation/grade-algebra|grade algebra reference]] — the scheduling dioid axioms (C1–C4) that T2 depends on, and how different grade instances (time, distance, weight) satisfy them.
