---
title: "Commuting Match Reduction in Exhaustive Exploration"
created: 2026-02-26
modified: 2026-02-27
summary: "Eliminate redundant tree branches caused by commuting matches (independent transitions explored in all orderings)"
tags: [symexec, forward-chaining, partial-order-reduction, loli, performance, theory, proof-nets, memoization]
type: design
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: [TODO_0041]
required_by: [TODO_0042]
---

# Commuting Match Reduction

## Problem

`findAllMatches` returns all applicable matches (forward rules + loli continuations) as equal alternatives. `explore()` branches on ALL of them. When two matches are **independent** (consume disjoint linear facts, produce independent facts), both orderings reach the same successor state — the subtrees below are identical.

### Concrete example (EVM)

State: `pc 5 * code 5 0x61 * stack (s ee) V * loli(!neq X Y, {stack SH 0})`

Two matches fire simultaneously:
1. `evm/push2`: consumes `pc`, `code` → produces new `pc`, `stack`
2. `loli:trigger`: consumes `loli` fact, proves `!neq` → produces `stack`

They consume disjoint facts. Both orderings reach the same state S:
```
push2 → loli → S
loli → push2 → S
```

Each such commuting pair doubles the tree. In MultisigNoCall (solc), 6 commuting points → 2^6 = 64 identical STOP leaves instead of 1.

### Scope

- **Multisig baseline**: 2 STOP → should be 1
- **Multisig + CALL**: 4 STOP → should be 2 (CALL fork is genuine)
- **Solc multisig**: 64 STOP → should be 1
- **General**: any program where independent transitions are simultaneously enabled

### Why this matters

- Performance: N commuting pairs → 2^N paths with identical outcomes
- Tree interpretation: leaf counts should reflect semantically distinct outcomes, not exploration artifacts
- hevm comparison: CALC reports 64 STOP vs hevm's 18 Success — misleading

## Why Cycle Detection Doesn't Help

The current `pathVisited` set detects **back-edges** (cycles on the current DFS path), not **joins** (diamonds where different paths converge):

```
      S₀           pathVisited at each point:
     / \
    t1   t2         S₀ → {S₀}
   /       \
  S₁       S₂      S₁ → {S₀, S₁}    S₂ → {S₀, S₂}
   \       /
    t2   t1
     \   /
      S₃            visited via S₁ → explored
      S₃            visited via S₂ → explored AGAIN (not a cycle!)
```

`pathVisited` is a DFS-path set: added before recursion, deleted after all children return. State S₃ is NOT in `pathVisited` when reached via S₂ (it was deleted after the S₁ subtree returned). So the join is invisible — the entire subtree below S₃ is re-explored.

A **global visited set** (never deleted) would detect the join. This is Option E below.

## Root Cause Analysis

The commuting matches arise specifically from **persistent-trigger lolis** (pattern `!guard -o {body}`) co-existing in state with forward rules. These lolis:
1. Are created by oplus branching (EQ, ISZERO, JUMPI rules)
2. Have persistent triggers — provable immediately from `state.persistent`
3. Don't consume any linear facts except the loli itself
4. Are therefore independent of any forward rule that doesn't consume the loli fact

Linear-trigger lolis (e.g. `unblock -o {pc PC'}` from calldatacopy) are **asynchronous** — they wait for a future fact and don't cause commuting matches because their trigger isn't available when they're created.

But commuting matches are not limited to lolis. In a general CALC program (not EVM), two forward rules consuming disjoint linear facts can fire simultaneously and commute. EVM avoids this because `pc` is consumed by every opcode rule (mutual exclusion), but other programs have no such constraint.

## Theoretical Framework

### The problem in proof-theoretic terms

Two sequent calculus derivations that differ only in the order of independent cut applications correspond to the **same proof net** (Girard 1987). The execution tree explores sequent derivations — it distinguishes orderings that proof nets identify. The tree has exponentially more leaves than the set of distinct proof nets.

The goal: explore **proof nets** (equivalence classes of derivations under commuting conversions), not derivations.

### Independence in ILL

Two transitions t₁, t₂ enabled at state S are **independent** iff:
1. `consumed(t₁) ∩ consumed(t₂) = ∅` — disjoint resource consumption
2. t₁ doesn't produce facts that t₂ consumes and vice versa (no causal dependency)
3. Neither's persistent proving depends on the other's produced persistent facts

Independent transitions commute: `t₁; t₂` and `t₂; t₁` reach the same state. This is the **diamond property** and follows directly from ILL's tensor commutativity (`A ⊗ B ≡ B ⊗ A`).

### What reduction MUST preserve

Any correct reduction must preserve the **set of reachable quiescent states**: for every quiescent state reachable under full interleaving, the reduced exploration must also reach it. This is the completeness criterion from TODO_0042.

## Approaches

### TODO_0054.Option_A — Eager Loli Resolution

Resolve all fireable lolis deterministically before looking for forward matches.

**Theory compliance: PARTIAL.** Correct when loli and forward rule are independent (consume disjoint linear facts). Always true for persistent-trigger lolis in EVM. But a loli with linear triggers COULD compete with a forward rule for the same linear fact — eagerly choosing the loli would drop the forward rule alternative. **Not safe for general programs without an independence check.**

Would require extending to a focusing-like discipline: "resolve invertible (forced) transitions first, branch only at genuine choice points." But ILL focusing theory (Andreoli 1992) is developed for backward chaining — a forward-chaining focusing discipline would be a novel theoretical contribution.

| | |
|---|---|
| Pro | Simple, handles EVM |
| Con | Not general — unsafe if loli competes with forward rule for linear facts |
| Con | No existing theory for "forward focusing" to justify the ordering |

### TODO_0054.Option_B — Partial Order Reduction (POR)

At each state, compute an **ample set** — a subset of enabled transitions that preserves reachability completeness.

**Theory compliance: YES.** Peled's theorem (1993) proves that ample sets satisfying conditions C0-C3 preserve all reachable states. The independence relation is computed explicitly — no assumption about which rules commute.

Independence check for CALC: compare `consumed` maps of two matches for overlap. O(|consumed₁| × |consumed₂|) per pair. For EVM rules (3-5 consumed facts), this is ~O(15) per pair.

| | |
|---|---|
| Pro | General, correct by theorem |
| Pro | Handles ALL commuting matches (loli-forward, forward-forward) |
| Con | Overhead per state (compute independence for all match pairs) |
| Con | Complex (C0-C3 conditions include cycle-freedom requirement for ample sets) |
| Con | Reduces branching but still explores each match at least once somewhere |

### TODO_0054.Option_C — Synchronous Loli Fusion

Resolve persistent-trigger lolis atomically with the oplus expansion. Guard resolution happens during the oplus step, not as a separate transition.

**Theory compliance: YES (by construction).** Changes the operational semantics so the oplus choice + guard resolution is one atomic step. The loli never enters the state. Corresponds to the CLF monadic step boundary: `{A}` is atomic. Producing a loli inside `{A}` and then firing it is semantically equivalent to proving the guard and producing the body directly.

BUT: CLF forbids lolis inside the monad for operational simplicity. Our extension allows them (TODO_0041). Fusion reverses this for persistent-trigger lolis — effectively agreeing with CLF that these particular lolis shouldn't exist in state.

Linear-trigger lolis (`unblock -o {body}`) genuinely need to be deferred (their trigger doesn't exist yet). They stay as-is.

| | |
|---|---|
| Pro | Eliminates the source — persistent-trigger lolis never enter state |
| Pro | Aligns with CLF monad boundary |
| Con | Only handles persistent-trigger lolis |
| Con | Significant refactor of oplus expansion in `go()` |

### TODO_0054.Option_D — Sleep Sets

Track "sleeping" transitions per DFS frame. When exploring child(t₁), propagate sleep set S' = {t₂ : t₂ independent of t₁}. Skip sleeping transitions at child states.

**Theory compliance: YES.** Godefroid (1996) proves sleep sets preserve reachability completeness. Equivalent to POR but with propagated state instead of per-node computation.

| | |
|---|---|
| Pro | Similar reduction to POR, sometimes better |
| Con | Bookkeeping per DFS frame (sleep set must be undone on backtrack) |
| Con | Still needs independence relation |

### TODO_0054.Option_E — State Memoization (Global Visited Set)

Add a global `Set<stateHash>` (distinct from `pathVisited`). Before exploring a state, check if it's already been fully explored. If so, return `{ type: 'memo' }` — a reference to the previously explored subtree.

**Theory compliance: YES.** Same state = same future. If state S was fully explored via one path, re-exploration via another path produces an identical subtree. Pruning is sound for reachability (same set of quiescent states reached).

This is standard graph search: DFS with a **closed set** (visited set that's never cleared). Turns the execution tree into a DAG.

```
      S₀
     / \
    t1   t2
   /       \
  S₁       S₂
   \       /
    t2   t1
     \   /
      S₃ (first visit: explore full subtree)
      S₃ (second visit: return { type: 'memo' })
```

Implementation: `const globalVisited = new Set()` alongside `pathVisited`. After fully exploring a state (all children returned), add stateHash to `globalVisited`. Before exploring, check `globalVisited.has(ctx.stateHash)`.

```javascript
function go(depth, ctx) {
  if (pathVisited.has(ctx.stateHash)) return { type: 'cycle', ... };
  if (globalVisited.has(ctx.stateHash)) return { type: 'memo', ... };
  if (depth >= maxDepth) return { type: 'bound', ... };

  // ... explore children ...

  globalVisited.add(ctx.stateHash);  // mark as fully explored
  pathVisited.delete(ctx.stateHash);
  return { type: 'branch', ... };
}
```

Catches ALL state duplicates — commuting matches, non-commuting convergence, any source. Does NOT reduce the branching factor (still branches on all matches), but avoids re-exploring identical subtrees.

| | |
|---|---|
| Pro | **Most general** — catches ALL state duplicates, not just commuting |
| Pro | Simplest to implement (~5 lines) |
| Pro | No independence relation needed |
| Pro | Sound: same state = same future (trivially correct) |
| Con | Does NOT reduce branching factor — tree still has 2^N branches, just 2^N − 1 are `memo` leaves |
| Con | Hash collisions → false memoization (missed states). 32-bit XOR hash has non-trivial collision risk |
| Con | Tree structure changes (DAG semantics, `memo` nodes reference other subtrees) |
| Con | Path information lost at memo nodes (can't trace full path to a leaf through a memo) |

### TODO_0054.Option_F — Maximal Step Semantics

At each state, partition enabled transitions into **independent groups**. Fire all transitions in a group simultaneously as one atomic step. Only branch between groups that conflict (consume overlapping resources).

**Theory compliance: YES.** This is the Petri net "step semantics" — well-understood in concurrency theory. Equivalent to exploring the maximal concurrent firings rather than all interleavings.

| | |
|---|---|
| Pro | Elegant — concurrent transitions fire together, no ordering artifacts |
| Pro | Minimal branching (only between conflicting transitions) |
| Con | Requires computing independence relation (like POR) |
| Con | "Simultaneous firing" needs careful definition for linear resources |
| Con | Complex mutation model (apply multiple matches atomically) |
| Con | No existing implementation framework to build on |

## Comparison

| | Scope | Complexity | Tree reduction | Theory-grounded | Safe for all programs |
|---|---|---|---|---|---|
| A. Eager loli | Loli vs forward | Low | 2^N → 1 | **No** (ad hoc ordering) | **No** (unsafe if loli competes for linear facts) |
| B. POR (ample sets) | All commuting | High | Optimal branching | **Yes** (Peled 1993) | **Yes** |
| C. Synchronous fusion | Persistent-trigger lolis | Medium | Same as A + shallower | **Yes** (CLF monadic step) | **Partial** (linear-trigger lolis unchanged) |
| D. Sleep sets | All commuting | Medium-high | Near-optimal | **Yes** (Godefroid 1996) | **Yes** |
| E. State memoization | ALL duplicates | **Low** | No branch reduction, but prunes subtrees | **Yes** (same state = same future) | **Yes** |
| F. Maximal step | All commuting | High | Minimal branching | **Yes** (Petri net steps) | **Yes** |

## Analysis: What Solves It Fundamentally

The problem has two facets:

1. **Branching**: `go()` creates branches for commuting matches (inflated branching factor)
2. **Re-exploration**: identical subtrees explored multiple times (wasted work)

Options A-D and F address facet 1 (reduce branching). Option E addresses facet 2 (avoid re-exploration). Ideally, we want both.

### Recommended combination: E + C

**State memoization (E)** is the foundation — it's simple, general, catches all duplicates regardless of source, and is trivially correct. It should be implemented regardless of which other option is chosen.

**Synchronous fusion (C)** addresses the specific source for EVM programs — persistent-trigger lolis. It's CLF-theoretically motivated (the monad boundary argument). Together with memoization, it eliminates both the branching and the re-exploration for the common case.

For non-EVM programs where forward-vs-forward commuting matters, POR (B) can be layered on top later.

### Hash collision mitigation for Option E

The 32-bit XOR hash in `computeNumericHash` has non-trivial collision probability for large state spaces. Mitigation options:
- **64-bit hash**: use BigInt or two 32-bit halves. Collision probability drops from ~2^-32 to ~2^-64
- **Full comparison on hit**: when `globalVisited.has(hash)`, do a full state equality check before pruning. Requires storing snapshot states, not just hashes
- **Probabilistic acceptance**: accept the small collision risk for performance (model checking tradition)

## Also Blocked

This TODO blocks the **symbolic sender/storage benchmark**: with duplication, timing comparisons with hevm are meaningless.

## References

- [TODO_0041](0041_unified-rule-matching.md) — unified matching (done, prerequisite)
- [TODO_0042](0042_exhaustive-exploration-completeness.md) — completeness proof (requires understanding of match reduction)
- `doc/theory/0001_exhaustive-forward-chaining.md` — loli-in-monad extension, execution tree judgment
- Girard, J-Y. (1987) "Linear Logic" — proof nets as canonical representations quotienting commuting conversions
- Andreoli, J-M. (1992) "Logic Programming with Focusing Proofs in Linear Logic" — focusing for backward chaining
- Peled, D. (1993) "All from One, One for All: On Model Checking Using Representatives"
- Godefroid, P. (1996) "Partial-Order Methods for the Verification of Concurrent Systems"
- Valmari, A. (1989) "Stubborn Sets for Reduced State Space Generation"
