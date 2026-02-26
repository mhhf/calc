---
title: "Commuting Match Reduction in Exhaustive Exploration"
created: 2026-02-26
modified: 2026-02-26
summary: "Eliminate redundant tree branches caused by commuting matches (independent transitions explored in all orderings)"
tags: [symexec, forward-chaining, partial-order-reduction, loli, performance, theory]
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
- **General**: any program with oplus branching that creates loli continuations while other forward rules are independently fireable

### Why this matters

- Performance: exploring N commuting pairs creates 2^N paths with identical outcomes
- Tree interpretation: leaf counts should reflect semantically distinct outcomes, not artifacts of exploration order
- hevm comparison: CALC reports 64 STOP vs hevm's 18 Success — misleading (both have 1 distinct STOP per member)

## Root Cause Analysis

The commuting matches arise specifically from **persistent-trigger lolis** (pattern `!guard -o {body}`) co-existing in state with forward rules. These lolis:
1. Are created by oplus branching (EQ, ISZERO, JUMPI rules)
2. Have persistent triggers — provable immediately from `state.persistent`
3. Don't consume any linear facts except the loli itself
4. Are therefore independent of any forward rule that doesn't consume the loli fact

Linear-trigger lolis (e.g. `unblock -o {pc PC'}` from calldatacopy) are **asynchronous** — they wait for a future fact and don't cause commuting matches because their trigger isn't available when they're created.

## Approaches

### TODO_0054.Option_A — Eager Loli Resolution

Resolve all fireable lolis **deterministically** before looking for forward matches. Lolis are not choices — they're deferred computations. In `go()`:

```
1. Loop: find fireable lolis from stateIndex
   - Single-alt loli: apply deterministically (mutate + track undo)
   - Multi-alt loli: branch (genuine nondeterminism from oplus in body)
   - Repeat until no more lolis fire
2. Find forward rule matches (the actual nondeterministic choices)
3. Branch on forward matches
4. Undo loli resolutions when backtracking
```

Changes needed:
- Remove loli scanning from `findAllMatches` (strategy.js)
- Import `matchLoli` in symexec.js
- Add loli resolution loop in `go()` before forward matching
- Track loli undo chain for backtracking (integrates with existing mutation/undo model)

| | |
|---|---|
| Pro | Simple, handles the exact EVM problem |
| Pro | Semantically motivated — lolis are continuations, not alternatives |
| Pro | Integrates with existing mutation/undo model |
| Con | Not general — only handles loli vs forward, not forward vs forward commuting |
| Con | Changes tree depth semantics (loli steps are "invisible") |

### TODO_0054.Option_B — Partial Order Reduction (POR)

Classic model-checking technique (Peled 1993, Godefroid 1996, Valmari 1989). At each state, compute an **ample set** — a subset of enabled transitions preserving all reachable states.

Two transitions t1, t2 are **independent** iff:
1. They consume disjoint linear facts (`consumed(t1) ∩ consumed(t2) = ∅`)
2. Neither's produced facts affect the other's enabling condition

At each state, if there exists a transition t such that all other enabled transitions are independent of t, the ample set is {t} — explore only t, skip the rest (they'll be explored at successor states).

| | |
|---|---|
| Pro | General — handles ALL commuting matches, not just loli vs forward |
| Pro | Well-studied theory with correctness proofs |
| Pro | Preserves reachability completeness (all quiescent states still found) |
| Con | Requires computing independence relation per state (overhead) |
| Con | Complex implementation (ample set conditions C0-C3 from Peled) |
| Con | May not be worth it if only loli-vs-forward commuting occurs in practice |

### TODO_0054.Option_C — Synchronous Loli Fusion

Instead of storing persistent-trigger lolis in state, resolve them **immediately** as part of the oplus expansion. The oplus choice + guard resolution become one atomic step.

Current (two steps):
```
Step 1: oplus fires → alt 0 produces loli(!neq, {stack 0}), alt 1 produces loli(!eq, {stack 1})
Step 2: loli fires → produces stack value (or fails → dead leaf)
```

Fused (one step):
```
Step 1: oplus fires → alt 0: prove !neq → produce stack 0 (or dead), alt 1: prove !eq → produce stack 1 (or dead)
```

Implementation: in `go()`'s multi-alt handling (or in `expandConsequentChoices`), when an alternative produces a loli with only persistent triggers, immediately prove the guard. On success: substitute body into consequent. On failure: dead leaf.

**Only applies to persistent-trigger lolis.** Linear-trigger lolis (`unblock -o {body}`) stay as deferred facts (their trigger requires future linear facts).

| | |
|---|---|
| Pro | Most principled — aligns with CLF semantics (monad boundary = atomic step) |
| Pro | Eliminates the source entirely — no lolis in state for the common case |
| Pro | Shallower tree (fewer steps per oplus resolution) |
| Con | Significant change to rule application semantics |
| Con | Only handles persistent-trigger lolis (linear-trigger lolis unchanged) |
| Con | Changes tree structure (depth, node counts) — all tests need updating |

### TODO_0054.Option_D — Sleep Sets

Variant of POR. Track transitions whose reordering with previously explored ones is redundant. At each state, maintain a "sleep set" of transitions to skip.

When exploring child(t1), pass along sleep set S' = {t2 : t2 ∈ enabled, t2 independent of t1}. At the child state, skip transitions in S'.

| | |
|---|---|
| Pro | More precise than ample sets in some cases |
| Pro | No need to recompute independence at each state (propagated) |
| Con | Additional bookkeeping (sleep set per DFS frame) |
| Con | Still requires independence relation |
| Con | Complex interaction with the mutation/undo model |

## Comparison

| | Scope | Complexity | Tree reduction | Theory |
|---|---|---|---|---|
| A. Eager loli | Loli vs forward only | Low | 2^N → 1 for N loli-forward pairs | Ad hoc |
| B. POR | All commuting | High | Optimal | Well-studied |
| C. Synchronous fusion | Persistent-trigger lolis | Medium | Same as A + shallower tree | CLF-motivated |
| D. Sleep sets | All commuting | Medium-high | Near-optimal | Well-studied |

## Recommendation

**Option A** for immediate fix (handles the concrete EVM problem, minimal changes). **Option C** as the medium-term target (more principled, eliminates the source). **Option B** as long-term research (needed if forward-vs-forward commuting becomes a problem in non-EVM programs).

Note: for EVM specifically, forward-vs-forward commuting doesn't occur because `pc` is a linear fact consumed by every opcode rule — at most one opcode fires per state. The only commuting matches are loli vs forward.

## Also Blocked

This TODO also blocks the **symbolic sender/storage benchmark**: with 64× duplication, timing comparisons with hevm (31 leaves) are meaningless. Fix commuting matches first, then benchmark.

## References

- [TODO_0041](0041_unified-rule-matching.md) — unified matching (done, prerequisite)
- [TODO_0042](0042_exhaustive-exploration-completeness.md) — completeness proof (requires understanding of match reduction)
- `doc/theory/0001_exhaustive-forward-chaining.md` — CALC's theoretical position, loli-in-monad extension
- Peled, D. (1993) "All from One, One for All: On Model Checking Using Representatives" (POR foundation)
- Godefroid, P. (1996) "Partial-Order Methods for the Verification of Concurrent Systems" (ample sets)
- Valmari, A. (1989) "Stubborn Sets for Reduced State Space Generation" (stubborn sets ≈ ample sets)
