---
title: Symexec DFS Mutation+Undo Pattern
created: 2026-02-13
summary: Why explore() mutates state, index, and pathVisited in-place
tags: [performance, symexec, architecture]
---

# Symexec DFS Mutation+Undo Pattern

The `explore()` function in `lib/prover/strategy/symexec.js` uses a mutation+undo
pattern for three data structures during DFS traversal. This document explains
why each exists and the invariant they maintain.

## Core invariant

**When `go()` returns, all three mutable structures (state, stateIndex, pathVisited)
are in exactly the state they were when `go()` was called.**

This is enforced by pairing every mutation with an undo operation after the child
subtree returns.

## 1. State mutation+undo

```
mutateState(state, consumed, theta, linear, persistent) → undo log
  go(child)
undoMutate(state, undo)
```

**Why:** Creating `{ ...state.linear }` (178 keys) for each of 62 children would
cost 62 × 46µs = 2.85ms — nearly the entire explore budget. Mutation+undo costs
~4µs per step (for-in over 5–9 changed keys).

**Undo log shape:** `{ linearOrig: { hash: oldCount }, persistentOrig: { hash: wasPresent } }`

## 2. Index mutation+undo

```
makeChildCtx(ctx, state, undo) → { ctx: childCtx, indexUndo }
  go(child)
undoIndexChanges(ctx.stateIndex, indexUndo)
```

**Why:** The stateIndex groups facts by predicate for O(1) lookup during tryMatch.
At branch points (nodes with multiple children), the previous approach cloned
the entire index via `cloneIndex()`. This was dominated by copying the 173-entry
`codeByPC` secondary index object (`{ ...codeByPC }` = 46µs per clone, 6 clones
per explore = 278µs).

With mutation+undo, the index is modified in-place (indexRemove/indexAdd for the
~4 predicates that actually change per step), then reversed after the child returns.

**Undo log shape:** Flat array `[hash1, wasRemoved1, hash2, wasRemoved2, ...]`
where `wasRemoved=1` means "undo by adding back", `wasRemoved=0` means "undo by removing".

**Why flat array:** Avoids object allocation. Pairs are read in reverse order
during undo.

## 3. Mutable pathVisited Set

```
pathVisited.add(ctx.stateHash)
  go(child1)
  go(child2)
pathVisited.delete(ctx.stateHash)
```

**Why:** DFS processes children sequentially, not in parallel. The previous approach
created `new Set(parent)` at each of 56 branch nodes (avg ~25 entries per copy =
85µs total). Add/delete on a single Set is O(1) with zero allocation.

**Correctness:** Each child sees the same pathVisited contents because:
- We add before any children
- Children undo their own additions before returning (recursive invariant)
- We delete after all children

## Cost summary (EVM multisig benchmark, 63 nodes)

| Approach | Cost |
|---|---|
| State copy per child | 62 × 46µs = 2,852µs |
| State mutation+undo | 62 × 4µs = 248µs |
| Index clone at branches | 6 × 46µs = 278µs |
| Index mutation+undo | 62 × ~1µs = 62µs |
| Set copy per branch | 56 × 1.5µs = 85µs |
| Mutable Set add/delete | 56 × ~0.02µs ≈ 1µs |

## When to be careful

- **Adding new tree consumers**: Terminal nodes (leaf/bound/cycle) snapshot the state
  via `snapshotState()`. Branch nodes have `state: null`. If a consumer needs branch
  node states, the mutation+undo pattern means those states don't exist after traversal.

- **Parallel exploration**: This pattern is inherently sequential (DFS). If explore()
  were ever parallelized (e.g., for multi-core), shared mutation would break.
  Each worker would need its own copies.

- **Index correctness**: `undoIndexChanges` must be called in the exact reverse order
  of `makeChildCtx`. Skipping it (e.g., early return) would corrupt the index for
  subsequent siblings.
