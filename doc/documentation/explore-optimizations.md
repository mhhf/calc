---
title: Explore DFS Mutation+Undo Pattern
modified: 2026-03-03
summary: Why explore() mutates state, index, and pathVisited in-place
tags: [performance, symexec, architecture]
---

# Explore DFS Mutation+Undo Pattern

The `explore()` function in `lib/engine/explore.js` uses a mutation+undo
pattern for three data structures during DFS traversal. This document explains
why each exists and the invariant they maintain.

## Core invariant

**When `go()` returns, all three mutable structures (state, stateIndex, pathVisited)
are in exactly the state they were when `go()` was called.**

This is enforced by pairing every mutation with an undo operation after the child
subtree returns.

## 1. State mutation+undo (FactSet + Arena)

```
linCp = linArena.checkpoint()
perCp = perArena.checkpoint()
mutateState(state, consumed, theta, linearPats, persistentPats, slots, rule, linArena, perArena)
  go(depth + 1, pred)
state.persistent.undo(perArena, perCp)
state.linear.undo(linArena, linCp)
```

**Why:** State is a FactSet (per-tag sorted Int32Array groups with incremental Zobrist hashing). Arena is a flat Int32Array undo log. Checkpoint/restore is O(delta) — only the changed entries are replayed. No object allocation, no cloning.

**Current implementation:** `state-ops.js:mutateState()` handles consume + produce. Arena records each insert/remove for automatic replay. FactSet maintains `stateHash` (Zobrist) incrementally.

## 2. FactSet replaces stateIndex

The original `stateIndex` (plain object grouping facts by predicate) was replaced by FactSet, which IS the index. Per-tag sorted arrays provide O(log n) lookup by tag. The `state._byKey` secondary index is built only when fingerprint config requires it (controlled by the `fingerprint` profile flag in `opt/fingerprint.js`).

## 3. Mutable pathVisited Set

```
pathVisited.add(sh)
  go(child1)
  go(child2)
pathVisited.delete(sh)
```

**Why:** DFS processes children sequentially, not in parallel. Add/delete on a single Set is O(1) with zero allocation. Children undo their own additions before returning (recursive invariant).

## 4. Constraint solver checkpoint/restore

```
scp = solver.checkpoint()
  mutateState(...)
  feedPersistent(solver, perArena, perCp)    // opt/constraint.js
  go(depth + 1)
solver.restore(scp)
```

The EqNeqSolver (union-find with forbid list) tracks eq/neq constraints from persistent facts. Checkpoint/restore wraps each subtree for backtracking. Multi-alt branches use `filterAltsBySAT()` to prune UNSAT alternatives before exploring.

## 5. De Bruijn indexed theta (Stage 6)

Each metavar in a rule gets a compile-time slot index (`metavarSlots`). Theta becomes
`theta[slot] = value` (O(1) lookup) instead of linear scan. The undo stack (`_undoStack`
in unify.js) tracks which slots were written so they can be cleared on match failure.

**Critical invariant:** `undoSave()` at tryMatch entry, `undoRestore(theta, saved)` on
every failure exit, `undoDiscard(saved)` on success exit. Without discard, `_undoLen`
grows monotonically across calls, eventually overflowing the fixed-size undo buffer.

## 6. Delta bypass + compiled substitution (Stage 7)

**Delta bypass** (`opt/delta-bypass.js`): For flat delta patterns (children are metavars or ground), extract children directly via `Store.child(fact, pos)` instead of full `matchIndexed` decomposition.

**Compiled substitution** (`opt/compiled-sub.js`): Precomputed recipes map consequent patterns to direct `Store.put(tag, [theta[slot0], theta[slot1]])` calls, bypassing recursive `applyIndexed` traversal.

**mutateState integration** (`state-ops.js`): When `rule` is passed to `mutateState`, it handles preserved-skip + compiled substitution together. Recipe indices align with full consequent pattern list. Multi-alt paths use external `filterPreserved` (`opt/preserved.js`).

## 7. Optimization modules

All optimizations called in the `go()` hot loop live in `lib/engine/opt/` as independently importable modules. Each is controlled by a profile flag in `optimizer.js`. See `doc/documentation/optimization-architecture.md` for the full module map, flag table, and V8 design constraints.

## When to be careful

- **Adding new tree consumers**: Terminal nodes (leaf/bound/cycle/memo) snapshot the state via `snapshotBulk()`. Branch nodes have `state: null`. The mutation+undo pattern means branch states don't exist after traversal.

- **Parallel exploration**: This pattern is inherently sequential (DFS). If explore() were ever parallelized, each worker would need its own State + Arena copies.

- **Arena ordering**: `state.persistent.undo()` must be called before `state.linear.undo()` to match the mutation order in `mutateState`. The solver must also be restored.

- **Importing in opt/ modules**: Never pass core functions as parameters to opt/ modules — import them directly. V8 polymorphic call sites from function-as-parameter cause measurable regression (70% observed with `mutateState` passed to `drainPersistentLolis`).
