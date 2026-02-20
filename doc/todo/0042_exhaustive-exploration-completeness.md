---
title: "Completeness of Exhaustive Exploration"
created: 2026-02-19
modified: 2026-02-19
summary: "Prove that symexec's exhaustive exploration finds all reachable quiescent states — soundness, completeness, and termination guarantees"
tags: [theory, symexec, completeness, soundness, model-checking]
type: research
status: planning
priority: 7
depends_on: [TODO_0041]
required_by: [TODO_0008]
---

# Completeness of Exhaustive Exploration

## The Question

Does symexec's execution tree contain every reachable quiescent state? Formally:

- **Soundness:** every leaf `Delta_q` in the tree is reachable from the initial state by a valid forward-chaining trace
- **Completeness:** every quiescent state reachable from the initial state appears as a leaf
- **Termination:** the exploration terminates (the tree is finite)

## What We Have

- Cycle detection via `pathVisited` (hash set) — prevents infinite loops on back-edges
- Depth bounding via `maxDepth` — prevents infinite trees
- State hashing via `ExploreContext` XOR hash — fast cycle detection

## What Needs Formalization

### Soundness

Each tree node records the rule and substitution that produced it. Replaying the path from root to any leaf produces a valid forward-chaining trace. This should follow directly from the correctness of `tryMatch` + `mutateState`.

### Completeness

Harder. Requires showing that `findAllMatches` at each state returns ALL applicable rules (no missed matches). Depends on:
- Strategy stack correctness: fingerprint + disc-tree + predicate layers don't miss rules
- Loli unification: after TODO_0041, loli continuations compete equally (the priority bug is the current completeness hole)
- State hash correctness: `hashState` doesn't create false cycle detections (hash collision → missed states)

### Termination

For finite-state systems (bounded gas in EVM): the state space is finite, and cycle detection prevents revisiting. For unbounded systems: depth bounding ensures finite tree but at the cost of completeness (bounded completeness only).

### Connection to Model Checking

The execution tree is a Kripke structure. Completeness of exploration = completeness of the reachability analysis. Properties expressible as CTL queries over leaves (safety, reachability, invariants) are decidable given a complete tree.

## Tasks

- [ ] Formalize soundness: path from root to leaf = valid trace
- [ ] Formalize completeness: findAllMatches returns all applicable rules (depends on TODO_0041)
- [ ] Analyze hash collision probability (32-bit XOR hash on states)
- [ ] Characterize termination conditions (gas bounds, resource consumption)
- [ ] Connect to model checking theory (CTL over execution trees)

## References

- `doc/theory/exhaustive-forward-chaining.md` — proposed execution tree judgment
- `doc/research/execution-trees-metaproofs.md` — execution trees and metaproofs
- [TODO_0008](0008_metaproofs.md) — program property verification (requires completeness)
- [TODO_0041](0041_unified-rule-matching.md) — unified matching (prerequisite: fixes priority bug)
