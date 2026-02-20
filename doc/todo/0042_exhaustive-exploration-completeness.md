---
title: "Completeness of Exhaustive Exploration"
created: 2026-02-19
modified: 2026-02-19
summary: "Prove that symexec's exhaustive exploration finds all reachable quiescent states — soundness, completeness, and termination guarantees"
tags: [theory, symexec, completeness, soundness, model-checking]
type: research
status: planning
priority: 7
depends_on: []
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
- Loli unification: after TODO_0041 (done), loli continuations compete equally (priority bug fixed)
- State hash correctness: `hashState` doesn't create false cycle detections (hash collision → missed states)

### Termination

For finite-state systems (bounded gas in EVM): the state space is finite, and cycle detection prevents revisiting. For unbounded systems: depth bounding ensures finite tree but at the cost of completeness (bounded completeness only).

### Connection to Model Checking

The execution tree is a Kripke structure. Completeness of exploration = completeness of the reachability analysis. Properties expressible as CTL queries over leaves (safety, reachability, invariants) are decidable given a complete tree.

### Connection to QCHR (Stéphan & Barichard, TOCL 2025)

CALC's exhaustive exploration is conceptually a QCHR game-tree solver where all branching is universal (∀ — explore all rule choices). The ω_l^{∃∀} system provides proof-theoretical soundness/completeness for this pattern:
- ∀-branching at rule nondeterminism = "for all applicable rules, explore the subtree"
- ∃-branching at ⊕ disjunction = "system decides which branch" (but symexec explores all)
- QCHR's tabling/memoization = `pathVisited` cycle detection + state hashing
- QCHR dynamic binder = loli continuations (rules produced at runtime)
- **Theorem 5.1 (QCHR):** ω_r^{∃∀} is sound and complete w.r.t. ω_l^{∃∀} — could ground CALC's completeness proof

See `doc/research/chr-linear-logic.md` §2.5, `doc/todo/0043_chr-linear-logic-mapping.md` §8.

## Tasks

- [ ] Formalize soundness: path from root to leaf = valid trace
- [ ] Formalize completeness: findAllMatches returns all applicable rules (TODO_0041 done — loli priority fixed)
- [ ] Analyze hash collision probability (32-bit XOR hash on states)
- [ ] Characterize termination conditions (gas bounds, resource consumption)
- [ ] Connect to model checking theory (CTL over execution trees)

## References

- `doc/theory/exhaustive-forward-chaining.md` — proposed execution tree judgment, Q5+Q6
- `doc/research/execution-trees-metaproofs.md` — execution trees and metaproofs
- `doc/research/chr-linear-logic.md` — §2.5 (QCHR), §10.3 (CALC↔QCHR mapping)
- [TODO_0008](0008_metaproofs.md) — program property verification (requires completeness)
- [TODO_0041](0041_unified-rule-matching.md) — unified matching (done: fixed priority bug)
- [TODO_0043](0043_chr-linear-logic-mapping.md) — CHR soundness mapping, §8 (QCHR connection)
- [TODO_0045](0045_execution-tree-judgment.md) — execution tree judgment formalization
- Barichard, Stéphan (2025) "Quantified Constraint Handling Rules" ACM TOCL 26(3):1-46
