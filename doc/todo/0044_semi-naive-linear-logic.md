---
title: "Semi-Naive Evaluation for Linear Logic"
created: 2026-02-19
modified: 2026-02-19
summary: "Open research problem: adapt Datalog's semi-naive evaluation to linear logic where facts can be consumed. No published solution exists."
tags: [research, semi-naive, Datalog, incremental, forward-engine, open-problem]
type: research
cluster: Performance
status: planning
priority: 4
depends_on: []
required_by: [TODO_0036]
---

# Semi-Naive Evaluation for Linear Logic

## The Problem

Standard Datalog semi-naive evaluation relies on **monotonicity**: the fact set only grows, so `delta_i = T_P(S_{i-1}) \ S_{i-1}` gives "just the new facts" at each iteration. In linear logic, facts can be **consumed**:

1. The fact set is not monotone — it shrinks and grows
2. There is no fixed point in the classical sense
3. The same rule may fire differently after resource consumption
4. Termination is by quiescence, not saturation

**No published paper addresses this directly.** This is an open theoretical problem.

## Current State in CALC

CALC sidesteps the problem via the strategy stack (indexing, not incrementality):
- Fingerprint layer: O(1) rule lookup by primary antecedent tag
- Disc-tree layer: pattern-based trie filtering
- Predicate layer: catch-all with trigger predicate scan

This works well at current scale (~44 rules, ~200 facts). At 1000+ rules or 100K+ facts, incremental matching (only re-evaluating rules affected by state changes) would matter.

## Related Work

- **Datalog semi-naive:** Bancilhon (1986), Ullman (1988). Monotonic only.
- **Datafun:** Arntzenius & Krishnaswami (ICFP 2016, POPL 2020). Semi-naive for a higher-order functional language, but uses discrete poset (not linear).
- **Linear Meld:** Cruz et al. (2014). Forward-chaining linear logic, but no semi-naive — re-evaluates all rules at each step.
- **CHR:** No semi-naive. Uses occurrence indexing and active constraint iteration instead.
- **Simmons & Pfenning (2008):** Linear Logical Algorithms. Cost semantics for forward-chaining linear logic, but no incremental matching.

## Possible Approaches

1. **Delta-driven with provenance**: track which rules consumed which facts. On new fact: activate rules with matching antecedent. On consumption: invalidate matches involving that fact. Problem: invalidation cascades.

2. **Mutation+undo as implicit semi-naive**: CALC's DFS with undo already avoids redundant computation within a single exploration path. The question is cross-path reuse.

3. **Tabled forward chaining**: memoize (state_hash → subtree) for recurring states. Already partially done via cycle detection. Full memoization would require state equivalence (modulo permutation?).

4. **Stratification**: if rules can be stratified (no circular consumption dependencies), each stratum runs to saturation before the next. This IS a form of semi-naive for the linear case.

## Priority Justification

Priority 4 (low-medium): theoretically interesting and potentially a publishable contribution, but CALC's current indexing handles the practical case well. This becomes urgent only at 1000+ rules or 100K+ facts — not the current EVM use case.

## Tasks

- [ ] Survey whether any post-2020 work addresses this gap
- [ ] Formalize what "semi-naive" means for linear logic (define the right delta notion)
- [ ] Prototype stratification-based approach for CALC's EVM rules
- [ ] Evaluate memoized subtrees for symexec cross-path reuse

## References

- `doc/research/incremental-matching.md` — incremental matching survey
- `doc/research/chr-linear-logic.md` — CHR avoids the problem differently
- `doc/theory/exhaustive-forward-chaining.md` — CALC's theoretical position
- [TODO_0036](0036_incremental-matching.md) — incremental matching implementation
