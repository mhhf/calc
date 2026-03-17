---
title: "Constructor Indexing"
created: 2026-02-18
modified: 2026-02-20
summary: "O(1) identity for ground formulas via tag-based index"
tags: [performance, indexing, optimization]
type: implementation
cluster: Performance
status: planning
priority: 5
depends_on: []
required_by: []
---

# Constructor Indexing

O(1) identity for ground formulas via tag-based index. Highest-impact single optimization for backward prover.

## Problem

`tryIdentity` in `lib/prover/generic.js` does a linear scan: O(m*n) per identity check where m = context size, n = formula size. 98.6% of unify attempts fail.

## Design

Three-level lookup:

| Level | Key | Lookup | When |
|-------|-----|--------|------|
| 1. Hash equality | `goal` hash | O(1) | Ground formulas (most common) |
| 2. Tag filter | `Store.tag(goal)` | O(c) candidates | Formulas with metavariables |
| 3. Variables | -- | O(v) | Variable goals (rare) |

Ground case: content-addressing gives O(1) — if `goal === linear[i]`, identity succeeds without unification.

## Complexity

| Scenario | Current | With Index | Speedup |
|----------|---------|------------|---------|
| Ground formula | O(m*n) | **O(1)** | m*n |
| Goal with metavars | O(m*n) | O(c*n) | m/c |
| Not in context | O(m*n) | **O(1)** | m*n |

Typical ILL proofs: 5-6 distinct tags, m=10-20 -> 2-3 candidates per lookup -> **5-10x from filtering alone**.

## Edge Cases

- All same tag (e.g. `A*B, C*D, E*F`): no filtering benefit. Rare.
- Small context (m<5): overhead may exceed benefit. Skip indexing.
- Index maintenance: build O(m) once per sequent, amortized.

## Implementation

Index lives in `lib/prover/generic.js`, wrapping `tryIdentity`. First check `goal in contextSet` (hash equality), then filter by `Store.tag(goal)`.

## References

- [Term indexing](https://en.wikipedia.org/wiki/Term_indexing)
- [CMU ATP: Indexing](https://www.cs.cmu.edu/~fp/courses/atp/lectures/22-indexing.html)
- [SWI-Prolog first-argument indexing](https://www.swi-prolog.org/pldoc/man?section=indexing)
- See also: `doc/research/prover-optimization.md`
