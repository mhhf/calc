---
title: "O(1) Identity via Constructor Indexing"
created: 2026-02-10
modified: 2026-02-13
status: draft
summary: Index context by outermost tag for O(1) ground identity and filtered unification.
tags: [optimization, indexing, identity-rule, proof-search]
---

# O(1) Identity via Constructor Indexing

**Verdict:** IMPLEMENT — highest impact single optimization. LOW effort.

## Problem

`tryIdentity` in `lib/prover/generic.js:74` does a linear scan:

```javascript
for (let i = 0; i < linear.length; i++) {
  const theta = unify(linear[i], goal);  // O(n) per attempt
  if (theta) { ... }
}
```

For m context formulas of size n: **O(m·n)** per identity check. Most unify attempts fail (98.6% per benchmarks).

## Key Insight

Two formulas can only unify if they share the same outermost constructor (or one is a variable). Index by `Store.tag(h)` to filter impossible candidates before calling `unify()`.

**Ground case:** With content-addressing, if `goal === linear[i]` (hash equality), identity succeeds in O(1). No unification needed.

## Design

Three-level lookup on the context:

| Level | Key | Lookup | When |
|-------|-----|--------|------|
| 1. Hash equality | `goal` hash | O(1) | Ground formulas (most common) |
| 2. Tag filter | `Store.tag(goal)` | O(c) candidates | Formulas with metavariables |
| 3. Variables | — | O(v) | Variable goals (rare) |

Where c = formulas sharing the same tag (typically c << m), v = variable formulas in context (usually 0).

## Complexity

| Scenario | Current | With Index | Speedup |
|----------|---------|------------|---------|
| Ground formula | O(m·n) | **O(1)** | m·n |
| Goal with metavars | O(m·n) | O(c·n) | m/c |
| Goal is variable | O(m·n) | O(1) | m·n |
| Not in context | O(m·n) | **O(1)** | m·n |

Typical ILL proofs: 5-6 distinct tags, m=10-20 → expect ~2-3 candidates per lookup → **5-10x from filtering alone**, **O(1) for ground** (most cases).

## Edge Cases

- **All same tag:** Context like `A⊗B, C⊗D, E⊗F` — no filtering benefit. Rare in practice.
- **Small context (m<5):** Overhead may exceed benefit. Skip indexing.
- **Index maintenance:** Build O(m) once per sequent, amortized across multiple lookups in focused phase.

## Implementation Notes

Current architecture uses content-addressed hashes (numbers):
- `Store.tag(h)` → outermost constructor tag (e.g., `'tensor'`, `'loli'`, `'atom'`)
- `Store.children(h)` → child hashes
- Context: array of hashes or `{ [hash]: count }` multiset
- `unify(a, b)` → substitution or null

The index should live in `lib/prover/generic.js`, wrapping `tryIdentity`. First check `goal in contextSet` (hash equality), then filter by `Store.tag(goal)`.

## References

- [Term indexing — Wikipedia](https://en.wikipedia.org/wiki/Term_indexing)
- [CMU ATP Course: Indexing](https://www.cs.cmu.edu/~fp/courses/atp/lectures/22-indexing.html)
- [First-argument indexing — SWI-Prolog](https://www.swi-prolog.org/pldoc/man?section=indexing)
