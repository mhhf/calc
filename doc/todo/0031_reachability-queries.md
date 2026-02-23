---
title: "Reachability Queries"
created: 2026-02-18
modified: 2026-02-23
summary: "Forward reachability (tree search) and backward reachability (coverability) for state properties"
tags: [metaproofs, reachability, verification, WSTS, coverability]
type: implementation
cluster: Verification
status: planning
priority: 7
depends_on: [TODO_0029]
required_by: []
---

# Reachability Queries

Extracted from TODO_0008. See [TODO_0008 §6](0008_metaproofs.md#6-reachability-queries-task_3) for full design.

## Forward Reachability (Phase 1)

Search the symexec execution tree for a leaf satisfying property P:

```javascript
function findReachable(tree, property) {
  if (tree.type === 'leaf' && property(tree.state))
    return { reachable: true, state: tree.state, path: [] };
  if (tree.type === 'branch')
    for (const child of tree.children) {
      const r = findReachable(child.child, property);
      if (r.reachable) { r.path.unshift({rule: child.rule}); return r; }
    }
  return { reachable: false };
}
```

## Backward Reachability (Phase 2, advanced)

For larger state spaces, compute predecessor sets from bad state backwards:
1. Start from target S_bad
2. Pre(S_bad) = { s | ∃ rule r. r(s) ∈ S_bad }
3. Iterate until fixpoint
4. If initial ∈ Pre*(S_bad): reachable. Otherwise: safe.

CALC's multiset states form a WSTS under multiset inclusion → coverability decidable (EXPSPACE, Rackoff 1978).

## Bounded vs Unbounded

| Mode | Guarantee | Cost |
|------|-----------|------|
| Bounded (depth k) | "Not reachable within k steps" | O(\|tree\|) |
| Unbounded (full) | "Not reachable ever" | EXPSPACE |

## Tasks

- [ ] Implement `findReachable(tree, property)` — DFS tree search
- [ ] Implement path extraction (witness trace from root to matching leaf)
- [ ] Tests: known-reachable state found, known-unreachable state not found
- [ ] (Advanced) Implement backward set-saturation for coverability

## References

- Finkel & Schnoebelen (2001) — WSTS framework, backward set-saturation
- Czerwinski et al. (2019) — Petri net reachability non-elementary lower bound
- Cervesato & Scedrov (2009) — MSR reachability for security protocols
