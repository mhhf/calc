---
title: "Invariant Checker"
created: 2026-02-18
modified: 2026-02-23
summary: "Verify invariants via tree traversal (Strategy A) or per-rule preservation (Strategy B)"
tags: [metaproofs, invariants, verification, implementation]
type: implementation
cluster: Verification
status: planning
priority: 7
depends_on: [TODO_0029]
required_by: []
---

# Invariant Checker

Extracted from TODO_0008. See [TODO_0008 §5](0008_metaproofs.md#5-invariant-checker-task_2) for full design.

## Two Strategies

**Strategy A (recommended first): Post-hoc tree traversal.** After `explore()`, walk every node and check invariant. Simple. Gets counterexample traces for free. Works for finite-state programs (EVM with bounded gas).

**Strategy B (future): Per-rule preservation.** Check each rule statically: if invariant holds pre-fire, it holds post-fire. O(|rules|). Needed for unbounded state spaces.

## Implementation (~100 LOC in `lib/engine/verify.js`)

```javascript
function checkInvariant(tree, invariant) {
  const violations = [];
  function walk(node, path) {
    if (node.state && !invariant(node.state)) {
      violations.push({ state: node.state, path: [...path] });
    }
    if (node.type === 'branch') {
      for (const child of node.children) {
        path.push({ rule: child.rule, choice: child.choice });
        walk(child.child, path);
        path.pop();
      }
    }
  }
  walk(tree, []);
  return { holds: violations.length === 0, violations };
}
```

## Tasks

- [ ] Implement `checkInvariant(tree, predicate)` — tree traversal
- [ ] Implement trace extraction for violations (path from root to violating leaf)
- [ ] Tests: known-good invariant (no violations), known-bad (violation found)
- [ ] Integration: `--invariant` flag in `tools/symexec-inspect.js`

## Connection to P-Invariants

P-invariants discovered automatically (TODO_0008.Task_0) can be verified via this checker. The incidence matrix gives conservation laws; the checker confirms they hold across all explored states.

## References

- Ceptre thesis Ch. 6 — consumptive/generative invariants (decidable for propositional fragment)
- Finkel & Schnoebelen (2001) — WSTS decidability framework
