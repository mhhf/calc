---
title: "Counter-Example Generation"
created: 2026-02-18
modified: 2026-02-23
summary: "Extract, minimize, and format execution traces for property violations"
tags: [metaproofs, counterexample, debugging, trace]
type: implementation
cluster: Verification
status: planning
priority: 6
depends_on: [TODO_0029]
required_by: []
---

# Counter-Example Generation

Extracted from TODO_0008. See [TODO_0008 §7](0008_metaproofs.md#7-counter-example-generation-task_4) for full design.

When an invariant fails or a bad state is reachable, produce a minimal human-readable trace.

## Three Steps

### 1. Trace Extraction (~30 LOC)

DFS from tree root to violating leaf, recording each rule application:

```javascript
function extractTrace(tree, target) {
  // Returns: [{rule, choice}, {rule, choice}, ...] from root to target
}
```

### 2. Trace Minimization (~50 LOC)

Remove steps irrelevant to the violation:
- **Backward slicing:** From violating fact, trace backward keeping only contributing steps
- **Delta-debugging:** Binary search on trace prefixes for shortest violating prefix

### 3. Human-Readable Formatting (~40 LOC)

Show each step as rule name + state diff (consumed/produced facts):

```
transfer:
  - token(alice, 100) ×1
  - request(alice, bob, 200) ×1
  + token(alice, -100) ×1        ← VIOLATION: negative balance
  + token(bob, 200) ×1
```

State diffs are computable from `mutateState`'s undo log: `[type, hash, oldValue, ...]`.

## Tasks

- [ ] Implement `extractTrace(tree, violatingLeaf)` — DFS path finder
- [ ] Implement `formatTrace(trace)` — using `show(hash)` from show.js
- [ ] Implement trace minimization (backward slicing)
- [ ] Integration: CLI output when `--check` finds violation
- [ ] Tests: known violation produces correct minimal trace

## CLI Integration

```bash
node tools/symexec-inspect.js --check "count('pc') === 1" program.ill
# Output: VIOLATION at leaf 7
#   Step 1: rule/foo — consumed pc(0), produced pc(1), pc(2)
#   ← pc count becomes 2, violating invariant
```
