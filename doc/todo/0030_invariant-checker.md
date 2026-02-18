---
title: "Invariant Checker"
created: 2026-02-18
modified: 2026-02-18
summary: "Verify initial + preservation conditions for state invariants"
tags: [metaproofs, invariants, verification, implementation]
type: implementation
status: planning
priority: 7
depends_on: [TODO_0029]
required_by: []
---

# Invariant Checker

Extracted from TODO_0008. Given a property in the state DSL, verify:
1. **Initial**: property holds in the initial state
2. **Preservation**: if property holds before a step, it holds after

- [ ] Initial state evaluation
- [ ] Step-wise preservation check across all rules
- [ ] Counter-example on violation (which rule, which state)

See: `doc/research/execution-trees-metaproofs.md`
