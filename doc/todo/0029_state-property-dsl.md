---
title: "State Property DSL"
created: 2026-02-18
modified: 2026-02-18
summary: "Design language to express invariants over CALC program states"
tags: [metaproofs, DSL, invariants, design]
type: design
cluster: Verification
status: planning
priority: 8
depends_on: []
required_by: [TODO_0030, TODO_0031, TODO_0032]
---

# State Property DSL

Extracted from TODO_0008. A language to express properties over execution states. Foundation for all metaproof tools.

- [ ] Define syntax for state predicates (linear resource counts, persistent fact presence, absence)
- [ ] Quantifiers over state (forall leaves, exists path)
- [ ] Temporal operators? (always, eventually, until)
- [ ] Integration with symexec tree traversal

See: `doc/research/execution-trees-metaproofs.md`
