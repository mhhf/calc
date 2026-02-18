---
title: "Counter-Example Generation"
created: 2026-02-18
modified: 2026-02-18
summary: "Generate execution trace to a state violating a property"
tags: [metaproofs, counterexample, debugging]
type: implementation
status: planning
priority: 6
depends_on: [TODO_0029]
required_by: []
---

# Counter-Example Generation

Extracted from TODO_0008. When an invariant fails or a bad state is reachable, produce a minimal trace.

- [ ] Trace extraction from symexec tree path
- [ ] Trace minimization (shortest path to violation)
- [ ] Human-readable trace formatting (rule names, state diffs)

See: `doc/research/execution-trees-metaproofs.md`
