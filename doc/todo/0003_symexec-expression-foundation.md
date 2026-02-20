---
title: "Symbolic Execution: Expression Foundation (Phase 3a)"
created: 2026-02-18
modified: 2026-02-18
summary: "Implement expression type constructors and equational completion — if expressions chosen"
tags: [symexec, expressions, implementation]
type: implementation
cluster: Symexec
status: planning
priority: 8
depends_on: [TODO_0002]
required_by: [TODO_0005]
---

# Expression Foundation

Only if TODO_0002 decides in favor of expression constructors.

- [ ] Expression type constructors (`calculus/ill/prelude/symbolic.ill`)
- [ ] Catch-all backward clauses (equational completion)
- [ ] Confluence proof — see [TODO_0028](0028_confluence-proof.md)
- [ ] Store.put restricted normalization (ground folding)
- [ ] Import wiring (`evm.ill` -> `symbolic.ill`)
- [ ] Integration tests

See: `doc/research/equational-completion.md`, `doc/research/expression-simplification.md`
