---
title: "Symbolic Execution: Expression Foundation — Skolem Path (Backlogged)"
created: 2026-02-18
modified: 2026-02-21
summary: "Implement expression type constructors and equational completion — backlogged in favor of eigenvariable/∃ path"
tags: [symexec, expressions, implementation, backlogged]
type: implementation
cluster: Symexec
status: planning
priority: 3
depends_on: [TODO_0002]
required_by: [TODO_0005]
---

# Expression Foundation (Skolem Path — Backlogged)

**Backlogged:** [TODO_0002](0002_symexec-expression-decision.md) decided in favor of eigenvariable/∃ path ([TODO_0004](0004_symexec-backward-foundation.md)). Skolem preserved as fallback if eigenvariable approach proves insufficient.

**Why backlogged:** Skolem axioms create redundant theory (catch-all always available, fallback ordering is implementation not logic). Leads toward K-framework (term rewriting replaces backward chaining). Requires deep inference for normalization. See RQ11 in TODO_0002.

- [ ] Expression type constructors (`calculus/ill/prelude/symbolic.ill`)
- [ ] Catch-all backward clauses (equational completion)
- [ ] Confluence proof — see [TODO_0028](0028_confluence-proof.md)
- [ ] Store.put restricted normalization (ground folding)
- [ ] Import wiring (`evm.ill` → `symbolic.ill`)
- [ ] Integration tests

See: `doc/research/equational-completion.md`, `doc/research/expression-simplification.md`
