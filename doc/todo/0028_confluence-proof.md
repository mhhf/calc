---
title: "Confluence Proof for Store.put Normalization"
created: 2026-02-18
modified: 2026-02-18
summary: "Prove confluence of restricted Store.put normalization (ground folding) for expression terms"
tags: [research, confluence, normalization, Store]
type: research
status: planning
priority: 6
depends_on: [TODO_0002]
required_by: [TODO_0003]
---

# Confluence Proof

Extracted from TODO_0003. If expression constructors are chosen (TODO_0002.Option_1), the Store needs restricted normalization for ground terms. This normalization must be confluent to ensure deterministic results.

- [ ] Define the rewrite system for ground folding
- [ ] Prove local confluence (critical pair analysis)
- [ ] Prove termination (weight function)
- [ ] Confluence follows from Newman's lemma

See: `doc/research/equational-completion.md`
