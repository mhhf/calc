---
title: "Forward Chaining Network Optimizations"
created: 2026-02-18
modified: 2026-02-18
summary: "TREAT, CHR join ordering, LEAPS, tabled forward chaining"
tags: [performance, research, TREAT, CHR, LEAPS, forward-engine]
type: research
status: planning
priority: 3
depends_on: []
required_by: []
---

# Forward Chaining Network Optimizations

Extracted from TODO_0022.Topic_1. Production rule system techniques for scaling to 100+ rules.

- [ ] TREAT-style dirty rule tracking — only re-evaluate rules whose trigger predicates changed
- [ ] CHR join ordering — match most selective antecedent first (beyond current deferral)
- [ ] LEAPS delta-driven activation — maintain activation queue instead of scanning all rules
- [ ] Tabled forward chaining — cache symexec subtrees for recurring states

[TODO_0043](0043_chr-linear-logic-mapping.md) §5 analyzed CHR compilation techniques vs CALC's existing optimizations (comparison tables, concrete improvements). Delta-driven activation is in `doc/dev/forward-optimization-roadmap.md`.

See: `doc/research/forward-chaining-networks.md`
