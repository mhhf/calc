---
title: "Compiled Pattern Matching"
created: 2026-02-18
modified: 2026-02-18
summary: "Per-rule specialized matchers, WAM-style compilation, Maranget decision trees"
tags: [performance, research, compilation, WAM, Maranget]
type: research
status: planning
priority: 3
depends_on: []
required_by: []
---

# Compiled Pattern Matching

Extracted from TODO_0022.Topic_3. Compile patterns into executable code for 1000+ rules.

- [ ] First-occurrence vs subsequent-occurrence distinction (WAM get_variable/get_value)
- [ ] Per-rule specialized match functions (beyond generic `matchIndexed`)
- [ ] Interaction between deferral order and first/subsequent classification
- [ ] Maranget-style decision trees for multi-rule dispatch

See: `doc/research/compiled-pattern-matching.md`, `doc/research/de-bruijn-indexed-matching.md`
