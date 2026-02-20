---
title: "Incremental Matching"
created: 2026-02-18
modified: 2026-02-18
summary: "Delta predicate tracking, semi-naive evaluation, provenance, relational e-matching"
tags: [performance, research, incremental, semi-naive, matching]
type: research
cluster: Performance
status: planning
priority: 3
depends_on: [TODO_0044]
required_by: []
---

# Incremental Matching

Extracted from TODO_0022.Topic_2. Techniques for scaling matching to 100K+ facts.

- [ ] Delta predicate tracking in `findAllMatches` (~30 LOC, helps at any scale)
- [ ] Full semi-naive evaluation at 100K+ facts (positive + negative delta for linear logic)
- [ ] Provenance tracking for non-monotonic semi-naive (which facts contributed to each match)
- [ ] Relational e-matching for multi-antecedent rules (leapfrog trie join at 100K+ facts)

See: `doc/research/incremental-matching.md`
