---
title: "Forward Optimization Research"
created: 2026-02-18
modified: 2026-02-18
summary: "Research items from forward chaining networks, incremental matching, compiled patterns"
tags: [performance, research, forward-engine, matching]
type: research
status: planning
priority: 3
depends_on: []
required_by: []
---

# Forward Optimization Research

Stages 5-11 are done. These are open research items for future scaling (100+ rules, 100K+ facts).

## TODO_0022.Topic_1 — Forward chaining network optimizations

- [ ] TREAT-style dirty rule tracking — only re-evaluate rules whose trigger predicates changed
- [ ] CHR join ordering — match most selective antecedent first (beyond current deferral)
- [ ] LEAPS delta-driven activation — maintain activation queue instead of scanning all rules
- [ ] Tabled forward chaining — cache symexec subtrees for recurring states

See: `doc/research/forward-chaining-networks.md`

## TODO_0022.Topic_2 — Incremental matching

- [ ] Delta predicate tracking in `findAllMatches` (~30 LOC, helps at any scale)
- [ ] Full semi-naive evaluation at 100K+ facts (positive + negative delta for linear logic)
- [ ] Provenance tracking for non-monotonic semi-naive (which facts contributed to each match)
- [ ] Relational e-matching for multi-antecedent rules (leapfrog trie join at 100K+ facts)

See: `doc/research/incremental-matching.md`

## TODO_0022.Topic_3 — Compiled pattern matching

- [ ] Compile-time first-occurrence vs subsequent-occurrence distinction (WAM get_variable/get_value)
- [ ] Compiled match functions (per-rule specialized matchers, beyond generic match())
- [ ] Interaction between deferral order and first/subsequent classification
- [ ] Maranget-style decision trees for 1000+ rules

See: `doc/research/compiled-pattern-matching.md`, `doc/research/de-bruijn-indexed-matching.md`
