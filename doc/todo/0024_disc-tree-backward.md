---
title: "Disc-Tree for Backward Proving"
created: 2026-02-18
modified: 2026-02-18
summary: "Discrimination tree indexing for backward chaining clause selection"
tags: [performance, disc-tree, backward-prover]
type: implementation
cluster: Performance
status: planning
priority: 2
depends_on: []
required_by: []
---

# Disc-Tree for Backward Proving

Currently backward proving uses clause-index scan. At scale (100+ backward clauses), disc-tree could give O(depth) vs O(R) candidate selection — same win as forward disc-tree (Stage 9). Not needed at current scale.

- [ ] Profile backward proving at scale to confirm bottleneck
- [ ] Adapt `lib/prover/strategy/disc-tree.js` for backward clause indexing
