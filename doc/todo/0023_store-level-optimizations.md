---
title: "Store-Level Optimizations"
created: 2026-02-18
modified: 2026-02-18
summary: "isMetavar Set and precomputed variable position maps"
tags: [performance, Store, optimization]
type: implementation
status: planning
priority: 2
depends_on: []
required_by: []
---

# Store-Level Optimizations

Low-priority opportunities identified during precompute audit.

- [ ] `isMetavar`/`isVar` do `Store.get(h)` per call — could maintain a `Set<hash>` of known metavars populated at `Store.put` time. Saves one Map lookup per unify/match step.
- [ ] `freshenTerm`/`freshenClause` walk full clause trees. Could precompute variable position maps per clause at load time so freshening only visits variable positions.
