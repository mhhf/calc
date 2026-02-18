---
title: "Induction and Coinduction (Fixed Points)"
created: 2026-02-18
modified: 2026-02-18
summary: "Handle unbounded/infinite behavior via fixed point connectives"
tags: [fixed-points, induction, coinduction, cyclic-proofs]
type: research
status: planning
priority: 5
depends_on: [TODO_0008]
required_by: []
---

# Induction and Coinduction

Handle unbounded/infinite behavior: recursive contracts, streaming payments.

Already implemented:
- Cycle detection in forward chaining — back-edge detection via commutative XOR hash
- Bounded exploration with depth limit — `maxDepth` option

Open:
- [ ] Fixed point syntax (mu, nu connectives)
- [ ] Progress checking for cyclic proofs

See: `doc/research/execution-trees-metaproofs.md`, `doc/research/muMALL-fixed-points.md`
