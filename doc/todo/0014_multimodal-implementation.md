---
title: "Multimodal Implementation"
created: 2026-02-18
modified: 2026-02-18
summary: "Implement ownership, authorization, and graded modalities"
tags: [multimodal, ownership, authorization, graded-types, implementation]
type: implementation
status: planning
priority: 8
depends_on: []
required_by: []
---

# Multimodal Implementation

Ownership `[Alice] A`, authorization `<Alice> A`, graded `[]_r token`.

Key decisions: MTDC with parametric indices (not SELL), user-centric ownership, quantities are object-level terms.

- [ ] Extend parser for `[P]`, `<P>`, `[]_r` modalities
- [ ] Implement fresh name generation
- [ ] Implement `WITH` clause for atomic deposit
- [ ] Forward-chaining engine for rule application
- [ ] Worked examples: token, transfer, atomic swap, AMM

See: `doc/research/multimodal-linear-logic.md`, `doc/research/ownership-design.md`
