---
title: "MPST-Based Authorization"
created: 2026-02-18
modified: 2026-02-20
summary: "Define atomic swap as global type, implement projection, prove deadlock freedom"
tags: [research, MPST, authorization, session-types]
type: research
cluster: Financial
status: planning
priority: 4
depends_on: []
required_by: []
---

# MPST-Based Authorization

- [ ] Define atomic swap as global type
- [ ] Implement projection algorithm
- [ ] Prove deadlock freedom

## Authorization Modalities (from design exploration)

### Mapping Authorization Concepts to CALC

| Auth Logic | CALC Current | CALC Goal |
|------------|--------------|-----------|
| `A says phi` | -- | `[A] phi` (ownership modality) |
| Linear credential | `linear_ctx` | Same |
| Reusable credential | `persistent_ctx` | Same |
| `A speaks for B` | -- | Mode hierarchy |
| `A ^ B says phi` | -- | `[A ^ B] phi` |
| Threshold | -- | `[k-of-{...}] phi` |

### Implementation Strategy

**Phase 1: Simple Ownership** — `[Alice] A` via multi-type DC (new type per principal), bridge rules for ownership transfer.

**Phase 2: Composite Principals** — `[Alice ^ Bob] A` (both agree), `[Alice v Bob] A` (either suffices). Principal expressions as first-class, inference rules for conjunction/disjunction.

**Phase 3: Thresholds and Weights** — `[2-of-{A,B,C}] A`, `[Alice:0.3, Bob:0.7] A`. Requires graded modalities, combine with semiring quantities from QTT.

### Novel Aspects

1. Ownership modalities as multi-type DC
2. Consensus modalities with thresholds
3. Weighted/graded authorization
4. Cut elimination for the combined logic

### Open Research Questions

1. Can we express `[Alice:0.3, Bob:0.7, threshold:0.5] phi` in multi-type DC?
2. What is the proof theory of composite principals?
3. How do threshold structures interact with linear resources?
4. Can we verify consensus algorithms as authorization proofs?

### Related Work

- **Nomos (CMU)**: Session types + linear types for digital contracts
- **Move (Sui/Aptos)**: Resource types for blockchain
- **Session Types**: Computational interpretation of linear logic
