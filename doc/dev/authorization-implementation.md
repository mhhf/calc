---
title: Ownership & Authorization Plan
created: 2026-02-10
modified: 2026-02-10
summary: Implementation plan for authorization modalities, composite principals, and threshold structures using multi-type display calculus
tags: [authorization, ownership, modalities, consensus, research]
priority: LOW
---

# Ownership & Authorization Implementation Plan

Implementation plan for authorization/ownership modalities in CALC, based on research in `dev/research/authorization-logic.md`.

---

## Current CALC Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     CALC (Current)                          │
├─────────────────────────────────────────────────────────────┤
│  persistent_ctx (Cartesian)  ←── Bang_L ──→  linear_ctx    │
│         ↓                                         ↓         │
│   Reusable resources              Consumable resources      │
│   (like !A in auth logic)         (linear credentials)      │
└─────────────────────────────────────────────────────────────┘
```

---

## Mapping Authorization Concepts to CALC

| Auth Logic | CALC Current | CALC Goal |
|------------|--------------|-----------|
| `A says φ` | — | `[A] φ` (ownership modality) |
| Linear credential | `linear_ctx` | Same |
| Reusable credential | `persistent_ctx` | Same |
| `A speaks for B` | — | Mode hierarchy |
| `A ∧ B says φ` | — | `[A ∧ B] φ` |
| Threshold | — | `[k-of-{...}] φ` |

---

## What We Need to Add

1. **Principal-indexed modalities**: `[Alice] φ`, `[Bob] φ`
2. **Mode hierarchy (partial order)**:
   ```
   shared ≥ alice, shared ≥ bob    (shared dominates individuals)
   alice ⊥ bob                      (incomparable)
   ```
3. **Composite principals**: `[Alice ∧ Bob]`, `[Alice ∨ Bob]`
4. **Threshold structures**: `[2-of-{A,B,C}]`
5. **Graded versions**: Weights on principals

---

## Implementation Strategy

### Phase 1: Simple Ownership

```
[Alice] A        -- Alice owns A
```

- Add ownership modality to .calc/.rules
- Implement as multi-type DC (new type per principal)
- Bridge rules: ownership transfer

### Phase 2: Composite Principals

```
[Alice ∧ Bob] A  -- Both Alice and Bob must agree
[Alice ∨ Bob] A  -- Either Alice or Bob suffices
```

- Principal expressions as first-class
- Inference rules for conjunction/disjunction of principals

### Phase 3: Thresholds and Weights

```
[2-of-{A,B,C}] A             -- Threshold
[Alice:0.3, Bob:0.7] A       -- Weighted
```

- Requires graded modalities
- Combine with semiring quantities from QTT

---

## CALC's Potential Contribution

**Thesis:** Multi-type display calculus provides a clean framework for:
- Authorization modalities (types for principals)
- Linear resources (type for consumables)
- Adjunctions for delegation (mode morphisms)
- Graded modalities for quantities

**Novel aspects:**
1. Ownership modalities as multi-type DC
2. Consensus modalities with thresholds
3. Weighted/graded authorization
4. Cut elimination for the combined logic

---

## Open Research Questions

1. Can we express `[Alice:0.3, Bob:0.7, threshold:0.5] φ` in multi-type DC?
2. What is the proof theory of composite principals?
3. How do threshold structures interact with linear resources?
4. Can we verify consensus algorithms as authorization proofs?

---

## What's Missing in Literature

1. **Weighted/graded authorization**: No existing work combines:
   - Authorization modalities (`A says`)
   - Graded modalities (semiring quantities)
   - Threshold predicates

2. **Consensus as modality**: Nobody has modeled:
   - PoW/PoS as authorization mechanisms
   - Weighted voting with linear resources
   - Dynamic consensus formation

3. **Multi-type DC for authorization**: Existing work uses standard or labeled sequent calculus, not multi-type display calculus with adjoint decomposition.

---

## Related Work

- **Nomos (CMU)**: Session types + linear types for digital contracts
- **Move (Sui/Aptos)**: Resource types for blockchain
- **Session Types**: Computational interpretation of linear logic

See `dev/research/authorization-logic.md` for full theory background and bibliography.

---

*Created: 2026-02-10*
