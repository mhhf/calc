---
title: Core/Calculus Separation
created: 2026-02-10
modified: 2026-02-11
summary: Design for generic prover vs ILL-specific focused prover
tags: [architecture, prover, design]
status: active
---

# Core/Calculus Separation

Separate generic "Gentzen machinery" from logic-specific optimized provers.

## Two Provers

```
┌─────────────────────────────────────────┐
│          ILL Prover (Specialized)       │
│   Focused proof search, lazy splitting  │
│   - Fast (polynomial for ILL)           │
│   - Uses focusing, polarity, delta_in   │
│   - Status: ✓ Implemented               │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│          Generic Prover (Core)          │
│   "Try all rules including structural"  │
│   - Works for ANY calculus              │
│   - Slow (no optimizations)             │
│   - Can verify proof trees              │
│   - Status: NOT IMPLEMENTED             │
└─────────────────────────────────────────┘
```

## Why Separate?

1. **Correctness**: GenericProver is simple enough to trust
2. **Verification**: `GenericProver.verify(proof)` catches bugs
3. **Experimentation**: ILLProver can use any optimizations

## Current Structure

```
lib/v2/prover/
├── focused/          # ✓ ILL-specific focused prover
│   ├── prover.js
│   ├── state.js
│   └── context.js
├── forward.js        # Forward chaining
├── pt.js             # Proof trees
└── index.js
```

## Remaining Work

### 1. GenericProver Implementation

```javascript
class GenericProver {
  prove(goal: Sequent): ProofResult;   // Try all rules
  verify(proof: ProofTree): boolean;   // Check proof validity
}
```

Key issues:
- Loop detection (structural rules can loop)
- Depth limiting
- Canonical sequent forms

### 2. Verification Interface

```javascript
const proof = focusedProver.prove(goal);
if (genericProver.verify(proof)) {
  // Trusted
}
```

## References

- [[architecture-pipelines]] - v2 architecture
- [[focusing_refactoring]] - Focused prover details
- Research: [[prover-architecture]]
