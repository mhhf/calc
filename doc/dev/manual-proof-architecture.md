# Manual Proof Architecture

## Suckless Principle

**Single Source of Truth**: The prover owns all proof logic. The UI is a pure view layer.

```
┌─────────────────────────────────────────────────────────┐
│                    PROVER                               │
│  (lib/v2/prover/manual.js - SINGLE SOURCE OF TRUTH)    │
│                                                         │
│  State:   ProofState { conclusion, focus, delta, ... } │
│  Actions: getApplicableActions(state) → Action[]       │
│  Apply:   applyAction(state, action) → ProofState      │
│  Render:  renderSequent(seq, fmt, focus) → string      │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│                      UI                                 │
│  (proofLogicV2.ts - THIN WRAPPER)                      │
│                                                         │
│  - Passes node directly to API (no state extraction)   │
│  - Converts types if needed                            │
│  - NEVER reimplements logic                            │
└─────────────────────────────────────────────────────────┘
```

## Key Design Decision

**The function extracts what it needs from the node.**

BAD (requires caller to do state threading):
```typescript
// Caller must extract and pass state - error prone!
const focus = node.delta_in?.focusPosition;
getApplicableRules(node.conclusion, { focusState: focus });
```

GOOD (function extracts what it needs):
```typescript
// Just pass the node - function reads delta_in itself
getApplicableRules(node, { mode: 'focused' });
```

## Components

### ManualProofAPI (`lib/v2/prover/manual.js`)

Single source of truth for interactive proofs:

```javascript
createManualProofAPI(calculus) → {
  // State
  createProofState(seq)           // Initial state with delta tracking
  cloneState(state)               // Immutable updates

  // Actions
  getApplicableActions(state)     // What can be done
  applyAction(state, action)      // Do it, get new state

  // Rendering
  renderSequent(seq, fmt, focus)  // With focus highlighting [A ⊸ B]
  getAbstractRule(name)           // Schema for rule display
}
```

### UI Layer (`proofLogicV2.ts`)

Thin wrapper that delegates to ManualProofAPI:

```typescript
// SUCKLESS: Takes node, extracts focus from delta_in internally
getApplicableRules(node, { mode }) → ApplicableRule[]

// Delegates to API
applyRule(pt, ruleName, position) → ProofTreeNode
applyRuleWithSplit(pt, ruleName, position, split) → ProofTreeNode
```

## Focus Phase Tracking

Focus is stored in `ProofTreeNode.delta_in`:
```typescript
{
  focusPosition: 'L' | 'R',  // Side of focused formula
  focusId: string | null     // Index in context (null for right)
}
```

The `getApplicableRules` function reads this directly from the node - callers don't need to extract and pass it.

## Rule Display

Inference rules use standard orientation:
- **Premises** ABOVE the line (what we prove next)
- **Conclusion** BELOW the line (what we started with)

```
  Γ, [A] ⊢ C    ← premise (focused state)
─────────────── Focus_L
   Γ, A ⊢ C     ← conclusion (unfocused state)
```

## Tests

- `tests/manual-api.test.js` - Unit tests for ManualProofAPI
- `tests/ui-flow.test.js` - Integration tests verifying:
  - Focus actions available in inversion phase
  - After focus: only rule for focused formula (NOT Focus again)
  - Focus_L schema has correct orientation
  - Context split detection works
