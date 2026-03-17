---
title: "Manual Prover Allows bang_r With Non-Empty Linear Context"
created: 2026-02-20
modified: 2026-02-20
summary: "buildRuleAction() in manual.js never checks requiresEmptyDelta, so the UI offers bang_r (promotion) even when the linear context is non-empty. This lets users construct invalid proofs."
tags: [bug, soundness, manual-prover]
type: bug
status: ready for implementation
priority: 8
depends_on: []
required_by: []
---

# Manual Prover Allows bang_r With Non-Empty Linear Context

## Bug

The manual prover offers `bang_r` (promotion) as an applicable rule even when the linear context is non-empty. ILL's promotion rule requires the linear context to be empty:

```
!Γ; · ⊢ A
────────── !R (bang_r)
!Γ; · ⊢ !A
```

This allows constructing invalid derivations like `!A ⊸ B ⊢ !(A ⊸ B)`, which would collapse the linear/persistent distinction — a foundational guarantee of ILL.

## Root Cause

The `requiresEmptyDelta` constraint is correctly propagated through the entire pipeline:

| Component | Enforces? |
|---|---|
| `ill.rules` — `promotion` rule has empty linear conclusion | ✓ |
| `rules2-parser.js:167` — detects `emptyLinear: true` | ✓ |
| `rule-interpreter.js:72` — sets `requiresEmptyDelta: true` on spec | ✓ |
| `focused.js:266-268` — checks before applying | ✓ |
| **`manual.js:buildRuleAction()` — never checks** | **BUG** |

The focused (automatic) prover correctly enforces it. Only the manual prover is affected.

## Fix

In `buildRuleAction()` (manual.js), after computing `remainingDelta`, add:

```javascript
if (spec.requiresEmptyDelta && !Context.isEmpty(remainingDelta)) {
  return null;
}
```

Also add a test in `tests/manual-prover-logic.test.js` that verifies bang_r is NOT offered when the linear context is non-empty.
