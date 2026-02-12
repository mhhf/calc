# Manual Prover Refactor

## Architecture

```
                     ManualProofAPI (lib/v2/prover/manual.js)
                    /              \
        focused mode              unfocused mode
        (Phase 1→2→3)            (all rules, no Focus)
              |                        |
        proofLogicV2.ts (thin wrapper, format conversion)
              |                        |
        ManualProof.tsx (pure view: tree, rule selector, split dialog)
```

ManualProofAPI is the **single source of truth**. The UI layer is a thin adapter. No proving logic in the UI.

## Confirmed Bugs

Reproduction: `tests/debug-manual.js`

### Bug 1: Unfocused mode only shows invertible rules + Focus

`getApplicableActions` only has two phases: inversion (invertible rules + Focus) and focused (decomposition rules). There's no unfocused mode — the UI's "unfocused" toggle just suppresses the focus propagation, which makes Focus actions useless while still showing them.

**Root**: `proofLogicV2.ts:457` guards focus propagation with `mode === 'focused'`. In unfocused mode, the API always sees inversion phase, so non-invertible rules (tensor_r, loli_l, with_l1, with_l2) are never returned.

### Bug 2: Focus actions shown in unfocused mode

The manual API always returns Focus actions during inversion (lines 167-193). The UI doesn't filter them in unfocused mode.

### Bug 3: Focus_L displayed as "Focus"

`action.name` is `'Focus'` for both L and R. `action.displayName` has the correct `'Focus_L'`/`'Focus_R'` but the UI uses `action.name` for display.

## Proposed Fix

### 1. Add unfocused mode to ManualProofAPI

Add `mode` parameter to `getApplicableActions`:

```javascript
getApplicableActions(state, opts = {})
  // opts.mode: 'focused' (default) | 'unfocused'
```

**Unfocused mode** returns ALL structurally applicable rules:
- Right rules: if `succedent` has tag T, offer `T_r`
- Left rules: for each `linear[i]` with tag T, offer `T_l`, `T_l1`, `T_l2`
- Identity: if any `linear[i] === succedent`
- **No Focus/Blur actions**
- Context splitting still applies (tensor_r, loli_l)

This reuses the existing `buildRuleAction` — no new proving logic needed.

**Focused mode** stays as-is (inversion → focus → decomposition).

### 2. Fix focus propagation in focused mode

`proofLogicV2.ts:457` — always propagate focus from `delta_in` when it exists, regardless of mode. The API's `getApplicableActions` handles the phase logic; the UI layer shouldn't second-guess it.

### 3. Fix rule naming

Use `action.displayName` (not `action.name`) for UI display. Or rename `action.name` to include L/R.

### 4. Clean up dead code in proofLogicV2.ts

Remove unused functions that duplicate ManualProofAPI logic:
- `tryComputePremises` (line 332)
- `getRuleSpecs` (line 323)
- `isRuleInvertible` (line 388)
- `isFocusable` (line 404)
- `isContextSplittingRule` (line 293) — use API's `isContextSplitting` instead

## Implementation Plan

### Phase 1: ManualProofAPI — add unfocused mode

**File: `lib/v2/prover/manual.js`**

In `getApplicableActions(state, opts = {})`:

```javascript
if (opts.mode === 'unfocused') {
  // Identity
  if (succedent && linear.some(h => h === succedent)) {
    actions.push({ type: 'rule', name: 'id', ... });
  }

  // Right rules (all, not just invertible)
  if (succedent && connective(succedent)) {
    const tag = connective(succedent);
    for (const suffix of ['', '1', '2']) {
      const rn = `${tag}_r${suffix}`;
      if (ruleSpecs[rn]) actions.push(buildRuleAction(rn, 'R', -1, succedent, seq, state.delta));
    }
  }

  // Left rules (all, not just invertible)
  for (let i = 0; i < linear.length; i++) {
    if (!isAtomic(linear[i])) {
      const tag = connective(linear[i]);
      for (const suffix of ['', '1', '2']) {
        const rn = `${tag}_l${suffix}`;
        if (ruleSpecs[rn]) actions.push(buildRuleAction(rn, 'L', i, linear[i], seq, state.delta));
      }
    }
  }

  return actions.filter(Boolean);
}
```

Everything else stays the same.

### Phase 2: Fix proofLogicV2.ts

1. Always propagate focus from `delta_in` (remove `mode === 'focused'` guard)
2. Pass `mode` to API: `api.getApplicableActions(proofState, { mode })`
3. Remove dead code
4. Use `displayName` for UI display

### Phase 3: Fix ManualProof.tsx

Minimal — the UI already delegates to `getApplicableRules`. Once the logic layer is fixed, the UI should work.

## Testing Strategy

### Level 1: ManualProofAPI unit tests (pure logic)

Test `getApplicableActions` in both modes. Parse ASCII sequents, assert rule sets.

```javascript
// unfocused mode: all applicable rules
const seq = parse('P -o (R & Q) |- (P -o Q) & (P -o R)');
const state = api.createProofState(seq);
const rules = api.getApplicableActions(state, { mode: 'unfocused' });
assertRuleNames(rules, ['with_r', 'loli_l']);
assertNoFocus(rules);

// focused mode: only invertible + focus
const focused = api.getApplicableActions(state, { mode: 'focused' });
assertRuleNames(focused, ['with_r']);
assertFocusTargets(focused, [{ pos: 'L', idx: 0 }]);
```

### Level 2: Step-by-step proof flow tests

Walk through entire proofs, asserting rules and premises at each step:

```javascript
// Distribution: P -o (R & Q) |- (P -o Q) & (P -o R)
// Step 1: with_r → two premises
// Step 2 (premise 1): loli_r → P -o (R & Q), P |- Q
// Step 3: Focus_L on loli → loli_l → split
// Step 4: id on each leaf
```

Both unfocused and focused paths should produce correct proofs.

### Level 3: Regression tests

Add the user's specific failing scenarios as test cases:
- Distribution example (above)
- Modus ponens: `P, P -o Q |- Q`
- Tensor commutativity: `P * Q |- Q * P`
- With elimination: `A & B |- A`

### Test files

- `tests/manual-prover-logic.test.js` — 38 API unit tests (rule suggestions, focusing phases, context splitting, premises, action application)
- `tests/manual-proof-flow.test.js` — 15 integration tests (complete proofs in both modes, edge cases)

Fast feedback: `node --test tests/manual-prover-logic.test.js tests/manual-proof-flow.test.js`

## Status: IMPLEMENTED

All fixes applied and tested (67/67 tests pass):
- `lib/v2/prover/manual.js` — unfocused mode added, Focus names fixed
- `src/ui/lib/proofLogicV2.ts` — focus always propagated, mode passed to API, dead code removed
- `src/ui/pages/ManualProof.tsx` — debug logs removed, Focus_L/R handled
