---
title: Focusing Architecture Refactor
created: 2026-02-10
modified: 2026-02-10
summary: Analysis of hybrid focusing architecture and options for cleaner separation between logic definition and proof search strategy
tags: [focusing, architecture, refactor, proof-search, andreoli]
---

# Focusing Architecture: Refactoring Considerations

This document analyzes the current hybrid focusing architecture and proposes options for refactoring to achieve a cleaner separation of concerns.

---

## Table of Contents

1. [Current State: The Hybrid Problem](#current-state-the-hybrid-problem)
2. [What is Focusing?](#what-is-focusing)
3. [Option A: Remove from Object Logic](#option-a-remove-from-object-logic)
4. [Option B: Full Object Logic Specification](#option-b-full-object-logic-specification)
5. [Option C: Declarative Hints + Generic Prover](#option-c-declarative-hints--generic-prover)
6. [Comparison Matrix](#comparison-matrix)
7. [How Other Systems Handle This](#how-other-systems-handle-this)
8. [Recommendation](#recommendation)
9. [Implementation Considerations](#implementation-considerations)
10. [Open Questions](#open-questions)

---

## Current State: The Hybrid Problem

The current architecture has focusing split awkwardly between two places:

### In `ll.json` (Object Logic Definition)

```json
"Formula": {
  "Focused_Formula": {
    "type": "Formula",
    "ascii": "[ _ ]",
    "latex": "[ _ ]"
  }
},
"Structure": {
  "Structure_Focused_Term_Formula": {
    "type": ["Term", "FFormula"],
    "ascii": "_ : _"
  }
},
"polarity": {
  "Formula_Tensor": "positive",
  "Formula_Loli": "negative",
  "Formula_With": "negative",
  "Formula_Lax": "positive",
  "Formula_Bang": "positive",
  "Formula_Forall": "negative"
}
```

### In `proofstate.js` (Proof Search Implementation)

```javascript
// Focus operation - NOT a rule from ll.json
Proofstate.focus = function (pt, id) {
  // ... focuses formula, sets pt.type = "Focus_L" or "Focus_R"
}

// Auto-prover decides WHEN to focus based on polarity
else if(pt.conclusion.succedent.isLax() || o.mode === "proof") {
  let isRightFocusable = suc.isPositive(o);
  let leftFilter = Object.keys(seq.linear_ctx)
    .filter(id => seq.linear_ctx[id].val.isNegative(o))
  // ...
}
```

### The Problems

1. **Unclear ownership**: Is focusing part of the logic (ll.json) or the prover (proofstate.js)?

2. **Rules appear from nowhere**: `Focus_L` and `Focus_R` appear in proof trees but aren't defined in ll.json's rules.

3. **Polarity duplication**: `ll.json` specifies polarity, but `proofstate.js` has hardcoded logic for using it.

4. **Not generic**: The focusing strategy is hardcoded for this specific logic. A different logic would need different code.

5. **UI confusion**: Should the UI show focus rules? Currently it hides them, but they appear in proofs.

---

## What is Focusing?

[Andreoli's focusing](https://arxiv.org/abs/0708.2252) is a **proof search discipline** that:

1. **Partitions connectives by polarity**:
   - **Positive/Synchronous**: ⊗, ⊕, !, ∃, 1, 0 - require choices, not invertible
   - **Negative/Asynchronous**: ⅋, &, ?, ∀, ⊥, ⊤ - no choices, invertible

2. **Defines two phases**:
   - **Inversion phase**: Apply all invertible (negative) rules eagerly
   - **Focusing phase**: Pick ONE positive formula to decompose completely

3. **Reduces non-determinism**: Instead of choosing which rule at each step, only choose which formula to focus on.

### Key Insight

Focusing is **complete**: every provable sequent has a focused proof. But it's a **proof search strategy**, not a change to what's provable.

**Analogy**: Like depth-first vs breadth-first search - same reachable nodes, different traversal order.

---

## Option A: Remove from Object Logic

**Philosophy**: Focusing is purely a proof search optimization. The object logic shouldn't know about it.

### Changes to ll.json

```json
// REMOVE these:
"Focused_Formula": { ... },
"Structure_Focused_Term_Formula": { ... },
"polarity": { ... }
```

Rules would be written in unfocused form:
```json
"Loli_L": [
  "?X, ?Y, -- : F?A -o F?B |- -- : F?C",
  "?X |- -- : F?A",
  "?Y, -- : F?B |- -- : F?C"
]
```

### Changes to proofstate.js

The prover would:
1. Internally track a "focus" state (not in sequent syntax)
2. Compute polarity from connective definitions (or have it hardcoded per-logic)
3. Apply focusing strategy during search
4. Present proofs without focus markers (or with them as annotations)

### Pros

- Clean separation: logic is logic, search is search
- Simpler `ll.json` - no meta-level syntax
- Rules are more readable (no `[ ]` brackets everywhere)
- Easier to define new logics

### Cons

- Prover becomes logic-specific (knows about Loli, Tensor, etc.)
- Hard to support different focusing strategies for different logics
- Polarity must be computed or hardcoded somewhere
- Proof output differs from internal representation

---

## Option B: Full Object Logic Specification

**Philosophy**: Focusing IS part of the logic. The prover should be generic and read focusing rules from ll.json.

### Changes to ll.json

Add explicit focus rules:
```json
"RuleFocus": {
  "Focus_R": [
    "?X |- -- : F?A",
    "?X |- -- : [ F?A ]"
  ],
  "Focus_L": [
    "?X, -- : F?A |- -- : F?B",
    "?X, -- : [ F?A ] |- -- : F?B"
  ],
  "Blur_R": [
    "?X |- -- : [ F?A ]",
    "?X |- -- : F?A"
  ],
  "Blur_L": [
    "?X, -- : [ F?A ] |- -- : F?B",
    "?X, -- : F?A |- -- : F?B"
  ]
}
```

Add focusing metadata:
```json
"focusing": {
  "enabled": true,
  "phases": ["inversion", "focus"],
  "polarity": {
    "Formula_Tensor": "positive",
    "Formula_Loli": "negative",
    ...
  },
  "inversion_rules": {
    "right_negative": ["Loli_R", "With_R", "Forall_R"],
    "left_positive": ["Tensor_L", "Plus_L", "Bang_L"]
  },
  "focus_triggers": {
    "right_positive": "can_focus",
    "left_negative": "can_focus"
  }
}
```

### Changes to proofstate.js

Make the prover completely generic:
```javascript
Proofstate.auto = function(pt, o) {
  const focusingConfig = o.calc.focusing;

  if (!focusingConfig || !focusingConfig.enabled) {
    return genericUnfocusedSearch(pt, o);
  }

  // Phase 1: Inversion
  const invertible = findInvertibleRule(pt, focusingConfig);
  if (invertible) {
    return applyRule(pt, invertible, o);
  }

  // Phase 2: Focusing
  const focusable = findFocusableFormula(pt, focusingConfig);
  // ...
}
```

### Pros

- Fully generic prover - works for any logic with focusing
- ll.json is the single source of truth
- Can support different focusing disciplines per logic
- Focus rules appear in proofs naturally

### Cons

- More complex ll.json specification
- Higher learning curve for defining new logics
- Overly general for simple cases
- Focus rules add "noise" to proofs

---

## Option C: Declarative Hints + Generic Prover

**Philosophy**: ll.json provides declarative "hints" (polarity, invertibility), and a semi-generic prover interprets them. Focus is an implementation detail, not a rule.

### Changes to ll.json

Keep polarity but make it optional metadata:
```json
"proof_search_hints": {
  "strategy": "focused",
  "polarity": {
    "Formula_Tensor": "positive",
    "Formula_Loli": "negative",
    ...
  },
  "invertible": {
    "right": ["Loli_R", "With_R"],
    "left": ["Tensor_L", "Plus_L"]
  }
}
```

Remove `Focused_Formula` and `Structure_Focused_Term_Formula` - these become internal to the prover.

Rules stay in unfocused form:
```json
"Loli_L": [
  "?X, ?Y, -- : F?A -o F?B |- -- : F?C",
  "?X |- -- : F?A",
  "?Y, -- : F?B |- -- : F?C"
]
```

### Changes to proofstate.js

```javascript
Proofstate.auto = function(pt, o) {
  const hints = o.calc.proof_search_hints || {};

  if (hints.strategy === 'focused') {
    return focusedSearch(pt, o, hints);
  } else if (hints.strategy === 'tableaux') {
    return tableauxSearch(pt, o, hints);
  } else {
    return naiveSearch(pt, o);
  }
}

function focusedSearch(pt, o, hints) {
  // Use hints.polarity and hints.invertible
  // But focus is internal state, not in sequent syntax
}
```

### Pros

- Clean rules (no focus syntax)
- Prover can use hints intelligently
- Easy to add new strategies
- Hints are optional - can fall back to naive search
- Good balance of configurability vs simplicity

### Cons

- Still some logic-specific knowledge in prover
- Hints might not capture all focusing variants
- Two representations: rules (unfocused) vs internal (focused)

---

## Comparison Matrix

| Criterion | Option A (Remove) | Option B (Full OL) | Option C (Hints) |
|-----------|------------------|-------------------|------------------|
| **Simplicity of ll.json** | ★★★ | ★ | ★★ |
| **Generic prover** | ★ | ★★★ | ★★ |
| **Proof readability** | ★★★ | ★★ | ★★★ |
| **Support multiple logics** | ★ | ★★★ | ★★ |
| **Support multiple strategies** | ★ | ★★★ | ★★ |
| **Implementation effort** | ★★ | ★ | ★★ |
| **UI clarity** | ★★★ | ★★ | ★★★ |

---

## How Other Systems Handle This

### Twelf/Celf

- Focusing is **built into the framework**, not user-specified
- Polarity is derived from connective definitions
- Users don't write focus rules
- Proofs may or may not expose focus steps

**Architecture**: Option A (prover owns focusing)

### Calculus-Toolbox-2

- Display calculus focus (structural rules)
- Focusing NOT built in - user would define focus rules explicitly
- Proof search is naive (no automatic focusing)

**Architecture**: Neither - relies on display postulates, not focusing

### Logitext

- Educational tool for natural deduction
- No focusing (not needed for intuitionistic logic)
- Simple rule application

**Architecture**: N/A

### Coq/Lean (via tactics)

- Focusing is a **tactic**, not a core feature
- Users invoke focusing explicitly when wanted
- Proof terms don't contain focus markers

**Architecture**: Option A with manual invocation

---

## Recommendation

**Recommended: Option C (Declarative Hints) as a stepping stone toward Option B.**

### Rationale

1. **Immediate benefit**: Clean up the current hybrid by removing focus syntax from rules while keeping polarity hints.

2. **Future-proof**: The hints structure can evolve into full Option B if we need more configurability.

3. **UI alignment**: Rules without focus syntax are easier to display and understand.

4. **Pragmatic**: We can implement this incrementally without breaking existing functionality.

### Migration Path

**Phase 1**: Clean up current system
- Remove `Focused_Formula` from ll.json (move to prover internal)
- Keep `polarity` in ll.json as hints
- Prover internally handles focus state

**Phase 2**: Generalize hints
- Add `proof_search_hints` section
- Make prover strategy-agnostic
- Support different logics with different hints

**Phase 3** (if needed): Full specification
- If we need multiple focusing disciplines per logic
- Or want user-defined focus rules
- Evolve hints into full Option B

---

## Implementation Considerations

### Internal Focus Representation

Instead of syntax like `[ F?A ]`, use an internal wrapper:
```javascript
class FocusedFormula {
  constructor(formula, position) {
    this.formula = formula;
    this.position = position; // 'L' or 'R'
  }
}
```

### Rule Application with Internal Focus

When applying a rule that expects focused input:
```javascript
function applyFocusedRule(pt, rule, focusId) {
  // 1. Verify formula at focusId matches rule's expected focus
  // 2. Apply rule using internal focus state
  // 3. Update proof tree
  // 4. For output, optionally annotate with focus info
}
```

### Proof Display Options

1. **Hide focus completely**: Show proofs without Focus_L/Focus_R steps
2. **Show as annotations**: Mark focused formulas but don't show as separate rules
3. **Full display**: Keep current behavior (Focus_L/Focus_R as rule names)

Recommendation: Option 2 - focused formulas get a visual marker (like underline or color) but don't clutter the proof tree with extra nodes.

---

## Open Questions

### Q1: Should the UI ever show focus choices to the user?

**Current answer**: No - focusing is automatic based on polarity.

**Alternative**: For educational purposes, could show "you can focus on A, B, or C" and let user choose. But this adds complexity.

**Recommendation**: Keep automatic for now. Revisit if users request manual control.

### Q2: What about logics without clear polarity?

Some logics (classical, certain modal logics) don't have the polarity structure that makes focusing work.

**Options**:
- Fall back to unfocused search
- Use different strategy (tableaux, resolution)
- Let user specify polarity assignments

**Recommendation**: Support multiple strategies in hints, fall back gracefully.

### Q3: How to handle the With rule?

The `With_R` rule is special - it duplicates context to both premises (additive). The current code has:
```javascript
let propagate = pt.type === "With_R";
```

This is hardcoded logic-specific knowledge.

**Options**:
- Add "propagation" hint per rule
- Derive from rule structure (if both premises have same context variable)
- Accept some hardcoding for common patterns

**Recommendation**: Add per-rule metadata:
```json
"With_R": {
  "rule": ["...", "..."],
  "context_mode": "duplicate"  // vs "split" for Tensor_R
}
```

### Q4: Should polarity be computed or specified?

Andreoli's focusing derives polarity from connective definitions. We could:
- Compute polarity from rule structure
- Require explicit specification (current approach)
- Use defaults with override capability

**Recommendation**: Specify explicitly for clarity, but could add "auto" option that computes from rules.

---

## Related Work

- [Focusing and Polarization in Linear, Intuitionistic, and Classical Logics](https://www.sciencedirect.com/science/article/pii/S0304397509005301) - Liang & Miller's comprehensive treatment
- [Structural Focalization (Twelf)](https://twelf.org/wiki/focusing/) - How Twelf encodes focusing
- [focusing in nLab](https://ncatlab.org/nlab/show/focusing) - Theoretical overview
- [Celf – A Logical Framework](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28) - Focused linear logic framework

---

## Summary

The current system has an awkward hybrid where focusing spans ll.json (syntax + polarity) and proofstate.js (strategy).

**Recommendation**: Move toward Option C - keep polarity as declarative hints in ll.json, but move focus syntax and strategy entirely to the prover. This gives us:
- Cleaner rule definitions
- Configurable proof search
- Clear separation of concerns
- Path to full genericity if needed

The key insight is that **focusing is a proof search optimization, not part of the logic's essence**. Users care about what's provable, not the search strategy. The prover should own that responsibility.

---

*Last updated: 2026-01-23*
