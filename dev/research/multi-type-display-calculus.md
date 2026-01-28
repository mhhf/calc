# Multi-Type Display Calculus in CALC

Deep research on how CALC implements multi-type display calculus and whether special rules can be generalized.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [CALC's Current Implementation](#calcs-current-implementation)
3. [Benton's LNL Model](#bentons-lnl-model)
4. [The F and G Functors](#the-f-and-g-functors)
5. [Multi-Type Display Calculus Theory](#multi-type-display-calculus-theory)
6. [Calculus-Toolbox-2 Approach](#calculus-toolbox-2-approach)
7. [Analysis: Can Special Rules Be Generalized?](#analysis-can-special-rules-be-generalized)
8. [Recommendation](#recommendation)
9. [Sources](#sources)

---

## Executive Summary

**Key Finding:** CALC already implements multi-type display calculus via Benton's LNL (Linear/Non-Linear) model.

| Component | CALC Implementation | LNL Equivalent |
|-----------|---------------------|----------------|
| `persistent_ctx` | Set of reusable formulas | Cartesian type (C) |
| `linear_ctx` | Multiset of linear resources | Linear type (M) |
| `Bang_L` hardcoded handling | Moves `!A` from linear to `A` in persistent | F functor: C → M |
| Implicit dereliction | `persistent_ctx` available in all premises | G functor: M → C |

**Conclusion:** The "special rules" (Bang_L) ARE the multi-type bridge rules. They are not a hack—they're the correct implementation of the F ⊣ G adjunction.

---

## CALC's Current Implementation

### Sequent Structure (lib/sequent.js:31-45)

```javascript
class Sequent {
  constructor(params) {
    this.persistent_ctx = params?.persistent_ctx || {};  // Cartesian type
    this.linear_ctx = params?.linear_ctx || {};          // Linear type
    this.succedent = params?.succedent || {};
  }
}
```

- **persistent_ctx**: A **set** mapping IDs to formulas. Formulas here can be used any number of times (contraction, weakening).
- **linear_ctx**: A **multiset** mapping IDs to `{num, val}`. Tracks exact resource counts.

This IS Benton's LNL structure: two types (Cartesian and Linear) existing side-by-side.

### Bang_L Special Handling (lib/prover.js:308-316)

```javascript
// Special case: Bang_L promotes to persistent context
if (ruleName === "Bang_L") {
  rule.forEach((seq, i) => {
    if (i === 0) return;
    const r = pt.conclusion.linear_ctx[position].val.copy();
    r.vals[1] = r.vals[1].vals[0];  // Unwrap: !A → A
    seq.persistent_ctx[position] = r;  // Move to Cartesian type
  });
}
```

This is the **F functor** (bridge from Linear to Cartesian):
- Takes `!A` from `linear_ctx` (Linear type)
- Extracts inner formula `A`
- Places `A` in `persistent_ctx` (Cartesian type)

### Persistent Context Propagation (lib/prover.js:269-275)

```javascript
// Copy rule and propagate persistent context
rule = rule.map(seq => {
  Object.keys(pt.conclusion.persistent_ctx).forEach(id => {
    seq.persistent_ctx[id] = pt.conclusion.persistent_ctx[id].copy();
  });
  return seq;
});
```

This is the **G functor** (implicit dereliction):
- Everything in `persistent_ctx` is automatically available in all premises
- This corresponds to "dereliction" in linear logic: `!A ⊢ A`

### The ll.json Rules

```json
"Bang_R" : [
  "I |- -- : ! F?A",
  "I |- -- : F?A"
],
"Bang_L" : [
  "?X, -- : ! F?A |- -- : F?B",
  "?X |- -- : F?B"
]
```

- **Bang_R**: Empty linear context (`I`) to prove `!A` — this is the promotion rule
- **Bang_L**: Remove `!A` from linear context — the rule itself doesn't mention persistent context (that's handled specially)

---

## Benton's LNL Model

### The Core Idea

Benton (1994) showed the exponential `!` decomposes into an adjunction:

```
         F
    C ─────→ M
    ↑       ↑
    │  ⊣   │
    │       │
    └───────┘
         G
```

Where:
- **C**: Cartesian closed category (intuitionistic logic)
- **M**: Symmetric monoidal closed category (linear logic)
- **F ⊣ G**: Adjunction between them

### The Adjunction Law

```
F(X) ⊢_Linear Y   iff   X ⊢_Cartesian G(Y)
```

This bidirectional equivalence IS a display postulate—but across types, not within a single type.

### Decomposition of Bang

```
!A = F(G(A))
```

- G(A): Extract the "reusable content" from A (move to Cartesian world)
- F(G(A)): Embed back into Linear world as unlimited resource

### Key Properties

From [A Simplification to LNL Models](https://blog.hde.design/published/2020-04-02-A-Simplification-to-LNL-Models.html):

- **F is strong monoidal**: `F(⊤) = I` and `F(X × Y) = F(X) ⊗ F(Y)`
- **! forms a comonad**: With counit (dereliction) and comultiplication (contraction)
- **The Kleisli category of !** is cartesian (but not always)

---

## The F and G Functors

### F: Cartesian → Linear (Embedding)

Operationally in CALC, F embeds Cartesian formulas into Linear context:

```
Γ ⊢_Cart A
─────────── F
F(Γ) ⊢_Lin F(A)
```

In CALC: When we apply Bang_L, we're using F to move a formula from the Cartesian world (where it was promoted to) back into the Linear world for use.

### G: Linear → Cartesian (Extraction)

Operationally, G extracts the reusable part:

```
Γ ⊢_Lin A
─────────── G
G(Γ) ⊢_Cart G(A)
```

In CALC: The `persistent_ctx` propagation IS the G functor—it makes formulas available in the Cartesian manner (copyable, droppable).

### The Bridge Rules in Standard Notation

| Rule | Standard | CALC Equivalent |
|------|----------|-----------------|
| Promotion | `!Γ ⊢ A` / `!Γ ⊢ !A` | Bang_R with empty linear_ctx |
| Dereliction | `!A ⊢ A` | Implicit via persistent_ctx propagation |
| Contraction | `!A ⊢ !A ⊗ !A` | persistent_ctx is a set (no counting) |
| Weakening | `Γ, !A ⊢ Δ` / `Γ ⊢ Δ` | persistent_ctx not required to be used |

---

## Multi-Type Display Calculus Theory

### Greco & Palmigiano's Approach

[Linear Logic Properly Displayed (2023)](https://dl.acm.org/doi/10.1145/3570919) introduces **proper** multi-type display calculi:

- Multiple types of formulas/structures
- Bridge connectives between types
- Properness: closure under uniform substitution
- Automatic cut elimination via Belnap's metatheorem

### Why Multi-Type Solves Exponentials

From our existing research ([exponential-display-problem.md](./exponential-display-problem.md)):

1. Single-type display postulate for `!` would require `!A ⊢ B iff A ⊢ f(B)`
2. No such `f` exists (proof by contradiction via contraction)
3. Solution: F and G operate **between** types, not within a single type
4. The adjunction F ⊣ G provides the bidirectionality needed

### Type-Uniform Sequents

In multi-type display calculus, sequents must be **type-uniform**: antecedent and succedent have the same type.

CALC handles this implicitly:
- Sequents operate in Linear type (linear_ctx, succedent)
- persistent_ctx is "background" Cartesian type
- Bridge rules (Bang_L) cross the type boundary

---

## Calculus-Toolbox-2 Approach

### DSL Specification

[Calculus-Toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2) uses a DSL for multi-type calculi:

```
default type atprop
type agent

box : formula{agent} -> formula{atprop} -> formula
  ("[_]_", NonAssoc, 4, "\Box_{#1} #2")
```

### Key Design Choices

1. **Type parameters**: Connectives specify types via `formula{type}`
2. **Homogeneity requirement**: Connectives must have uniform types within rules
3. **Runtime loading**: Calculi can be modified at runtime
4. **Bridge connectives**: Cross-type via explicit type parameters

### Comparison with CALC

| Aspect | Calculus-Toolbox-2 | CALC |
|--------|-------------------|------|
| Type specification | Explicit in DSL | Implicit (persistent vs linear) |
| Bridge rules | Via type parameters | Hardcoded Bang_L handling |
| Generality | Supports any multi-type | Specialized for LNL |
| Complexity | Higher | Lower |

---

## Analysis: Can Special Rules Be Generalized?

### Option 1: Specify Bridge Rules in ll.json

Add metadata to indicate bridge behavior:

```json
"RuleU": {
  "Bang_L": {
    "ascii": "!_L",
    "bridge": {
      "from_type": "linear",
      "to_type": "persistent",
      "unwrap_formula": "Formula_Bang"
    }
  }
}
```

**Pros:**
- More declarative
- Supports future multi-type calculi

**Cons:**
- Added complexity
- Need to extend parser/interpreter
- No clear use case yet

### Option 2: Generic Multi-Type Framework

Define types explicitly:

```json
"types": {
  "linear": {"structural_rules": []},
  "persistent": {"structural_rules": ["contraction", "weakening"]}
},
"contexts": {
  "linear_ctx": {"type": "linear", "structure": "multiset"},
  "persistent_ctx": {"type": "persistent", "structure": "set"}
},
"bridge_rules": {
  "Bang_L": {
    "consumes": {"type": "linear", "pattern": "!A"},
    "produces": {"type": "persistent", "pattern": "A"}
  }
}
```

**Pros:**
- Fully generic
- Matches academic multi-type DC

**Cons:**
- Significant refactoring
- Overkill for current needs
- Introduces abstraction before necessity

### Option 3: Keep It Simple (YAGNI)

Keep the current implementation:
- `persistent_ctx` + `linear_ctx` hardcoded
- `Bang_L` special handling in prover.js

**Pros:**
- Working now
- Simple to understand
- Matches our actual use case (ILL)

**Cons:**
- Requires code changes for new calculi
- "Special case" feels hacky (but isn't)

---

## Recommendation

**Keep the current implementation (Option 3) for now.**

### Rationale

1. **We already have multi-type DC**: The `persistent_ctx` / `linear_ctx` split IS Benton's LNL

2. **Bang_L is correct, not a hack**: The special handling implements exactly what the F functor should do

3. **YAGNI applies**: Until we need a second calculus with different multi-type structure, generalization adds complexity without benefit

4. **Even mature tools hardcode**: Calculus-Toolbox-2 has type-specific handling built into the system

### When to Generalize

Consider generalization if:
- We add a second calculus with different exponential structure
- We want to support user-defined bridge rules
- We're building a calculus editor/generator

### What We Learned

The "special rules" investigation revealed that CALC's design is **correct and well-founded**:

```
┌─────────────────────────────────────────────────────────────┐
│                     CALC Architecture                        │
├─────────────────────────────────────────────────────────────┤
│  persistent_ctx (Cartesian)  ←──── Bang_L ────  linear_ctx  │
│         ↓                         (F functor)       ↓       │
│   Set structure               Multiset structure            │
│   Contraction OK              No contraction                │
│   Weakening OK                No weakening                  │
│         ↓                                          ↓        │
│   Available everywhere         Used exactly as specified    │
│   (implicit G functor)                                      │
└─────────────────────────────────────────────────────────────┘
```

---

## Sources

### Primary References

- [Benton (1995): A Mixed Linear and Non-Linear Logic](https://link.springer.com/chapter/10.1007/BFb0022251) — Original LNL paper
- [Greco & Palmigiano (2023): Linear Logic Properly Displayed](https://dl.acm.org/doi/10.1145/3570919) — State-of-the-art multi-type DC
- [nLab: !-modality](https://ncatlab.org/nlab/show/!-modality) — Comonad structure of bang

### Supporting Materials

- [A Simplification to LNL Models](https://blog.hde.design/published/2020-04-02-A-Simplification-to-LNL-Models.html) — Simplified LNL definition
- [Calculus-Toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2) — Multi-type DC implementation
- [Pfenning: Adjoint SAX Lecture Notes](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/15-adjsax.pdf) — Adjoint logic generalization
- [Frittella et al.: Multi-type display calculus for PDL](https://www.academia.edu/35092418/Multi_type_display_calculus_for_Propositional_Dynamic_Logic) — Multi-type for dynamic logic

### Cross-References

See also in this knowledge base:
- [[exponential-display-problem]] — Why ! lacks residuals
- [[residuation]] — Foundation for display postulates
- [[logics-overview]] — Which logics can be displayed
- [[ANKI]] — Flashcards including LNL

---

*Last updated: 2026-01-28*
