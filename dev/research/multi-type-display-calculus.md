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

 | Component                   | CALC Implementation                         | LNL Equivalent     |
 | -----------                 | ---------------------                       | ----------------   |
 | `persistent_ctx`            | Set of reusable formulas                    | Cartesian type (C) |
 | `linear_ctx`                | Multiset of linear resources                | Linear type (M)    |
 | `Bang_L` hardcoded handling | Moves `!A` from linear to `A` in persistent | F functor: C → M   |
 | Implicit dereliction        | `persistent_ctx` available in all premises  | G functor: M → C   |

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
    │   ⊣   │
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

| Aspect             | Calculus-Toolbox-2      | CALC                            |
| --------           | -------------------     | ------                          |
| Type specification | Explicit in DSL         | Implicit (persistent vs linear) |
| Bridge rules       | Via type parameters     | Hardcoded Bang_L handling       |
| Generality         | Supports any multi-type | Specialized for LNL             |
| Complexity         | Higher                  | Lower                           |

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

**Generalize multi-type DC to support multimodalities, graded types, and agents.**

### Rationale

1. **LNL is correct and serves as case study**: The current implementation validates that multi-type DC works in practice

2. **Project goals require generalization**: We aim to extend with:
   - Ownership modalities (`[Alice] A`, `[Bob] A`)
   - Multi-signature (`[Alice ∧ Bob] A`)
   - Graded types (semiring quantities)
   - Agent-based reasoning

3. **LNL is just one adjunction**: The pattern generalizes to any adjunction between types

### Current Architecture (LNL case study)

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

### Generalization Path

The key insight: **adjunctions between types** are the general pattern. Modes form a **partial order** (poset), not necessarily a total order — incomparable modes like `alice ⊥ bob` are natural.

**For authorization modalities (our primary goal):**

The goal is to generalize beyond simple ownership to **arbitrary consensus algorithms**:

| Consensus Type | Modality Pattern | Example |
|----------------|------------------|---------|
| Single authority | `[Alice] A` | Alice controls A |
| Multi-signature | `[Alice ∧ Bob] A` | Both must agree |
| k-of-n threshold | `[2-of-{A,B,C}] A` | Any 2 of 3 |
| Weighted voting | `[Alice:0.3, Bob:0.7] A` | Weighted threshold |
| Proof of Work | `[PoW(nonce, difficulty)] A` | Computational proof |
| Proof of Stake | `[Stake(Alice, 100 ETH)] A` | Staked collateral |

```
Types: {linear, alice, bob, shared, staked, ...}
Partial order:
  - shared ≥ alice, shared ≥ bob (consensus dominates individuals)
  - alice ⊥ bob (incomparable — neither controls the other)
  - staked ≥ linear (staked resources have extra structure)

Adjunctions:
  - alice_ctx ←→ linear_ctx (Alice's ownership bridge)
  - bob_ctx ←→ linear_ctx (Bob's ownership bridge)
  - shared_ctx ←→ alice_ctx, bob_ctx (consensus formation)
```

**Key paper to study:** [Garg et al.: A Linear Logic of Authorization and Knowledge (ESORICS 2006)](https://link.springer.com/chapter/10.1007/11863908_19)

This paper combines linear logic with authorization modalities (`A says φ`) for:
- Consumable authorizations (linear affirmations)
- Reusable credentials (exponential affirmations)
- Knowledge modalities for information flow
- Cut elimination for the combined logic

**For graded types:**
```
Types: {0, 1, 2, ..., ω} or semiring R
Adjunctions: grading ↔ linear via semiring operations
```

**Combining both:** The ultimate goal is a framework supporting:
- Multiple agent modes (Alice, Bob, ...)
- Consensus modes (multi-sig, voting, PoW/PoS)
- Graded quantities (semiring-indexed resources)
- All with proper cut elimination

---

## Alternatives for Generalization

Three main approaches exist (see also [[proof-calculi-foundations]], [[QnA]]):

### 1. Multi-Type Display Calculus (MTDC)

**What:** Multiple formula types with bridge connectives and adjunctions.

**Key papers:** Greco & Palmigiano (2023), Frittella et al. (2014), calculus-toolbox-2

**Pros:**
- Automatic cut elimination via Belnap's conditions
- Natural for LNL-style decompositions
- CALC already uses this pattern

**Cons:**
- Requires extending ll.json significantly
- Proof search with display postulates can be expensive

**Implementation sketch:**
```json
"types": {
  "linear": {"structural": []},
  "cartesian": {"structural": ["contraction", "weakening"]},
  "alice": {"structural": ["contraction", "weakening"]}
},
"adjunctions": {
  "bang": {"left": "cartesian", "right": "linear", "counit": "dereliction"},
  "alice_has": {"left": "alice", "right": "linear", "counit": "use"}
}
```

### 2. Labelled Sequent Calculus

**What:** Explicit labels (worlds/modes) and accessibility relations.

**Key papers:** Negri (2005), Poggiolesi (2011)

```
x:A, y:B, xRy ⊢ z:C
```

**Pros:**
- Most general — any Kripke semantics
- Global conditions become local label checks
- Well-understood proof theory

**Cons:**
- Proliferation of labels in complex proofs
- Less "pure" — labels are semantic artifacts
- Harder to extract computational content

**Use case:** When types have complex accessibility relations (e.g., distributed systems, temporal logic).

### 3. Pfenning's Adjoint Logic

**What:** Modes form a partial order (poset), adjunctions as mode-crossing connectives.

**Key papers:** Pfenning (2023 SAX notes), Pruiksma & Pfenning (2020)

```
Modes: {U (unrestricted), L (linear), A (affine), alice, bob, shared, ...}
Partial order examples:
  - U ≥ A ≥ L (substructural hierarchy)
  - shared ≥ alice, shared ≥ bob (ownership lattice)
  - alice ⊥ bob (incomparable — no ordering)
Adjunctions: ↑ᵐ (shift up), ↓ᵐ (shift down)
```

**Pros:**
- Elegant algebraic structure
- Generalizes LNL, affine, relevant in one framework
- Session types connection
- Partial order handles incomparable modes (alice ⊥ bob)

**Cons:**
- Requires poset structure on modes
- Not all multi-type calculi fit this pattern

### Comparison

| Aspect | Multi-Type DC | Labelled | Adjoint Logic |
|--------|---------------|----------|---------------|
| **Expressiveness** | High | Highest | Medium-High |
| **Cut elimination** | Generic (Belnap) | Per-logic | Generic |
| **Proof search** | Display postulates | Label management | Mode-directed |
| **Semantic purity** | High | Lower | High |
| **CALC fit** | Natural extension | Significant change | Good fit |

### Recommendation for CALC

**Start with Multi-Type DC (Option 1):**
- CALC already has the pattern (LNL)
- Extend ll.json to declare types and adjunctions
- Use LNL as validation case study

**Consider Adjoint Logic for modes:**
- If ownership modalities form a preorder (likely!)
- E.g., `admin ≥ user ≥ guest`

**Reserve Labelled for complex scenarios:**
- Distributed systems with arbitrary topology
- When other approaches prove insufficient

---

## Evaluation: Do We Need Systems Beyond MTDC?

Beyond Display/Labelled, there are three more powerful proof systems. Are any relevant for our goals?

### The Extended Hierarchy

```
Standard sequent < Hypersequent < Nested < Display ≈ Labelled < Deep Inference / Cyclic / Proof Nets
```

### Deep Inference

**What:** Rules apply anywhere inside formulas, not just at the root.

**Relevance for us:** LOW

Deep inference provides structural flexibility and symmetry (cut ↔ identity duality), but doesn't add expressiveness we specifically need. The multimodal authorization work (like Garg et al.) uses standard sequent/display approaches.

### Cyclic Proofs

**What:** Non-wellfounded proofs as finite graphs. Essential for fixpoints (μ-calculus) and inductive definitions.

**Relevance for us:** MEDIUM-HIGH (for future phases)

We'd need cyclic proofs if we model:
- Recursive smart contracts
- Transaction histories as inductive structures
- "Valid blockchain state" as least fixpoint
- Temporal properties ("eventually consistent")

**Current phase:** Not needed. Our authorization modalities don't require fixpoints yet.

**Future phase:** Likely needed when modeling stateful contracts.

**Interesting work:** [Looping for Good: Cyclic Proofs for Security Protocols](https://zenodo.org/records/16992323) — uses cyclic proofs in Tamarin Prover for protocol verification.

### Proof Nets

**What:** Geometric/graph representation eliminating proof bureaucracy.

**Relevance for us:** LOW

> "Proof nets are hard for multimodalities."

Proof nets work well for pure linear logic but extending them to modal/multimodal logics is problematic. We need multimodal logics for ownership/authorization — proof nets are not the right tool.

### Summary

| System | Adds | Our Need | Recommendation |
|--------|------|----------|----------------|
| **Deep Inference** | Structural flexibility | Not specific | Skip |
| **Cyclic Proofs** | Fixpoints, induction | Future (contracts) | Keep on radar |
| **Proof Nets** | Proof identity | Multimodal ✗ | Skip |
| **Multi-Type DC** | Type-indexed modalities | Authorization ✓ | **Primary approach** |
| **Labelled Sequents** | Arbitrary accessibility | Backup | If MTDC insufficient |

**Conclusion:** Stick with Multi-Type Display Calculus. Study Garg et al.'s authorization paper as our model for combining linear logic with agent modalities. Consider cyclic proofs later if we need recursive/inductive definitions for smart contracts.

---

## Sources

### Primary References

- [Benton (1995): A Mixed Linear and Non-Linear Logic](https://link.springer.com/chapter/10.1007/BFb0022251) — Original LNL paper
- [Greco & Palmigiano (2023): Linear Logic Properly Displayed](https://dl.acm.org/doi/10.1145/3570919) — State-of-the-art multi-type DC
- [nLab: !-modality](https://ncatlab.org/nlab/show/!-modality) — Comonad structure of bang
- [Garg et al. (2006): A Linear Logic of Authorization and Knowledge](https://link.springer.com/chapter/10.1007/11863908_19) — **Key paper** for combining linear logic with authorization modalities (`A says`), consumable credentials, cut elimination

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
