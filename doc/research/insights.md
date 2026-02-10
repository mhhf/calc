---
title: "Research Insights"
created: 2026-02-10
modified: 2026-02-10
summary: Key discoveries including Pacioli group as grading ring, ownership as fibration not mode, debt as channel, and MPST methodology for authorization.
tags: [insights, novel-contributions, research, pacioli-group, ownership]
---

# Research Insights

Key discoveries from the CALC research program that may be significant contributions.

> **See also:** [[graded-resource-tracking]] for QTT/Granule, [[fibrations-study-plan]] for ownership-as-fibration, [[linear-negation-debt]] for debt semantics, [[consensus-modalities-mpst]] for coherence/consensus, [[adjunctions-and-adjoint-logic]] for mode structure.

---

## Table of Contents

1. [Pacioli Group as Grading Ring](#1-pacioli-group-as-grading-ring--potentially-novel)
2. [Ownership as Fibration, Not Mode](#2-ownership-as-fibration-not-mode)
3. [Debt as Channel](#3-debt-as-channel--unification-of-debt-and-session-types)
4. [MPST Methodology for Authorization](#4-mpst-methodology-for-authorization)
5. [Coherence = Consensus Achievability](#5-coherence--consensus-achievability--compile-time-guarantee)
6. [Closed Questions](#6-closed-questions--what-not-to-pursue)
7. [The Three-Level Structure](#7-the-three-level-structure--big-picture)
8. [Two-Layer Architecture](#8-two-layer-architecture-clarification)

---

## 1. Pacioli Group as Grading Ring — Potentially Novel

**Discovery:** The Pacioli group (T-accounts) relates to MULTIPLICATIVE structure, not additives:

```
[x // y] ≈ x ⊗ y⊥   (tensor with negation)
```

**Insight:** The Pacioli group could BE a grading structure for graded linear logic:

```
□_{[x//y]} A  =  "have x of A, owe y of A"
```

**Significance:**
- T-accounts become NATIVE to the type system
- Not separate asset/liability tracking — one unified graded modality
- 500 years of accounting practice formalized as graded types
- Connects Ellerman's work directly to Granule-style QTT

**Open question:** What is the multiplication operation for Pacioli-graded types?

---

## 2. Ownership as Fibration, Not Mode

**Discovery:** Ownership transfer `[Alice] A ⊸ [Bob] A` is NOT an adjunction-derived operation. It's a morphism in a fibration:

```
Base category: Principals (with speaks-for morphisms?)
Fiber over P: Resources owned by P
Transfer: Reindexing along principal morphisms
```

**Significance:**
- Fibrations ARE dependent types (Lawvere)
- Connects ownership to dependent type theory
- Clean metatheory: fibrations have well-understood properties
- Transfer = reindexing gives compositional semantics

**Key distinction:** `[Alice] A` is not "A at mode Alice" but "A in the fiber over Alice."

---

## 3. Debt as Channel — Unification of Debt and Session Types

**Discovery:** Session types show that a channel c has type A on one end, A⊥ on the other. The channel IS the bilateral relationship.

**For debt:**
```
Alice owns c : debt(BTC, q)
Bob owns c⊥ : debt(BTC, q)⊥   -- i.e., claim(BTC, q)
```

**Unification:**
| Accounting | Session Types |
|------------|---------------|
| Loan creation | Channel creation |
| Debt payment | Message on channel |
| Settlement | Channel close |
| Default | Protocol violation |

**Significance:** A loan isn't just "Alice owes Bob" — it's an ongoing RELATIONSHIP with a protocol. Session types capture this naturally.

---

## 4. MPST Methodology for Authorization

**Discovery:** Strong parallel between MPST and authorization:

```
Global type        ≈  Authorization policy
Projection         ≈  Deriving local permissions
Deadlock freedom   ≈  Consensus achievable
```

**Methodology:**
1. Write global "who can do what" specification
2. Project to each principal's local rules
3. Deadlock freedom theorem ensures consistency
4. Implementation follows local types automatically

**Significance:** Not just theory — a DESIGN METHODOLOGY for CALC.

---

## 5. Coherence = Consensus Achievability — Compile-Time Guarantee

**Discovery:** From MCP: `coherent(T₁,...,Tₙ)` implies deadlock freedom.

**Translation:** If participant types are coherent, consensus is ACHIEVABLE.

**Significance:** TYPE-LEVEL CRITERION for consensus. Check at compile time whether consensus is possible.

---

## 6. Closed Questions — What NOT to Pursue

| Question | Answer | Implication |
|----------|--------|-------------|
| Threshold modalities compact? | NO | Use predicate `threshold(k, ps, φ)` |
| Ownership transfer = adjunction? | NO | Use fibration/reindexing |
| Principals as modes? | NOT DIRECTLY | Keep as orthogonal index |
| n-ary orthogonality in Ludics? | NOT NATIVE | Use MCP coherence |

---

## 7. The Three-Level Structure — Big Picture

**Discovery:** CALC's modalities operate at THREE ORTHOGONAL LEVELS:

1. **Structural** (adjoint modes): Linear vs Cartesian — can you copy/discard?
2. **Epistemic** (principal index): [Alice], [Bob] — WHO controls?
3. **Quantitative** (grades): How much? T-account structure?

These COMBINE MULTIPLICATIVELY:

```
□_{[x//y]}^{L} [Alice] coin(BTC)
   │           │       └── base type
   │           └── principal index (epistemic)
   └── structural mode + grade (Pacioli T-account)
```

**Significance:** This three-level structure might be CALC's distinctive contribution — no existing system combines all three with this specific interpretation.

---

## 8. Two-Layer Architecture Clarification

**Discovery:** Adjoint logic modes and authorization principals are ORTHOGONAL:

- **Layer 1:** Adjoint modes (structural) — U, L, S with ↑/↓
- **Layer 2:** Principal index (epistemic) — [Alice], [Bob], says

**Implication:** Don't force principals INTO modes. They're different:
- Modes control structural properties (copy? discard?)
- Principals control identity (WHO owns/authorizes)

---

*Last updated: 2026-01-29*
