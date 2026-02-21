---
title: "Linear Logic Connectives: Par, Why Not, and Polarity"
created: 2026-02-10
modified: 2026-02-10
summary: Deep understanding of Par (⅋), Why Not (?), and polarity in linear logic, including resource intuitions, game semantics, and session type interpretations.
tags: [linear-logic, par, why-not, polarity, connectives, semantics]
category: "Proof Theory"
---

# Linear Logic Connectives: Par, Why Not, and Polarity

Understanding the "mysterious" connectives in linear logic that lack obvious resource interpretations.

> **See also:** [[proof-calculi-foundations]] for sequent calculus basics, [[clf-celf-ceptre]] for operational semantics, [[nomos]] for session type perspective.

---

## The Challenge

Linear logic's connectives split into two groups:

**Well-understood (resource intuition works):**
- `A ⊗ B` (tensor) — "I have both A and B simultaneously"
- `A ⊸ B` (lolli) — "consuming A produces B"
- `A & B` (with) — "I can choose A or B, but not both"
- `A ⊕ B` (plus) — "I have either A or B (tagged union)"
- `!A` (bang) — "unlimited copies of A"

**Mysterious (resource intuition unclear):**
- `A ⅋ B` (par) — "???"
- `?A` (why not) — "???"

This document aims to build intuition for the mysterious connectives.

---

## 1. Par (⅋) — Multiplicative Disjunction

### Definition

Par is the De Morgan dual of tensor:
```
A ⅋ B = (A⊥ ⊗ B⊥)⊥
```

**It is NOT "I have A or B" (that's ⊕).**

### The Confusion

Par looks like disjunction but behaves differently:
- `A ⊕ B` is **additive** (one branch chosen, resources split)
- `A ⅋ B` is **multiplicative** (both branches active, resources shared)

### Possible Interpretations

**1. Parallel composition (session types):**
```
A ⅋ B = "A and B running in parallel, sharing resources"
```

In session types (Wadler's classical version):
- Tensor `⊗` = sequential composition
- Par `⅋` = parallel composition

**2. Game semantics:**
```
A ⅋ B = "Opponent chooses the branch, but must handle both"
```

In dialogue games:
- Proponent (P) plays the proof
- Opponent (O) plays the refutation
- Par means O chooses, but P can use resources from both sides

**3. "Failure or success" reading:**
```
A ⅋ B = "Either A fails or B succeeds (or both)"
```

Less intuitive, but matches classical logic duality.

**4. Coherence spaces:**

In Girard's original semantics:
```
|A ⅋ B| = |A| ∪ |B|   (union of webs)
```

This contrasts with:
```
|A ⊗ B| = |A| × |B|   (product of webs)
```

### Why Par Matters

Par is essential for:
1. **Classical linear logic** — CLL is symmetric; par is dual to tensor
2. **Full cut elimination** — Need par for complete proof normalization
3. **Session types** — Par models parallel processes

### For CALC

**Current status:** CALC focuses on intuitionistic linear logic (ILL), which doesn't have par. This is deliberate — we want resource intuition.

**When we might need it:** If modeling parallel execution or concurrent processes.

---

## 2. Why Not (?) — Exponential

### Definition

Why not is the De Morgan dual of bang:
```
?A = (!A⊥)⊥
```

**Structural rules:**
- `?` allows **weakening** on the LEFT (discard)
- `?` allows **contraction** on the LEFT (duplicate)
- (Compare: `!` allows these on the RIGHT)

### The Symmetry

| Modality | On Right | On Left | Interpretation |
|----------|----------|---------|----------------|
| `!A` | Copy, discard | Use linearly | "Unlimited supply" |
| `?A` | Use linearly | Copy, discard | "Sink" / "garbage collector" |

### Possible Interpretations

**1. "Garbage collection":**
```
?A = "I can discard or duplicate demands for A"
```

If `!A` is "unlimited supply", then `?A` is "flexible demand."

**2. Classical control / continuations:**

In proof terms:
- `!A` corresponds to `!` in linear lambda calculus (thunk)
- `?A` corresponds to control operators (like `call/cc`)

**3. Non-deterministic consumption:**
```
?A = "Choose how many A's to consume from the context"
```

### Why We Avoid It

CALC uses intuitionistic linear logic because:
1. **Cleaner resource intuition** — One side of the sequent is the goal
2. **No need for par** — ILL has lolli instead
3. **Better proof search** — More deterministic

---

## 3. Polarity

### The Key Insight

Andreoli discovered that linear logic formulas have **polarity**:

| Polarity | Connectives | Right Rules | Proof Search |
|----------|-------------|-------------|--------------|
| **Positive** | `⊗`, `⊕`, `!`, `1`, `0` | Non-invertible | Focus, choose |
| **Negative** | `⅋`, `&`, `?`, `⊥`, `⊤`, `⊸` | Invertible | Invert eagerly |

### Why Polarity Matters

**1. Proof search efficiency:**
- Negative formulas: apply rules eagerly (no backtracking)
- Positive formulas: choose focus point (may backtrack)

**2. Focusing discipline:**
```
Proof search alternates:
  1. Inversion phase: decompose all negative formulas
  2. Focus phase: choose positive formula, decompose until blur
```

**3. Correspondence to computation:**
- Positive = values (data ready)
- Negative = computations (need evaluation)

### In CALC

CALC's `ll.json` marks polarity explicitly:
```json
{
  "Formula_Tensor": { "polarity": "positive" },
  "Formula_Lolli": { "polarity": "negative" },
  "Formula_Bang": { "polarity": "positive" },
  "Formula_With": { "polarity": "negative" }
}
```

The prover uses this for focusing-based proof search.

---

## 4. The Symmetry Puzzle

### Classical Linear Logic is Symmetric

Every connective has a dual:
```
⊗ ↔ ⅋    (tensor ↔ par)
& ↔ ⊕    (with ↔ plus)
! ↔ ?    (bang ↔ why not)
1 ↔ ⊥    (one ↔ bottom)
⊤ ↔ 0    (top ↔ zero)
```

De Morgan duality: `(A ⊗ B)⊥ = A⊥ ⅋ B⊥`

### Intuitionistic Linear Logic Breaks Symmetry

ILL only has one side of each pair:
- Tensor `⊗` but no par `⅋`
- With `&` and plus `⊕` (both)
- Bang `!` but no why not `?`

**Why?** ILL sequents are:
```
Γ ⊢ A    (single conclusion)
```

Classical LL sequents are:
```
Γ ⊢ Δ    (multiple conclusions)
```

Single conclusion means we can't express par naturally.

### Options for Understanding

1. **Accept asymmetry** — ILL has good resource intuition
2. **Learn game semantics** — Makes duality crystal clear
3. **Study session types** — Par becomes parallel composition

---

## 5. Session Type Perspective

### Propositions as Sessions

Following Caires-Pfenning and Wadler:

| Linear Logic | Session Type |
|--------------|--------------|
| `A ⊗ B` | Send A, then continue as B |
| `A ⅋ B` | Receive A, then continue as B |
| `A ⊸ B` | Receive A, then send B |
| `A & B` | Offer choice between A and B |
| `A ⊕ B` | Make choice between A and B |
| `!A` | Server (replicated process) |
| `?A` | Client (requesting service) |

### Par in Session Types

```
A ⅋ B = "Receive something of type A, then behave as B"
```

This is the **input** side of the communication.

Compare:
```
A ⊗ B = "Send something of type A, then behave as B"
```

This is the **output** side.

**Channel endpoints:**
```
If one end has type A ⊗ B (sends A, then B)
The other end has type A⊥ ⅋ B⊥ (receives A, then B)
```

---

## 6. References

### Essential

- Girard (1987) — "Linear Logic" — Original paper with all connectives
- Andreoli (1992) — "Logic Programming with Focusing Proofs" — Polarity
- Wadler (2012) — "Propositions as Sessions" — Session type interpretation

### Advanced

- Girard — "Proofs and Types" — Philosophical perspective
- Abramsky & Jagadeesan (1994) — "Games and Full Completeness for MLL" — Game semantics
- Mellies (2009) — "Categorical Semantics of Linear Logic" — Coherence spaces

### For Practice

- Caires & Pfenning (2010) — "Session Types as ILL Propositions"
- [[nomos]] — Implementation showing session types in action
- [[clf-celf-ceptre]] — Forward chaining perspective

---

## Summary

| Connective | Resource Intuition | Session Type | Polarity |
|------------|-------------------|--------------|----------|
| `⊗` (tensor) | Both simultaneously | Send then continue | Positive |
| `⅋` (par) | Parallel / receive | Receive then continue | Negative |
| `&` (with) | Choose one | Offer choice | Negative |
| `⊕` (plus) | Tagged union | Make choice | Positive |
| `⊸` (lolli) | Consume to produce | Receive, then send | Negative |
| `!` (bang) | Unlimited supply | Server (replicated) | Positive |
| `?` (why not) | Flexible demand | Client | Negative |

**For CALC:** We stay with ILL (no par, no why not) because:
1. Resource intuition is clear
2. Proof search is more deterministic
3. Session types (if needed) can use the ILL fragment

---

*Last updated: 2026-02-10*
