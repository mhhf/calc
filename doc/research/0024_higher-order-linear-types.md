---
title: "Higher-Order Linear Types"
created: 2026-02-05
modified: 2026-02-10
summary: Research on type constructors taking linear types as arguments including second-order linear logic, higher-kinded types, and parametric polymorphism in linear systems.
tags: [higher-order, type-constructors, second-order, polymorphism, linear-logic]
category: "Implementation"
---

# Higher-Order Linear Types

**Date:** 2026-02-05
**Status:** Research Complete
**Priority:** HIGH

**See also:** [[multimodal-linear-logic]] — comprehensive treatment of ownership, location, and graded modalities

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Quick Answer](#quick-answer)
3. [The Three-Level Hierarchy](#1-the-three-level-hierarchy)
4. [Built-in Type Operators](#2-built-in-type-operators)
5. [Approaches to Higher-Kinded Linear Types](#3-approaches-to-higher-kinded-linear-types)
6. [Second-Order Linear Logic](#4-second-order-linear-logic)
7. [What CALC Currently Has](#5-what-calc-currently-has)
8. [Recommendations for CALC](#6-recommendations-for-calc)
9. [Linear Modalities (Interpretation B)](#7-linear-modalities-interpretation-b)
10. [Summary](#8-summary)
11. [References](#references)

---

## Executive Summary

**Question:** Can we have type constructors that take linear types as arguments?

```celf
% Current capability:
foo: bin -> ltype.        % type family indexed by a TERM (bin is cartesian)

% Desired capability:
bar: ltype -> ltype       % type constructor taking a LINEAR TYPE as argument
```

### Two Interpretations

**Interpretation A (Cartesian HKT):** `List : type -> type` — standard higher-kinded types
- This is what System Fω provides
- Not directly supported in CLF/Celf/LF

**Interpretation B (Linear Modalities):** `left : ltype -> ltype` — wrapping linear resources
- Example: `left(pc X)` where `pc X` is a linear resource
- This is about **modalities on linear propositions**
- Much more relevant for CALC's goals!

```celf
% Example use case (EVM with parallel execution):
pc: bin -> type.                    % linear program counter
left: ??? -> type.                  % left branch marker
right: ??? -> type.                 % right branch marker

% Desired:
left(pc X) * right(pc Y) -o merged(...)
```

**This document addresses both interpretations.**

---

## Quick Answer

**For Interpretation A (Cartesian HKT):**
Standard approaches apply — see Section 3.

**For Interpretation B (Linear Modalities):**
This is achievable TODAY via several approaches:

| Approach | Syntax | Complexity |
|----------|--------|------------|
| **Indexed wrapper** | `left: bin -> type` then `left X` pairs with `pc X` | Simple |
| **Product encoding** | `left_pc: bin -> type` as monolithic | Simple |
| **Subexponentials** | `!_left A` with indexed bang | Medium |
| **Modal operators** | `[left] A` as first-class modality | Advanced |

**Recommendation:** Start with indexed wrapper or product encoding.

---

**Answer:** This requires **higher-kinded types** (type operators at the kind level), which CLF/Celf/LF do NOT support by design. However, there are well-understood approaches:

| Approach | Complexity | Expressivity | Recommended |
|----------|------------|--------------|-------------|
| **Encoding via explicit type passing** | LOW | MEDIUM | ✅ Short-term |
| **System F° style (kinded linearity)** | MEDIUM | MEDIUM | Research |
| **Linear System Fω (full HKT)** | HIGH | HIGH | Long-term |
| **Universe polymorphism** | HIGH | VERY HIGH | Overkill |

**Recommendation:** For CALC's accounting goals, use the **encoding approach** (explicit type parameters). Most financial constructs don't require user-defined type operators. Built-in connectives (`!`, `⊗`, `⊸`, `&`) already provide the essential type operators.

---

## 1. The Three-Level Hierarchy

### 1.1 LF/LLF/CLF Structure

Logical frameworks like LF and its linear variant LLF use a **three-level hierarchy**:

```
Level 3: KINDS       — classify type families
         Examples: type, bin -> type, nat -> nat -> type

Level 2: TYPE FAMILIES — classify terms, indexed by terms
         Examples: bin, nat, plus e e e, list nat

Level 1: TERMS/OBJECTS — the values being manipulated
         Examples: e, (i e), z, (s z)
```

**Critical observation:** Type families can be indexed by **terms** (Level 1), but NOT by other type families (Level 2).

### 1.2 What CLF/Celf Supports

In Celf syntax:

```celf
% Simple types (kind: type)
bin: type.
nat: type.

% Type family indexed by terms (kind: bin -> bin -> bin -> type)
plus: bin -> bin -> bin -> type.

% Type family with linear consumption
token: type.                    % linear resource type
counter: nat -> type.           % indexed by nat term
```

**What you CANNOT write in Celf:**

```celf
% INVALID: type -> type is not a valid kind
list: type -> type.

% INVALID: ltype -> ltype
container: ltype -> ltype.
```

### 1.3 Why This Limitation?

The restriction is intentional:

1. **Decidability:** Type-checking with only term-indexed families is decidable
2. **Adequacy:** Bijection between LF terms and object-language derivations
3. **Simplicity:** No need for kind polymorphism or higher-order unification at the kind level
4. **Metatheory:** Cut elimination and other properties are easier to prove

---

## 2. Built-in Type Operators

CALC and linear logic already have **built-in type operators** that take types as arguments:

| Operator | Kind (conceptually) | Meaning |
|----------|---------------------|---------|
| `!A` | `type -> type` | Exponential/unrestricted |
| `A ⊗ B` | `type -> type -> type` | Tensor (simultaneous) |
| `A ⊸ B` | `type -> type -> type` | Linear implication |
| `A & B` | `type -> type -> type` | With (choice) |
| `{A}` | `type -> type` | Lax monad |

These are **primitive** — users cannot define new ones at this level.

**Key insight:** For most applications, the built-in connectives suffice. The question is whether users need to define **custom** type operators.

---

## 3. Approaches to Higher-Kinded Linear Types

### 3.1 Encoding via Explicit Type Passing (Recommended)

Instead of:
```celf
% INVALID
list: type -> type.
nil: list A.
cons: A -> list A -> list A.
```

Use explicit type parameters:
```celf
% VALID - parametric encoding
list: type.
nil: {A: type} list.
cons: {A: type} A -> list -> list.

% Usage requires explicit type argument
mylist = cons nat z (cons nat (s z) (nil nat)).
```

**Pros:**
- Works in current CLF/Celf
- No type system changes needed
- Explicit types aid proof search

**Cons:**
- Verbose syntax
- No type inference for parameters
- Manual consistency checking

**Example for containers:**
```celf
% Instead of: container: ltype -> ltype
container: type.
empty: {A: type} container.
insert: {A: type} A -o container -o container.
extract: {A: type} container -o (A * container).
```

### 3.2 System F° Approach (Kinded Linearity)

[System F°](https://dl.acm.org/doi/10.1145/1708016.1708027) introduces **kinds that track linearity**:

```
Kinds:
  ◦  — linear type (must be used exactly once)
  ⋆  — unrestricted type (can be used freely)

Subkinding:
  ⋆ <: ◦  — unrestricted values can be used linearly

Type formation:
  τ ⊗ υ : ◦  if either τ : ◦ or υ : ◦
  τ ⊗ υ : ⋆  if both τ : ⋆ and υ : ⋆
```

**What F° provides:**
- Types classified by whether they're linear or unrestricted
- Subkinding for flexible use of unrestricted types
- Protocols and state machines via linear types

**What F° does NOT provide:**
- User-defined type operators (`type -> type`)
- This is about CLASSIFYING types, not CONSTRUCTING them

### 3.3 Linear System Fω (Full Higher-Kinded Types)

Combining linearity with Fω gives:

```
Kinds:
  κ ::= ◦ | ⋆ | κ₁ → κ₂

Type operators:
  List : ⋆ → ⋆               % unrestricted list
  LinearList : ◦ → ◦         % linear list (elements used once)
  Mixed : ⋆ → ◦ → ◦          % mixed parameters
```

**Challenges:**
1. **Kind inference:** What kind should `λα. α ⊗ α` have?
2. **Linearity checking:** Must track linearity at the kind level
3. **Unification:** Higher-order unification is undecidable in general
4. **Metatheory:** Cut elimination with HKT is complex

**State of research:** This is an active research area. No production system fully implements "Linear Fω" with good proof search.

### 3.4 Universe Polymorphism (Agda/Idris Style)

In dependently typed languages:

```agda
-- Agda style
List : (A : Set) → Set
List A = ...

-- With universe levels
List : {ℓ : Level} → Set ℓ → Set ℓ
```

**Why this is overkill for CALC:**
- Full dependent types are heavyweight
- Universe management is complex
- Proof search becomes undecidable
- Not needed for accounting applications

---

## 4. Second-Order Linear Logic

Girard's original linear logic includes **second-order quantification**:

```
∀X. A    — universal quantification over formulas
∃X. A    — existential quantification over formulas
```

### 4.1 Second-Order Universal (∀)

```
∀X. (X ⊸ X)     — polymorphic identity
∀X. (!X ⊸ X)    — dereliction schema
```

**Proof rules:**
```
Γ ⊢ A[B/X]
─────────────── ∀R (B not free in Γ)
Γ ⊢ ∀X. A

Γ ⊢ ∀X. A
─────────────── ∀L
Γ ⊢ A[B/X]
```

### 4.2 Relationship to Type Operators

Second-order quantification is related but distinct from type operators:

| Feature | Second-Order ∀ | Type Operators |
|---------|---------------|----------------|
| Level | Formula/proposition | Type/kind |
| Binding | Bound variable X | Lambda over types |
| Instantiation | Substitution A[B/X] | Application (λα.τ) σ |
| Use case | Polymorphic formulas | Type constructors |

**Second-order ∀ in linear logic:**
- IS well-studied (Girard 1987)
- Has categorical semantics
- Can express polymorphism

**Type operators:**
- Require extending the KIND system
- Less studied in linear setting
- Need careful treatment of linearity

---

## 5. What CALC Currently Has

### 5.1 MDE/Celf Layer

```celf
% Types (kind: type)
bin: type.
token: type.

% Type families (kind: T₁ -> ... -> Tₙ -> type)
plus: bin -> bin -> bin -> type.
owns: principal -> quantity -> commodity -> type.

% Terms
e: bin.
alice: principal.
```

### 5.2 Built-in Connectives

The ILL fragment provides:
- `A ⊗ B` — tensor
- `A ⊸ B` — linear implication
- `A & B` — with (additive conjunction)
- `!A` — bang (exponential)
- `1` — unit

These ARE type operators but are **primitive**, not user-definable.

### 5.3 The Gap

**What users might want:**
```celf
% A "list" of linearly-owned items
linear_list: type -> type.
lnil: {A: type} linear_list A.
lcons: {A: type} A -o linear_list A -o linear_list A.

% A "maybe" for optional linear resources
linear_maybe: type -> type.
nothing: {A: type} linear_maybe A.
just: {A: type} A -o linear_maybe A.
```

**Current workaround:**
```celf
% Monomorphic approach - define for each type
list_token: type.
lnil_token: list_token.
lcons_token: token -o list_token -o list_token.

% Or parametric encoding with explicit type passing
list: type.
lnil: {A: type} list.
lcons: {A: type} A -o list -o list.
```

---

## 6. Recommendations for CALC

### 6.1 Short-Term: Use Encoding

For immediate needs, use the parametric encoding:

```celf
% Define a generic linear container
container: type.
empty: {A: type} container.
put: {A: type} A -o container -o container.
get: {A: type} container -o {A * container}.

% Usage
my_tokens: container = put token t1 (put token t2 (empty token)).
```

**Advantages:**
- Works today
- No type system changes
- Explicit types help proof search
- Adequate for accounting use cases

### 6.2 Medium-Term: Consider F°-Style Kinds

If linear vs. unrestricted distinction becomes important:

```
% Kinds
◦     — linear type
⋆     — unrestricted type

% Example
token: ◦           — linear (consumed on use)
principal: ⋆       — unrestricted (can be copied)
```

This helps **classify** types but doesn't add user-defined type operators.

### 6.3 Long-Term: Research Direction

If true higher-kinded linear types become necessary:

1. Study [Linear Haskell](https://arxiv.org/abs/1710.09756) approach (multiplicity on arrows)
2. Study [System F°](https://dl.acm.org/doi/10.1145/1708016.1708027) for kinded linearity
3. Consider limited form of type operators (not full Fω)
4. Investigate categorical semantics for Linear Fω

### 6.4 Practical Assessment

**Do accounting applications need HKT?**

Most likely **NO**. Common patterns:

| Pattern | Without HKT | With HKT |
|---------|-------------|----------|
| Portfolio of assets | `asset: commodity -> quantity -> type` | `portfolio: type -> type` |
| Multi-party transaction | `transfer: principal -> principal -> asset -> type` | N/A |
| Conditional claim | `option: asset -> type` | N/A |
| Debt relationship | `debt: principal -> principal -> asset -> type` | N/A |

The first-order type families with term indices handle these cases well.

---

## 7. Linear Modalities (Interpretation B)

This section addresses the specific question: can we have `left(pc X)` where `left` is a linear wrapper around the linear resource `pc X`?

### 7.1 The Use Case

In parallel EVM execution or branching scenarios:

```celf
% We have a linear program counter
pc: bin -> type.

% We want to track which "branch" owns it
% Desired syntax:
left(pc X) * right(pc Y) -o merged(pc X, pc Y)
```

### 7.2 Approach 1: Indexed Wrapper (Recommended)

The simplest approach — use a separate linear type with the same index:

```celf
% Define branch markers as separate indexed types
left_pc: bin -> type.
right_pc: bin -> type.

% Rules transform between them
split_pc: pc X -o { left_pc X * right_pc X }.
merge_pc: left_pc X * right_pc X -o { pc X }.
```

**Pros:**
- Works today in Celf/MDE
- Clear semantics
- Efficient (no extra indirection)

**Cons:**
- Must define `left_X` for each linear type X you want to wrap
- No abstraction over the wrapped type

### 7.3 Approach 2: Pair Encoding

Encode the "branch" as data paired with the resource:

```celf
% Branch tag
branch: type.
left_b: branch.
right_b: branch.

% Tagged resource (consumes the underlying resource)
tagged_pc: branch -> bin -> type.

% Wrapping/unwrapping
tag_pc: {B: branch} pc X -o { tagged_pc B X }.
untag_pc: tagged_pc B X -o { pc X }.
```

**Pros:**
- Single definition works for the tagging pattern
- Branch is a value, can be computed

**Cons:**
- Still need separate `tagged_X` for each type X

### 7.4 Approach 3: Subexponentials

Subexponential linear logic has **indexed modalities** `!_a A`:

```
!_left A    — resource A in the "left" subexponential
!_right A   — resource A in the "right" subexponential
```

Subexponentials have a **preorder** structure determining when resources can move between indices.

**In Celf-like syntax (hypothetical):**
```celf
% Subexponential declarations
subexp left.
subexp right.
subexp merged <= left, right.  % merged can absorb both

% Usage
!_left (pc X) * !_right (pc Y) -o { !_merged (pc X) * !_merged (pc Y) }
```

**Pros:**
- First-class notion of "location" or "ownership"
- Well-studied proof theory
- Works for ANY linear type

**Cons:**
- Not standard Celf — requires extension
- Adds complexity to proof search

### 7.5 Approach 4: Modal Operators as First-Class

Extend the logic with modal operators that can be applied to any proposition:

```celf
% Modal operator declaration (hypothetical syntax)
mode left: ltype -> ltype.
mode right: ltype -> ltype.

% Usage
left (pc X) * right (pc Y) -o merged (pc X, pc Y)
```

This is essentially **adding new connectives** to the logic.

**Pros:**
- Most expressive
- `left` becomes a true type operator

**Cons:**
- Requires extending the core logic
- Proof search must understand the new modality
- Need to define introduction/elimination rules

### 7.6 What CALC Could Do

**Short-term (today):**
Use Approach 1 (indexed wrappers) or Approach 2 (pair encoding).

```celf
% For EVM branching:
left_pc: bin -> type.
right_pc: bin -> type.
left_stack: nat -> bin -> type.
right_stack: nat -> bin -> type.
% ... etc for each linear resource type
```

**Medium-term:**
Add a code generation step that auto-generates wrapped types:

```celf
% In .calc file:
pc: bin -> type
  @linear
  @branchable.   % generates left_pc, right_pc automatically

% Auto-generated:
% left_pc: bin -> type.
% right_pc: bin -> type.
% split_pc: pc X -o { left_pc X * right_pc X }.
% merge_pc: left_pc X * right_pc X -o { pc X }.
```

**Long-term:**
Implement subexponentials or first-class modalities in the logic itself.

### 7.7 Related: Ownership Modalities

This connects to our ownership research:

```celf
% Ownership as indexed modality
owns: principal -> ltype -> ltype.

% Alice owns a token
owns alice (token X)

% Transfer
owns alice (token X) -o { owns bob (token X) }
```

The `owns` operator is exactly an `ltype -> ltype` function!

**See:** dev/research/ownership-as-session-types.md

---

## 8. Summary

### The Question
Can we have `bar: ltype -> ltype` (type constructors over linear types)?

### Two Interpretations

**A. Cartesian HKT** (`List: type -> type`):
- Not directly in CLF/Celf/LF
- Use encoding with explicit type parameters
- Not critical for CALC's goals

**B. Linear Modalities** (`left: ltype -> ltype`):
- THIS is what's needed for EVM branching, ownership, etc.
- Achievable TODAY via indexed wrappers or pair encoding
- Long-term: subexponentials or first-class modalities

### Practical Recommendation

**For your EVM use case:**

```celf
% Define indexed wrappers for each linear resource:
left_pc: bin -> type.
right_pc: bin -> type.
left_stack: nat -> bin -> type.
right_stack: nat -> bin -> type.

% Split/merge rules:
split_pc: pc X -o { left_pc X * right_pc X }.
merge_pc: left_pc X * right_pc X -o { pc X }.
```

**Future enhancement:**
Add `@branchable` annotation that auto-generates these wrappers.

### The Deeper Question

The underlying question is: **should modalities be first-class in CALC?**

- Ownership: `[Alice] A`
- Location: `[left] A`
- Time: `[t] A`
- Consensus: `[2-of-3] A`

These are all `ltype -> ltype` operators. A unified treatment would be powerful.

**See:**
- dev/research/authorization-logic.md
- dev/research/ownership-as-session-types.md
- dev/research/consensus-modalities-mpst.md

---

## References

### Core Papers

- [A Linear Logical Framework](https://www.sciencedirect.com/science/article/pii/S0890540101929517) - Cervesato & Pfenning, 1996
- [Lightweight Linear Types in System F°](https://dl.acm.org/doi/10.1145/1708016.1708027) - Mazurak et al., TLDI 2010
- [Linear Haskell](https://arxiv.org/abs/1710.09756) - Bernardy et al., POPL 2018
- [Linear Logic: Its Syntax and Semantics](https://girard.perso.math.cnrs.fr/Synsem.pdf) - Girard, 1995

### Background

- [LF in nLab](https://ncatlab.org/nlab/show/LF) - Overview of logical frameworks
- [Linear Type Theory in nLab](https://ncatlab.org/nlab/show/linear+type+theory) - Categorical semantics
- [System F](https://en.wikipedia.org/wiki/System_F) - Polymorphic lambda calculus
- [Twelf Type Families](https://twelf.org/wiki/type-family/) - LF type family documentation
- [Celf](https://clf.github.io/celf/) - CLF implementation

### Related CALC Research

- dev/research/clf-celf-ceptre.md — CLF/Celf/Ceptre overview
- dev/research/QTT.md — Quantitative type theory
- dev/research/typed-dsl-logical-framework.md — DSL design

---

*Last updated: 2026-02-05*
