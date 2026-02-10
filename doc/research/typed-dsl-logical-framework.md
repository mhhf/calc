---
title: "Typed DSL / Logical Framework for CALC"
created: 2026-02-10
modified: 2026-02-10
summary: Design of typed DSL for CALC using logical framework approach with three-file architecture inspired by Celf, Twelf, and Lean for type-safe rule definitions.
tags: [DSL, logical-framework, LF, CLF, Celf]
---

# Typed DSL / Logical Framework for CALC

Research on logical frameworks (LF, CLF, Twelf, Celf) and their influence on CALC's DSL design.

> **See also:** [[clf-celf-ceptre]] for CLF/Celf/Ceptre details, [[DSL-approaches]] for DSL comparison, [[ffi-logics]] for oracle integration, [[higher-order-linear-types]] for type-level features.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Logical Frameworks: LF, CLF, Twelf, Celf](#logical-frameworks)
3. [The optimism-mde DSL](#the-optimism-mde-dsl)
4. [Design Decisions](#design-decisions)
5. [References](#references)

---

## Executive Summary

**Goal:** Design a typed DSL where inference rules are well-typed terms, catching malformed rules at definition time.

**Key Decision:** Extended Celf syntax with three-file architecture:

| File Type | Purpose | Style Inspiration |
|-----------|---------|-------------------|
| `.calc` | Types, connectives, metadata | Lean 4 / Twelf |
| `.rules` | Inference rules | calculus-toolbox-2 (horizontal lines) |
| `.mde` | Stdlib and programs | Celf / optimism-mde |

**Implementation Status:** See `dev/dsl_refactor.md` for current progress.

---

## Logical Frameworks

### LF (Edinburgh Logical Framework)

LF is a dependently typed lambda calculus for representing deductive systems.

**Core idea:** Judgments as types, derivations as terms.

**Twelf syntax example (STLC encoding):**

```twelf
% Types
tp : type.
arrow : tp -> tp -> tp.
unit : tp.

% Terms
tm : type.
app : tm -> tm -> tm.
lam : tp -> (tm -> tm) -> tm.    % Higher-order abstract syntax

% Typing judgment
of : tm -> tp -> type.           % Judgment declaration

of-lam : of (lam T2 ([x] E x)) (arrow T2 T)
        <- ({x: tm} of x T2 -> of (E x) T).

of-app : of (app E1 E2) T
        <- of E1 (arrow T2 T)
        <- of E2 T2.
```

**Key features:**
- **Dependent types**: `of : tm -> tp -> type` — typing is a type family
- **HOAS**: `(tm -> tm)` represents binding without explicit substitution
- **Adequacy**: Bijection between LF terms and object-language derivations

**Relevance to CALC:**
- Our sequent rules could be typed: `Tensor_L : rule (Γ, A ⊗ B ⊢ C) [(Γ, A, B ⊢ C)]`
- Dependent types ensure conclusion/premise formulas match
- HOAS could represent formula schemas with free variables

### CLF (Concurrent Linear Framework)

CLF extends LF with:
1. **Linear types** — Resources used exactly once
2. **Monadic encapsulation** — `{A}` for concurrent/stateful computation

**Celf syntax:**

```celf
% Type declaration
state : type.

% Linear resources
counter : nat -> type.          % Linear by default

% Persistent facts
!rule : ...                     % ! makes it persistent

% Linear rewrite rule
inc : counter N * trigger -o { counter (s N) }.

% Backward chaining (non-linear)
plus : nat -> nat -> nat -> type.
plus/z : plus z N N.
plus/s : plus (s M) N (s R) <- plus M N R.
```

**Key syntax elements:**
- `A -> B` — Intuitionistic function (persistent)
- `A -o B` — Linear implication (resource-consuming)
- `A * B` — Simultaneous conjunction (tensor ⊗)
- `{A}` — Monadic suspension (forward-chaining)
- `!A` — Persistent/unrestricted resource
- `<-` — Backward-chaining premise

### The optimism-mde DSL

Our local `~/src/optimism-mde/` uses Celf-style syntax to model EVM:

```celf
% lib/bin.mde - Binary numbers
bin: type.
e: bin.                         % Zero
i: bin -> bin.                  % Bit 1
o: bin -> bin.                  % Bit 0

% Arithmetic relations
plus: bin -> bin -> bin -> type.
plus/z1: plus e e e.
plus/s1: plus (o M) (o N) (o R)
  <- plus M N R.

% lib/evm.mde - EVM instructions
pc: bin -> type.                % Program counter (linear)
stack: nat -> bin -> type.      % Stack slot (linear)
code: bin -> bin -> type.       % Code at address (persistent via context)

% EVM ADD instruction
evm/add:
  pc PC *
  code PC N_01 *
  !inc PC PC' *                 % Persistent increment relation
  sh (s (s SH)) *               % Stack height
  stack (s SH) A *              % Pop A
  stack SH B *                  % Pop B
  !plus A B C                   % Compute A + B
  -o {
    code PC N_01 *
    pc PC' *
    sh (s SH) *
    stack SH C                  % Push result
  }.
```

**Pattern analysis:**
1. **Type declarations** — Simple: `name: type.`
2. **Constructors** — `name: arg -> ... -> return_type.`
3. **Relations/Judgments** — `name: arg1 -> arg2 -> type.`
4. **Clauses** — `name/case: head <- premises.` (backward) or `antecedent -o { consequent }.` (forward)

---

## Design Decisions

### Why Extended Celf?

1. **Familiar syntax** — Already proven in optimism-mde
2. **HOAS for binders** — `(formula -> formula)` handles binding elegantly
3. **Backward compatible** — Pure Celf works, annotations are optional
4. **Clean extension** — `@annotations` don't clash with Celf syntax
5. **Proven at scale** — EVM model works with this approach

### Three-File Architecture

| File | Syntax | Extensions | Purpose |
|------|--------|------------|---------|
| `.calc` | Extended Celf | `@annotations` | Connectives + metadata |
| `.rules` | Celf or Horizontal | `@annotations` | Inference rules |
| `.mde` | **Pure Celf** | None | Stdlib and programs |

**Key insight**: Only the calculus definition (`.calc`) needs extensions. Everything else is pure Celf.

### Annotation Catalog

| Annotation | Purpose | Example |
|------------|---------|---------|
| `@ascii "..."` | Parser syntax pattern | `"_ * _"` |
| `@latex "..."` | LaTeX output | `"#1 \\otimes #2"` |
| `@prec N [assoc]` | Precedence + associativity | `60 left` |
| `@polarity P` | Positive or negative | `positive` |
| `@category C` | Logical category | `multiplicative` |
| `@dual NAME` | Dual connective | `par` |
| `@role R` | Infrastructure role | `judgment`, `context_concat` |
| `@ffi path` | FFI function | `arithmetic.plus` |
| `@mode ...` | FFI mode | `+ + -` |

### Parser Choice

**Decision:** tree-sitter

| Option | Why Chosen/Rejected |
|--------|---------------------|
| Jison | Rejected — unmaintained, poor errors |
| Ohm | Rejected — stack overflow on deep nesting |
| Chevrotain | Rejected — same stack issues |
| **tree-sitter** | Chosen — handles 1000+ nesting, Zig bindings, WASM |

---

## Implementation

For implementation details, see:

- `dev/dsl_refactor.md` — DSL implementation progress (Phase 1-3 complete)
- `dev/FFI-IMPLEMENTATION-PLAN.md` — FFI implementation (complete)
- `dev/import-mechanism.md` — @import system design
- `dev/syntactic-sugar.md` — @literal and @sugar annotations
- `dev/lazy-primitive-storage.md` — Primitive type storage

---

## References

### Logical Frameworks

- Harper, Honsell, Plotkin, "[A Framework for Defining Logics](https://www.cs.cmu.edu/~rwh/papers/lfp/jacm.pdf)" (LF)
- Watkins et al., "[A Concurrent Logical Framework](https://www.cs.cmu.edu/~fp/papers/tr02-cl1.pdf)" (CLF)
- [Twelf Wiki](https://twelf.org/wiki/)
- [Celf GitHub](https://clf.github.io/celf/)
- [Celf Syntax Wiki](https://github.com/clf/celf/wiki/Syntax)

### Celf Syntax Elements

From the Celf documentation:
- `A -> B` — Intuitionistic function (persistent)
- `A -o B` — Linear implication (resource-consuming)
- `A * B` — Simultaneous conjunction (tensor ⊗)
- `{A}` — Monadic suspension (forward-chaining)
- `!N` — Use only persistent variables
- `@N` — Use only affine variables
- `<-` — Backward-chaining premise

### Parser Frameworks

- [tree-sitter](https://tree-sitter.github.io/) — Incremental parsing with Zig bindings
- [Ohm.js](https://ohmjs.org/) — PEG parser with visualization
- [Chevrotain](https://chevrotain.io/) — Fast JS parser toolkit

### Calculus Toolbox

- [calculus-toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2)
- [Documentation: Calculi](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculi.html)

### Local Resources

- `~/src/optimism-mde/` — EVM modeled in Celf syntax
- `calculus/linear-logic.calc` — ILL connective definitions
- `calculus/linear-logic.rules` — ILL inference rules

---

*Last updated: 2026-02-10*
