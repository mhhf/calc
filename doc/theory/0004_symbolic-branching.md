---
title: "Symbolic Branching in ILL Forward Chaining"
created: 2026-02-17
modified: 2026-02-21
summary: "Analysis of how to handle conditional branches on symbolic values in ILL. ⊕ (internal choice) is the theoretically correct object-level solution."
tags: [symbolic-execution, branching, oplus, with, case-analysis, path-conditions, forward-chaining]
category: "Forward Chaining"
unique_contribution: "Identifies additive disjunction (⊕) as the correct connective for system-decided branching in forward chaining, distinct from & (external choice). No existing system (CLF, Celf, Ceptre) uses ⊕ in forward consequents."
---

# Symbolic Branching in ILL Forward Chaining

## The Problem

At JUMPI with symbolic condition C (e.g. `gt(32, ?S)`):

```
jumpi_neq: ... stack SH C * !neq C 0 -o { pc NPC }.    % guard: FFI neq
jumpi_eq:  ... stack SH 0             -o { pc PC' }.    % guard: pattern match
```

**Ground C:** exactly one rule fires (FFI decides or pattern matches). No problem.
**Symbolic C:** neither fires. `neq(gt(32,?S), 0)` fails (FFI can't evaluate), `gt(32,?S)` doesn't match `0`. Execution stops — false quiescence.

The `evm/eq` rule uses `&` with loli guards:

```
evm/eq: ... -o { ... ((!neq X Y -o { stack SH 0 }) & (!eq X Y -o { stack SH 1 })) }.
```

Symexec forks at the `&`, but both loli continuations are stuck — neither `!neq X Y` nor `!eq X Y` can be proved for symbolic X, Y.

**Core tension:** Guards ensure soundness (prevent false branches) but require evaluation (which fails on symbolic values).

---

## Relationship to Problem A

**B1: Problem B is independent of Problem A.**

With `⊕` at comparison operations, GT doesn't COMPUTE `gt(32, ?S)` — it BRANCHES:

```
evm/gt: ... -o { ... ((stack SH (i e) * !gt X Y (i e)) + (stack SH e * !gt X Y e)) }.
```

Each branch gets a **concrete** boolean value (0 or 1). JUMPI always sees concrete — no Problem B. The path condition `!gt(32, ?S, (i e))` references the symbolic value but doesn't evaluate it.

For arithmetic flowing into comparisons: `ADD ?S 32 → ?R (symbolic)`, then `GT 100 ?R`. The ⊕ at GT branches and records `!gt(100, ?R, 1)` or `!gt(100, ?R, 0)` — referencing whatever Problem A produced for `?R`, without needing to evaluate it.

A determines what `plus(?S, 32)` IS. B determines how to branch on comparisons involving it. They compose but are orthogonal.

---

## Theoretical Analysis

### Which Connective?

| Connective | Meaning | Context | Who decides | Right for case split? |
|-----------|---------|---------|------------|----------------------|
| `A ⊗ B` (tensor) | Both exist | Split Δ | Nobody — parallel | No: resources can't go to both |
| `A & B` (with) | Both offered | Shared Δ | Consumer (external) | Semantically wrong: "both valid" |
| `A ⊕ B` (plus) | One holds | Shared Δ | Producer (internal) | Correct: "exactly one, handle both" |

**`⊕` is the correct connective.** EVM comparisons are deterministic — given inputs, the result is determined. `&` means "both arms available, you choose" — semantically wrong. `⊕` means "system has decided; handle both cases" — semantically correct.

The `⊕L` rule gives case analysis with **shared context**:

```
  Γ; Δ, A ⊢ C    Γ; Δ, B ⊢ C
  ─────────────────────────────  ⊕L (invertible)
       Γ; Δ, A ⊕ B ⊢ C
```

Both branches get the full Δ. This is NOT duplication of linear resources — the two premises are ALTERNATIVES (only one ultimately holds). Linearity preserved at the object level.

### ⊕ vs & — Coexistence

| | `A & B` (with) | `A ⊕ B` (plus) |
|---|---|---|
| **Semantics** | Both available, consumer picks | One holds, handle both cases |
| **Who decides** | Environment (external choice) | System (internal choice) |
| **Forward behavior** | Deferred (loli guards decide later) | Immediate case split |
| **Invertibility** | &R invertible, &L non-invertible | ⊕L invertible, ⊕R non-invertible |
| **Use case** | Lazy pairs, interactive choice, proof UI | Decidable predicates, boolean branching |

Both are needed. Current EVM rules use `&` where `⊕` is correct. Switch boolean operations to `⊕`, keep `&` for other uses.

### The DNF Analogy

```
Γ ⊗ (A ⊕ B)  ─── ⊕L ───→  (Γ, A ⊢ C) and (Γ, B ⊢ C)
```

This is distribution: ⊕ is "pushed outward," creating explicit alternatives. Each symexec leaf is a complete state with no pending ⊕. **Symbolic execution = normalization of ⊕ into a tree of alternatives.**

The distribution is valid because ⊕L shares context (both branches get Γ). No linear resource is copied — branches are alternatives, not parallel.

### Decidability Axiom

For decidable predicates, excluded middle holds constructively:

```
∀A,B. eq(A,B) ⊕ neq(A,B)     % decidability of equality
∀A,B. gt(A,B,R) for R ∈ {0,1} % decidability of comparison
```

Standard in constructive logic: Martin-Löf's `Dec(A) = A + (A → Void)`, Heyting arithmetic proves decidable equality. The FFI witnesses computability. Sound for ground values. For symbolic values, the axiom still holds (they WILL be concrete at runtime) — it gives us the right to case-split.

### Path Conditions

Path conditions are assumptions accumulated in each ⊕ branch, represented as **persistent ILL facts**.

When ⊕L case-splits on `(result * !neq C 0) ⊕ (result * !eq C 0)`:
- Branch 1 gets `!neq(C, 0)` in persistent context
- Branch 2 gets `!eq(C, 0)` in persistent context

They serve two purposes:
1. **Guard satisfaction:** Later rules needing `!neq C 0` find it via persistent state lookup
2. **Feasibility checking:** If `!neq(0, 0)` is persistent but `neq(0,0)` is decidably false, the branch is infeasible → prune

Not a new mechanism — just persistent facts. What's new: they're **asserted by ⊕L** rather than proved by backward chaining.

### What Existing Systems Do

| System | ⊕ in forward? | Nondeterminism | Branching model |
|--------|--------------|----------------|----------------|
| CLF/Celf | No (monad excludes ⊕) | Committed choice | Don't-care |
| LolliMon | No (monad excludes ⊕) | Committed choice | Don't-care |
| Ceptre | No (not in language) | Committed choice | Don't-care |
| Forum | Yes (full LL) | Both | Polarity-driven |
| CHR∨ | Yes (maps to ⊕) | Don't-know | Disjunctive heads |

No practical system puts ⊕ in forward chaining — they all use committed choice. CALC's symexec already goes beyond CLF by doing exhaustive exploration. Adding ⊕ to forward chaining is novel but well-founded (Forum, CHR∨, Andreoli focusing).

### Focusing Properties

⊕ is **positive** (synchronous). In Andreoli focusing:
- `⊕R`: synchronous — must choose a side during focus phase
- `⊕L`: invertible — case-split eagerly in the inversion phase

For forward rules: `⊕R` in consequent means "commit to a disjunct." For ground values, FFI decides. For symbolic, the choice is undecidable → explore both (don't-know nondeterminism over ⊕R).

---

## Concrete Rule Design

### evm/eq — comparison with ⊕

```
evm/eq: pc PC * code PC 0x14 * !inc PC PC' * gas GAS * !plus 2 GAS GAS' *
  sh (s (s SH)) * stack (s SH) X * stack SH Y
  -o {
    pc PC' * gas GAS' * code PC 0x14 * sh (s SH) *
    ((stack SH 0 * !neq X Y) + (stack SH 1 * !eq X Y))
  }.
```

No lolis, no guards. The `+` creates two alternatives in `expandConsequentChoices()`. Each branch produces the result AND the path condition.

### evm/jumpi — single rule with ⊕

```
evm/jumpi: pc PC * code PC 0x57 * !inc PC PC' * gas GAS * !plus 10 GAS GAS' *
  sh (s (s SH)) * stack (s SH) NPC * stack SH C
  -o {
    code PC 0x57 * sh SH * gas GAS' *
    ((pc NPC * !neq C 0) + (pc PC' * !eq C 0))
  }.
```

One rule (replaces `jumpi_neq` + `jumpi_eq`). Both branches explored. For ground C, the wrong branch has a contradictory path condition → pruned.

### Ground execution: pruning restores efficiency

For ground C = 5:
- Branch 1: `!neq(5, 0)` — true → continues
- Branch 2: `!eq(5, 0)` — false → pruned (optimization)

Without pruning, ground execution explores 2^k branches for k boolean operations. Eager pruning (check path condition via FFI at each ⊕) restores single-path behavior. This is an optimization, not a theoretical concern.

---

## Implementation

### What's Needed

1. **ill.calc:** `plus: formula -> formula -> formula` with annotations (@ascii `_ + _`, @prec, @category additive)
2. **ill.rules:** `plus_r1`, `plus_r2`, `plus_l` (three rules)
3. **compile.js / expandItem:** Add case for `plus` tag — same behavior as `with` (create two alternatives)
4. **Focusing metadata:** ⊕ positive, ⊕L invertible
5. **EVM rules:** Rewrite comparison/boolean operations to use `⊕` + path conditions
6. **(Optimization)** Eager path condition pruning for ground values

Steps 1-4: extend ILL to MALL fragment (~50 LOC).
Step 5: rewrite ~10 EVM rules.
Step 6: optimization (can be deferred).

---

## References

- Andreoli (1992) — Focusing proofs in linear logic
- Miller (1996) — Forum: multiple-conclusion specification logic
- Watkins, Cervesato, Pfenning, Walker (2004) — CLF
- Lopez, Pfenning, Polakow, Watkins (2005) — LolliMon
- Martens (2015) — Ceptre: programming interactive worlds
- Betz, Frühwirth (2013) — CHR∨ via linear logic
- Fages, Ruet, Soliman (2001) — Linear concurrent constraint programming
- Hedberg (1998) — Decidable equality in type theory
- Avron (1991) — Hypersequent calculus
- Liang, Miller (2009) — Focusing and polarization
