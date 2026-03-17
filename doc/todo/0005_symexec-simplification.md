---
title: "Symbolic Execution: Constraint Propagation"
created: 2026-02-18
modified: 2026-02-21
summary: "Constraint propagation levels for eigenvariable path: equality resolution, FFI re-check, chain simplification, domain propagation"
tags: [symexec, simplification, constraint-propagation, CLP]
type: implementation
cluster: Symexec
status: planning
priority: 5
depends_on: [TODO_0004]
required_by: []
---

# Constraint Propagation

After [TODO_0004](0004_symexec-backward-foundation.md) (∃ + eigenvariables), constraints accumulate without simplification. This TODO adds propagation levels incrementally.

## TODO_0005.Level_0 — Equality Resolution (~30 LOC)

When `!eq(α, v)` appears (from ⊕ branching), substitute α → v everywhere. Cascade through dependent constraints via inverted index.

## TODO_0005.Level_1 — FFI Re-check (~20 LOC)

When a constraint's inputs all become ground, re-prove via FFI. E.g., `!plus(binlit(5), binlit(3), α₀)` → FFI gives 8 → α₀ = 8 → cascade.

## TODO_0005.Level_2 — Chain Simplification (~100 LOC)

Detect and merge constraint chains: `!plus(X, 3, Y), !plus(Y, 5, Z)` → `!plus(X, 8, Z)`. Delete intermediate evar. Eigenvariable analogue of AC-normalization. Requires constraint pattern matching.

## TODO_0005.Level_3 — Domain Propagation (~200 LOC)

Track intervals: `!neq(α, 0)` → domain(α) = [1, 2²⁵⁶-1]. CLP(FD) territory.

## TODO_0005.Level_4 — Multi-Mode Resolution

Constraint rewriting for non-standard modes: `!plus(A, B, C) ∧ ground(A,C) ⟹ B = C-A`. Requires multi-mode FFI or explicit rewrite rules.

Each level independent and testable. Level 0 is the minimum useful propagation.

See: [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) §3.6, [RES_0021](../research/0021_fresh-variable-generation.md)
