---
title: "Add ∃ Connective and Forward-Engine Eigenvariables"
created: 2026-02-18
modified: 2026-02-21
summary: "Add explicit existential quantifier to CALC: grammar, parser, forward engine ∃-decomposition, eager resolution, constraint tracking"
tags: [symexec, existential, eigenvariable, CLF, implementation]
type: implementation
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: [TODO_0002]
required_by: [TODO_0005]
---

# Add ∃ Connective and Forward-Engine Eigenvariables

Decided in [TODO_0002](0002_symexec-expression-decision.md): explicit ∃ with eigenvariables and eager resolution.

## TODO_0004.Phase_1 — Grammar and Parser (~30 LOC)

Add `exists X. A` syntax to tree-sitter grammar and wire through parsers.

- [ ] Grammar: `expr_exists` production in `lib/tree-sitter-mde/grammar.js`
- [ ] Rebuild: `npm run build:ts:wasm` (not just `build:ts`)
- [ ] CST→AST: handle `expr_exists` in `lib/meta-parser/cst-to-ast.js`
- [ ] Program parser: handle ∃ in `lib/engine/convert.js` — Store node `Store.put('exists', [body])`
- [ ] ill.calc: declare `exists` connective with `@ascii "exists _ . _"`, `@prec`, `@category quantifier`

**Design choice:** ∃-bound variable in rule consequents is a metavar slot marked as existential. The compiled rule tracks which slots are existential vs universal (matched by antecedent). De Bruijn for the Store representation of the binder.

## TODO_0004.Phase_2 — Forward Engine ∃ Decomposition + Eager Resolution (~50 LOC)

- [ ] `expandItem` case for tag `exists`: generate fresh `evar(N)` (monotonic counter), substitute into body, continue decomposition
- [ ] `evar` Store tag: `Store.put('evar', [N])` — unique hash by construction
- [ ] Eager resolution: after emitting a persistent constraint `!plus(A, B, evar(N))`, immediately try FFI → state → backward. If succeeds: bind evar to concrete value. If fails: constraint stays.
- [ ] Ensure evar counter is monotonic (no undo needed — counter only goes up, even across undo/backtrack)

## TODO_0004.Phase_3 — Constraint Index and Dependency Tracking (~40 LOC)

- [ ] Inverted index: `Map<evarHash, [constraintFact, ...]>` — which constraints mention each evar
- [ ] On resolution (evar becomes ground): look up dependent constraints, re-prove via FFI, cascade
- [ ] Integration with mutation+undo: index entries added during exploration, removed on undo
- [ ] Propagation function: `resolveEvar(evarHash, concreteValue, state, calc)` — walks dependency chain

## TODO_0004.Phase_4 — EVM Rule Restructuring

11 rules need `!arithmetic` moved from antecedent to consequent with ∃:

**Arithmetic (4):** evm/add, evm/mul, evm/sub, evm/exp
**Comparison (2):** evm/lt, evm/gt
**Bitwise (3):** evm/and, evm/or, evm/not
**Memory (2):** concatMemory/s, calldatacopy/s

Example transformation:
```
% Before:
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC') * !plus(A, B, C)
  -o { pc(PC') * stack(0, C) }.

% After:
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC')
  -o { exists C. (pc(PC') * stack(0, C) * !plus(A, B, C)) }.
```

26 rules stay unchanged (ground PC/GAS: `!inc`, `!plus N GAS GAS'` with literal N).
3 rules with ⊕ guards (eq/neq/iszero/jumpi) stay as-is.

- [ ] Rewrite 11 rules in evm.ill
- [ ] Verify ground execution unchanged (same FFI path, same results)
- [ ] Verify symbolic execution produces eigenvariables + constraints
- [ ] Symexec benchmark: compare tree sizes and timing

## TODO_0004.Phase_5 — Tests

- [ ] Unit: fresh evar generation, Store.put('evar', ...), constraint index
- [ ] Unit: expandItem with ∃ node — generates fresh, substitutes, continues
- [ ] Unit: eager resolution — ground inputs resolve immediately, symbolic accumulate
- [ ] Integration: symbolic ADD chain (Scenario 2 from walkthrough)
- [ ] Integration: symbolic branching (Scenario 3 — ⊕ + ∃ composition)
- [ ] Integration: full EVM symexec with restructured rules
- [ ] Regression: existing ground-only EVM tests still pass

## Deferred

- **Backward prover ∃ (∃R, ∃L):** Not needed for forward-engine symbolic execution. Add when proof search needs ∃.
- **Focusing for ∃:** ∃ is positive (invertible on left, focusable on right). Add with backward prover support.
- **ill.rules ∃ rules:** Sequent-notation rules for ∃. Add with backward prover support.
- **Constraint propagation (P3):** See [TODO_0005](0005_symexec-simplification.md).

## Cross-References

- [TODO_0002](0002_symexec-expression-decision.md) — decision and rationale
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (after this)
- `doc/research/eigenvariable-walkthrough.md` — scenarios 1-6, scale analysis
- `doc/research/symbolic-values-in-forward-chaining.md` — theoretical foundations
