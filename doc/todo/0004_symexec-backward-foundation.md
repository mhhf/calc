---
title: "Add ∃ Connective to CALC — Full First-Class Support"
created: 2026-02-18
modified: 2026-02-21
summary: "Add explicit existential quantifier as a proper first-class connective: de Bruijn binders, alpha-equivalence, unification, backward prover, focusing, forward engine eigenvariables — sound and complete"
tags: [symexec, existential, eigenvariable, CLF, implementation, de-Bruijn]
type: implementation
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: []
required_by: [TODO_0005]
---

# Add ∃ Connective to CALC — Full First-Class Support

Decided in [TODO_0002](0002_symexec-expression-decision.md): explicit ∃ with eigenvariables and eager resolution. EVM/multisig is just the benchmark — ∃ must be proper through every layer, sound and complete.

## TODO_0004.Phase_1 — Store Foundation: De Bruijn Binders

Alpha-equivalence for free: `∃X.p(X)` and `∃Y.p(Y)` get the same hash.

- [ ] New Store tag `bound`: `Store.put('bound', [index])` — de Bruijn variable reference
- [ ] New Store tag `exists`: `Store.put('exists', [body])` — body uses `bound(0)` for the bound variable. Nested ∃ shift: inner binder's variable is `bound(0)`, outer is `bound(1)`.
- [ ] New Store tag `evar`: `Store.put('evar', [N])` — fresh eigenvariable (monotonic counter)
- [ ] `debruijnSubst(bodyHash, index, replacement)`: substitute de Bruijn `index` with `replacement` in `bodyHash`. Recursive over Store structure. Shift under nested binders. (~30 LOC)
- [ ] Tests: alpha-equivalence (same hash for renamed binders), substitution correctness, nested binders, shifting

## TODO_0004.Phase_2 — Grammar and Parser

- [ ] Grammar: `expr_exists` production in `lib/tree-sitter-mde/grammar.js` — `exists X. A` syntax
- [ ] Rebuild: `npm run build:ts:wasm`
- [ ] CST→AST: handle `expr_exists` in `lib/meta-parser/cst-to-ast.js`
- [ ] Program parser: `lib/engine/convert.js` — convert named variable to de Bruijn at parse time. In scope of the ∃ body, occurrences of the bound variable become `bound(0)`. Free variables shift up.
- [ ] ill.calc: declare `exists` connective with `@ascii "exists _ . _"`, `@prec`, `@category quantifier`

**De Bruijn conversion at parse time:** Parser sees `exists C. (stack(0, C) * !plus(A, B, C))`. Replaces `C` → `bound(0)` inside body. `A`, `B` remain as freevars/metavars. This is standard locally-nameless or full de Bruijn.

## TODO_0004.Phase_3 — Unification and Substitution Under Binders

- [ ] `unify.js`: case for `exists` — unify bodies after ensuring binders align. With de Bruijn, this is structural: `unify(bodyA, bodyB)` directly (alpha-equivalence is structural equality).
- [ ] `substitute.js`: substitution under ∃ binder — shift de Bruijn indices. `apply(exists(body), θ)` = `exists(apply(body, shift(θ)))` where `shift` increments all de Bruijn indices in θ by 1.
- [ ] `matchIndexed`/`applyIndexed`: handle `bound` tag (de Bruijn references don't match metavar slots; they're opaque)
- [ ] Tests: unification of ∃-formulas, substitution under nested binders, occurs check, edge cases (free vars with same index as bound)

## TODO_0004.Phase_4 — ill.rules: Sequent Rules for ∃

- [ ] ∃R (right introduction): `G ; D |- exists x . B  <-  G ; D |- B[t/x]` — provide witness t
- [ ] ∃L (left elimination): `G ; D, exists x . B |- C  <-  G ; D, B[a/x] |- C` — open, bind fresh eigenvariable a
- [ ] Rule descriptors for ∃ — extend descriptor format if needed for binding rules
- [ ] Rule interpreter: `buildRuleSpecs` handles ∃ (debruijnSubst for premise computation)

**∃L** is invertible (always safe to decompose). **∃R** is non-invertible (must choose witness — synchronous/focused).

## TODO_0004.Phase_5 — Focusing

∃ is **positive** (same polarity as ⊗, 1, ⊕):
- Invertible on LEFT → `findInvertible` decomposes ∃L automatically
- Focusable on RIGHT → ∃R appears during synchronous phase (focus decision)

- [ ] `lib/meta/focusing.js`: classify ∃ as positive (from descriptor or hardcoded)
- [ ] `lib/prover/focused.js`: `findInvertible` checks for ∃ on left; `chooseFocus` allows ∃ on right
- [ ] Witness strategy for ∃R in auto prover: introduce logic variable (standard Celf approach — delay witness choice, let unification determine it)

## TODO_0004.Phase_6 — Backward Prover ∃R and ∃L

- [ ] `lib/prover/generic.js`: `connective()` case for ∃ — dispatch to ∃R or ∃L based on side
- [ ] ∃L implementation: extract body, apply `debruijnSubst(body, 0, freshEvar)`, continue with substituted formula on left
- [ ] ∃R implementation: extract body, introduce logic variable (metavar), apply `debruijnSubst(body, 0, metavar)`, continue with substituted formula on right. Unification determines the witness.
- [ ] Manual prover: expose ∃R witness choice to user (UI selects witness term)
- [ ] Tests: backward proofs with ∃, both manual and auto

## TODO_0004.Phase_7 — Forward Engine: ∃ Decomposition + Eager Resolution

- [ ] `expandItem` case for `exists`: generate fresh `evar(N)` (monotonic counter), `debruijnSubst(body, 0, evarHash)`, continue expansion
- [ ] Eager resolution: after emitting persistent constraint `!plus(A, B, evar(N))`, try FFI → state → backward. If succeeds: bind evar to concrete value. If fails: constraint stays.
- [ ] Evar counter: monotonic (no undo needed — counter only goes up, even across backtrack)
- [ ] Constraint index: `Map<evarHash, [constraintFact, ...]>` for dependency tracking
- [ ] Propagation: `resolveEvar(evar, value, state, calc)` — cascade through dependency chain
- [ ] Integration with mutation+undo: index entries added/removed alongside state mutations

## TODO_0004.Phase_8 — EVM Rule Restructuring

11 rules need `!arithmetic` moved from antecedent to consequent with ∃:

**Arithmetic (4):** evm/add, evm/mul, evm/sub, evm/exp
**Comparison (2):** evm/lt, evm/gt
**Bitwise (3):** evm/and, evm/or, evm/not
**Memory (2):** concatMemory/s, calldatacopy/s

Example:
```
% Before:
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC') * !plus(A, B, C)
  -o { pc(PC') * stack(0, C) }.

% After:
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC')
  -o { exists C. (pc(PC') * stack(0, C) * !plus(A, B, C)) }.
```

- [ ] Rewrite 11 rules in evm.ill
- [ ] Verify ground execution unchanged (same FFI path, same results)
- [ ] Verify symbolic execution produces eigenvariables + constraints
- [ ] Symexec benchmark: compare tree sizes and timing

## TODO_0004.Phase_9 — Tests (all phases)

- [ ] Store: de Bruijn representation, alpha-equivalence, `debruijnSubst`, nested binders
- [ ] Parser: `exists X. A` round-trips through parse → Store → render
- [ ] Unification: ∃-formulas unify correctly, substitution under binders, shifting
- [ ] Backward prover: proofs with ∃ (both ∃L and ∃R), focused and unfocused
- [ ] Forward engine: `expandItem` with ∃, eager resolution, constraint index
- [ ] Integration: symbolic ADD chain, branching (⊕ + ∃), late resolution cascade
- [ ] Regression: all existing tests pass (kernel, generic, manual, rule-interpreter, engine)

## Open Questions

**NQ1:** Also add ∀ (universal quantifier)? ∀ is the dual of ∃ — negative polarity, invertible on right, focusable on left. CLF has both. Adding both simultaneously shares infrastructure (de Bruijn, shifting, substitution under binders). But ∀ is not needed for the symexec use case.

**NQ2:** De Bruijn representation: full de Bruijn (all variables are indices) or locally nameless (bound = indices, free = names)? Locally nameless avoids shifting for free variables. Both are standard.

**NQ3:** `build:bundle` — does `out/ill.json` need changes for ∃? If ∃ rules have descriptors, yes. If ∃ is handled specially by the interpreter (like structural rules), maybe not.

## Cross-References

- [TODO_0002](0002_symexec-expression-decision.md) — decision and rationale
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (after this)
- `doc/research/eigenvariable-walkthrough.md` — scenarios 1-6, scale analysis, ⊕ composition
- `doc/research/symbolic-values-in-forward-chaining.md` — theoretical foundations
