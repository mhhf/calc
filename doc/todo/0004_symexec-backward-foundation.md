---
title: "Add ∃ and ∀ Quantifiers to CALC — Full First-Class Support"
created: 2026-02-18
modified: 2026-02-21
summary: "Add explicit existential and universal quantifiers as proper first-class connectives: de Bruijn binders, alpha-equivalence, unification, backward prover, focusing, forward engine eigenvariables — sound and complete"
tags: [symexec, existential, universal, eigenvariable, CLF, implementation, de-Bruijn]
type: implementation
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: []
required_by: [TODO_0005]
---

# Add ∃ and ∀ Quantifiers to CALC — Full First-Class Support

Decided in [TODO_0002](0002_symexec-expression-decision.md): explicit ∃ with eigenvariables and eager resolution. ∀ added in the same leg — shared de Bruijn infrastructure, ~25 LOC incremental, completes first-order linear logic (MALL₁).

**Polarity:**
- ∃ is **positive** (like ⊗, 1, ⊕): invertible on left, focusable on right
- ∀ is **negative** (like ⊸, &): invertible on right, focusable on left

**Duality:** ∃ is to ⊕ as ∀ is to &. Quantifier versions of additive choice.

**Forward engine:** Only ∃ appears inside the monad `{A}` (positive). ∀ is negative — it quantifies over rule variables at the outer level (already implicit in CALC). No forward engine changes for ∀.

## TODO_0004.Phase_1 — Store Foundation: De Bruijn Binders

Alpha-equivalence for free: `∃X.p(X)` and `∃Y.p(Y)` get the same hash. Same for `∀X` / `∀Y`.

- [ ] New Store tag `bound`: `Store.put('bound', [index])` — de Bruijn variable reference
- [ ] New Store tag `exists`: `Store.put('exists', [body])` — body uses `bound(0)` for the bound variable
- [ ] New Store tag `forall`: `Store.put('forall', [body])` — same de Bruijn representation as `exists`
- [ ] New Store tag `evar`: `Store.put('evar', [N])` — fresh eigenvariable (monotonic counter)
- [ ] `debruijnSubst(bodyHash, index, replacement)`: substitute de Bruijn `index` with `replacement` in `bodyHash`. Recursive over Store structure. Shift under nested binders (both `exists` and `forall`). (~30 LOC)
- [ ] Tests: alpha-equivalence, substitution correctness, nested/mixed binders (`∃X.∀Y.p(X,Y)`), shifting

## TODO_0004.Phase_2 — Grammar and Parser

- [ ] Grammar: `expr_exists` and `expr_forall` productions in `lib/tree-sitter-mde/grammar.js` — `exists X. A` and `forall X. A` syntax
- [ ] Rebuild: `npm run build:ts:wasm`
- [ ] CST→AST: handle both in `lib/meta-parser/cst-to-ast.js`
- [ ] Program parser: `lib/engine/convert.js` — convert named variable to de Bruijn at parse time. In scope of binder body, occurrences of the bound variable become `bound(0)`. Free variables shift up. Same logic for both quantifiers.
- [ ] ill.calc: declare both connectives with `@ascii`, `@prec`, `@category quantifier`

**De Bruijn conversion at parse time:** Parser sees `exists C. (stack(0, C) * !plus(A, B, C))`. Replaces `C` → `bound(0)` inside body. `A`, `B` remain as freevars/metavars. Same for `forall X. body`.

## TODO_0004.Phase_3 — Unification and Substitution Under Binders

- [ ] `unify.js`: cases for `exists` and `forall` — unify bodies structurally (de Bruijn = alpha-equivalence is structural equality). `exists` only unifies with `exists`, `forall` with `forall`.
- [ ] `substitute.js`: substitution under binder — shift de Bruijn indices. `apply(exists(body), θ)` = `exists(apply(body, shift(θ)))`. Same for `forall`.
- [ ] `matchIndexed`/`applyIndexed`: handle `bound` tag (opaque — de Bruijn references don't match metavar slots)
- [ ] Tests: unification of quantified formulas, mixed nested binders, substitution, occurs check

## TODO_0004.Phase_4 — ill.rules: Sequent Rules for ∃ and ∀

**∃ rules:**
- [ ] ∃R (right): `G ; D |- exists x . B  <-  G ; D |- B[t/x]` — provide witness t
- [ ] ∃L (left): `G ; D, exists x . B |- C  <-  G ; D, B[a/x] |- C` — open, bind fresh eigenvariable a
- ∃L is invertible. ∃R is non-invertible (must choose witness).

**∀ rules:**
- [ ] ∀R (right): `G ; D |- forall x . B  <-  G ; D |- B[a/x]` — introduce eigenvariable a (prove for generic)
- [ ] ∀L (left): `G ; D, forall x . B |- C  <-  G ; D, B[t/x] |- C` — instantiate with chosen t
- ∀R is invertible. ∀L is non-invertible (must choose instantiation).

**Symmetry:** ∃L ↔ ∀R (both introduce eigenvariable). ∃R ↔ ∀L (both choose a term).

- [ ] Rule descriptors for both — extend descriptor format if needed for binding rules
- [ ] Rule interpreter: `buildRuleSpecs` handles both (debruijnSubst for premise computation)

## TODO_0004.Phase_5 — Focusing

- [ ] `lib/meta/focusing.js`: classify ∃ as positive, ∀ as negative
- [ ] `lib/prover/focused.js`:
  - `findInvertible` checks for ∃ on left AND ∀ on right (both always decompose)
  - `chooseFocus` allows ∃ on right AND ∀ on left (both need a decision)
- [ ] Witness strategy for ∃R and ∀L in auto prover: introduce logic variable (standard Celf approach — delay choice, let unification determine it)

## TODO_0004.Phase_6 — Backward Prover

- [ ] `lib/prover/generic.js`: `connective()` cases for `exists` and `forall`, dispatch by side

**∃:**
- [ ] ∃L: extract body, `debruijnSubst(body, 0, freshEvar)`, continue on left
- [ ] ∃R: extract body, introduce logic variable, `debruijnSubst(body, 0, metavar)`, continue on right

**∀:**
- [ ] ∀R: extract body, `debruijnSubst(body, 0, freshEvar)`, continue on right (same mechanism as ∃L)
- [ ] ∀L: extract body, introduce logic variable, `debruijnSubst(body, 0, metavar)`, continue on left (same mechanism as ∃R)

- [ ] Manual prover: expose witness choice for ∃R and ∀L to user
- [ ] Tests: backward proofs with both quantifiers, focused and unfocused

## TODO_0004.Phase_7 — Forward Engine: ∃ Decomposition + Eager Resolution

Only ∃ — ∀ is negative, doesn't appear inside the monad `{A}`.

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

- [ ] Store: de Bruijn for both quantifiers, alpha-equivalence, `debruijnSubst`, mixed nested binders
- [ ] Parser: `exists X. A` and `forall X. A` round-trip through parse → Store → render
- [ ] Unification: quantified formulas unify correctly, substitution under binders, shifting
- [ ] Backward prover: proofs with ∃ and ∀ (all four rules), focused and unfocused
- [ ] Forward engine: `expandItem` with ∃, eager resolution, constraint index
- [ ] Integration: symbolic ADD chain, branching (⊕ + ∃), late resolution cascade
- [ ] Regression: all existing tests pass (kernel, generic, manual, rule-interpreter, engine)

## Open Questions

**NQ1 (resolved):** ~~Also add ∀?~~ Yes — included in this TODO. ~25 LOC incremental, shared infrastructure.

**NQ2:** De Bruijn representation: full de Bruijn (all variables are indices) or locally nameless (bound = indices, free = names)? Locally nameless avoids shifting for free variables. Both are standard.

**NQ3:** `build:bundle` — does `out/ill.json` need changes for ∃/∀? If rules have descriptors, yes. If handled specially by the interpreter (like structural rules), maybe not.

## Cross-References

- [TODO_0002](0002_symexec-expression-decision.md) — decision and rationale
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (after this)
- `doc/research/eigenvariable-walkthrough.md` — scenarios 1-6, scale analysis, ⊕ composition
- `doc/research/symbolic-values-in-forward-chaining.md` — theoretical foundations
