---
title: "Add ∃ and ∀ Quantifiers to CALC — Full First-Class Support"
created: 2026-02-18
modified: 2026-02-22
summary: "Add explicit existential and universal quantifiers as proper first-class connectives: de Bruijn binders, alpha-equivalence, unification, backward prover, focusing, forward engine eigenvariables — sound and complete"
tags: [symexec, existential, universal, eigenvariable, clf, implementation, de-bruijn]
type: implementation
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: []
required_by: [TODO_0005]
---

# Add ∃ and ∀ Quantifiers to CALC

Decided in [TODO_0002](0002_symexec-expression-decision.md): explicit ∃ with eigenvariables and eager resolution. ∀ added in the same leg — shared de Bruijn infrastructure, ~25 LOC incremental, completes first-order linear logic (MALL₁).

**Polarity:** ∃ is **positive** (like ⊗, 1, ⊕), ∀ is **negative** (like ⊸, &). Duality: ∃ is to ⊕ as ∀ is to &.

**Forward engine:** Only ∃ appears inside the monad `{A}` (positive). ∀ is negative — quantifies over rule variables at the outer level (already implicit). No forward engine changes for ∀.

**Arity:** Store representation is arity-1 (`Store.put('exists', [body])`). Grammar syntax is arity-2 (`exists X. body`). Parser closes: named variable → `bound(0)` in body. Renderer opens: generates fresh display name, substitutes via `debruijnSubst`.

## TODO_0004.Phase_1 — Store Foundation: Locally Nameless Binders

Bound variables are de Bruijn indices (`bound(0)`), free variables keep their Store hashes unchanged. Alpha-equivalence for free: `∃X.p(X)` and `∃Y.p(Y)` get the same hash. No shifting needed for free variables under substitution (Aydemir et al. 2008, §2.3).

- [ ] New Store tag `bound`: `Store.put('bound', [index])` — de Bruijn index (add to `BIGINT_CHILD_TAGS`)
- [ ] New Store tag `exists`: `Store.put('exists', [body])` — arity-1, body uses `bound(0)`
- [ ] New Store tag `forall`: `Store.put('forall', [body])` — same representation as `exists`
- [ ] New Store tag `evar`: `Store.put('evar', [N])` — fresh eigenvariable (add to `BIGINT_CHILD_TAGS`)
- [ ] `lib/kernel/fresh.js`: `createFreshSource(next, stride)` — module-level singleton. `freshEvar()` returns `Store.put('evar', [next])`, advances `next += stride`. `fork(n)` returns n children with interleaved streams (child i: `next+i*stride, stride*n`). `reset()` for tests. (~10 LOC)
- [ ] `debruijnSubst(bodyHash, index, replacement)` in `lib/kernel/substitute.js`: substitute de Bruijn `index` with `replacement`. Recursive over Store. Shift index under nested `exists`/`forall`. (~30 LOC)
- [ ] Tests: alpha-equivalence, substitution, nested/mixed binders (`∃X.∀Y.p(X,Y)`), shifting, fresh source fork

## TODO_0004.Phase_2 — Grammar and Parser

- [ ] Grammar: `expr_exists` / `expr_forall` in `lib/tree-sitter-mde/grammar.js` — `exists X. A` / `forall X. A`. Insert between `expr` and `expr_plus` in precedence cascade.
- [ ] Rebuild: `npm run build:ts:wasm` (NOT just `build:ts` — runtime uses WASM)
- [ ] CST→AST: handle both in `lib/meta-parser/cst-to-ast.js` (switch cases, like `expr_bang`)
- [ ] Program parser (`lib/engine/convert.js`): add `binderEnv` stack to `convertExpr`. On `exists C. body`: push `C`, convert body (`C` → `bound(depth)`), pop. Free variables not in stack remain as `freevar`. (~15 LOC)
- [ ] Rules parser (`lib/rules/rules2-parser.js`): same `binderEnv` close mechanism
- [ ] `ill.calc`: declare both connectives with `@ascii`, `@prec`, `@category quantifier`, `@polarity positive` on ∃
- [ ] Renderer: `@binding quantifier` annotation. Detect in renderer, generate fresh display name, open body with `debruijnSubst`. Display-only, never stored.

## TODO_0004.Phase_3 — Unification and Substitution Under Binders

No shifting needed (locally nameless): `apply(exists(body), θ)` = `exists(apply(body, θ))`. θ maps free variables (hashes) to terms. `bound(k)` is a distinct tag, never in θ. Existing `matchIndexed`/`applyIndexed`/`subCompiled` need zero changes.

- [ ] `unify.js`: structural cases for `exists`/`forall` — unify bodies. `exists` only unifies with `exists`, `forall` with `forall`.
- [ ] `substitute.js`: recurse through `exists`/`forall` like any structural node. `bound(k)` is a leaf, untouched.
- [ ] Tests: unification of quantified formulas, substitution under binders, occurs check

## TODO_0004.Phase_4 — ill.rules: Sequent Rules

**∃ rules:**
- [ ] ∃R: `G ; D |- exists x . B  <-  G ; D |- B[t/x]` — provide witness (non-invertible)
- [ ] ∃L: `G ; D, exists x . B |- C  <-  G ; D, B[a/x] |- C` — eigenvariable (invertible)

**∀ rules:**
- [ ] ∀R: `G ; D |- forall x . B  <-  G ; D |- B[a/x]` — eigenvariable (invertible)
- [ ] ∀L: `G ; D, forall x . B |- C  <-  G ; D, B[t/x] |- C` — instantiate (non-invertible)

**Symmetry:** ∃L ↔ ∀R (eigenvariable), ∃R ↔ ∀L (choose term).

- [ ] Write rules with `@binding eigenvariable` (∃L, ∀R) / `@binding metavar` (∃R, ∀L). Annotation parsing already supported in `rules2-parser.js`.
- [ ] `@polarity positive` on ∃ — contextFlow inference misclassifies (preserved → negative). Override already supported (`explicitPolarity` in `buildFocusingMeta`). ∀ infers correctly.
- [ ] Extend descriptor: `binding` field — generic, reusable for future binders (μ/ν, Π/Σ)
- [ ] Rule interpreter: `buildRuleSpecs`/`buildRuleSpecsFromMeta` reads `binding`, calls `debruijnSubst`
- [ ] `npm run build:bundle` — verify ∃/∀ in `out/ill.json`

## TODO_0004.Phase_5 — Focusing

Polarity handled in Phase 4. No changes in `focusing.js` — reads descriptors and explicit polarity, both already supported.

- [ ] `focused.js`: `findInvertible` checks ∃ on left, ∀ on right. `chooseFocus` allows ∃ on right, ∀ on left.
- [ ] Witness strategy for ∃R/∀L in auto prover: introduce logic variable (Celf approach — delay choice, let unification determine)

## TODO_0004.Phase_6 — Backward Prover

- [ ] `generic.js`: `connective()` cases for `exists`/`forall`, dispatch by side
- [ ] ∃L: `debruijnSubst(body, 0, freshEvar)`, continue on left
- [ ] ∃R: `debruijnSubst(body, 0, metavar)`, continue on right
- [ ] ∀R: `debruijnSubst(body, 0, freshEvar)`, continue on right (same as ∃L)
- [ ] ∀L: `debruijnSubst(body, 0, metavar)`, continue on left (same as ∃R)
- [ ] Manual prover: expose witness choice for ∃R/∀L to user
- [ ] Tests: backward proofs, focused and unfocused

## TODO_0004.Phase_7 — Forward Engine: ∃ Decomposition + Eager Resolution

Only ∃ — ∀ is negative, doesn't appear inside `{A}`.

- [ ] `expandItem` case for `exists`: `freshEvar()`, `debruijnSubst(body, 0, evarHash)`, continue
- [ ] Eager resolution: after emitting `!plus(A, B, evar(N))`, try FFI → state → backward. Succeeds → concrete value (evar never emitted). Fails → evar + constraint stays as persistent fact.
- [ ] Counter is monotonic (no undo). `fork(n)` for future parallel symexec.

Constraint propagation is [TODO_0005](0005_symexec-simplification.md).

## TODO_0004.Phase_8 — EVM Rule Restructuring

11 rules: move `!arithmetic` from antecedent to consequent with ∃.

**Arithmetic (4):** add, mul, sub, exp | **Comparison (2):** lt, gt | **Bitwise (3):** and, or, not | **Memory (2):** concatMemory/s, calldatacopy/s

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

## TODO_0004.Phase_9 — Tests

- [ ] Store: de Bruijn, alpha-equivalence, `debruijnSubst`, mixed nested binders
- [ ] Parser: `exists X. A` / `forall X. A` round-trip (parse → Store → render)
- [ ] Unification: quantified formulas, substitution under binders
- [ ] Backward prover: all four rules, focused and unfocused
- [ ] Forward engine: `expandItem` with ∃, eager resolution
- [ ] Integration: symbolic ADD chain, branching (⊕ + ∃), evar accumulation
- [ ] Regression: all existing tests pass

## Resolved Questions

All resolved. Decisions integrated into phases above.

| # | Question | Decision | Phase |
|---|----------|----------|-------|
| NQ1 | Also add ∀? | Yes, ~25 LOC incremental | All |
| NQ2 | Full de Bruijn or locally nameless? | Locally nameless (no shifting for free vars) | 1 |
| NQ3 | ill.json changes? | Add `binding` field to descriptor | 4 |
| NQ4 | Polarity inference for ∃? | `@polarity positive` explicit override | 4 |
| NQ5 | Fresh variable mechanism? | Splittable monotonic counter in `fresh.js` | 1 |
| NQ6 | .rules syntax? | `@binding eigenvariable` / `@binding metavar` | 4 |
| NQ7 | Close operation? | `binderEnv` stack in parsers | 2 |
| NQ8 | Rendering? | `@binding quantifier`, fresh display names | 2 |
| NQ9 | Name hints? | Side table `Map<hash, string>`, not in Store | -- |

## Cross-References

- [TODO_0002](0002_symexec-expression-decision.md) — decision and rationale
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (after this)
- `doc/research/eigenvariable-walkthrough.md` — scenarios, scale analysis, ⊕ composition
- `doc/research/symbolic-values-in-forward-chaining.md` — theoretical foundations
- `doc/research/fresh-variable-generation.md` — fresh variable survey (8 systems)
