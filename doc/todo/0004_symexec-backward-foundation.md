---
title: "Add ∃ and ∀ Quantifiers to CALC — Full First-Class Support"
created: 2026-02-18
modified: 2026-02-23
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
- [ ] `state.nameHints: Map<hash, string>`: add to `createState()` in forward.js and `decomposeQuery()` in convert.js. Share reference (not copy) in `applyMatch`, `snapshotState`, `applyMatchChoice`. See "Name Hints" section below.
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

**Why this is safe:** If θ[X] = some_term and some_term contains `bound(k)`, that `bound(k)` refers to a binder *within* some_term's own structure, not to the enclosing exists/forall. All Store values are locally closed (no dangling bound vars). This is the core invariant of locally nameless.

**Occurs check:** CALC's `unifyUF()` already has an eager occurs check (`occursInUF()`, unify.js line 264). No changes needed — prevents `X = f(X)` circularity when unifying quantified formulas.

- [ ] `unify.js`: structural cases for `exists`/`forall` — unify bodies. `exists` only unifies with `exists`, `forall` with `forall`.
- [ ] `substitute.js`: recurse through `exists`/`forall` like any structural node. `bound(k)` is a leaf, untouched.
- [ ] Tests: unification of quantified formulas, substitution under binders

## TODO_0004.Phase_4 — ill.rules: Sequent Rules

**∃ rules:**
- [ ] ∃R: `G ; D |- exists x . B  <-  G ; D |- B[t/x]` — provide witness (non-invertible)
- [ ] ∃L: `G ; D, exists x . B |- C  <-  G ; D, B[a/x] |- C` — eigenvariable (invertible)

**∀ rules:**
- [ ] ∀R: `G ; D |- forall x . B  <-  G ; D |- B[a/x]` — eigenvariable (invertible)
- [ ] ∀L: `G ; D, forall x . B |- C  <-  G ; D, B[t/x] |- C` — instantiate (non-invertible)

**Symmetry:** ∃L ↔ ∀R (eigenvariable), ∃R ↔ ∀L (choose term).

- [ ] Write rules with `@binding eigenvariable` (∃L, ∀R) / `@binding metavar` (∃R, ∀L). The `rules2-parser.js` regex loop (line ~91) already captures any `@key value` pair into `annotations`, but the return object (line ~196) doesn't extract `binding`. Add: `binding: annotations.binding || null` to the returned descriptor.
- [ ] `@polarity positive` on ∃ — contextFlow inference misclassifies (preserved → negative). Override already supported (`explicitPolarity` in `buildFocusingMeta`). ∀ infers correctly (∀R has single premise, preserved context → negative, which is correct).
- [ ] Extend descriptor: `binding` field — generic, reusable for future binders (μ/ν, Π/Σ)
- [ ] Rule interpreter `makePremises` — reads `binding`, generates fresh variable, opens binder:

**Eigenvariable rules** (∃L, ∀R) — `binding === 'eigenvariable'`:
```javascript
makePremises(formula, seq, index) {
  const body = Store.child(formula, 0)       // arity-1
  const a = freshEvar()                       // fresh parameter
  const opened = debruijnSubst(body, 0, a)    // substitute bound(0) → a
  state.nameHints.set(a, varNameFromSource)   // display hint
  // build premise with 'opened' as the new formula
}
```

**Witness rules** (∃R, ∀L) — `binding === 'metavar'`:
```javascript
makePremises(formula, seq, index) {
  const body = Store.child(formula, 0)
  const mv = Store.put('freevar', ['_witness'])  // logic variable
  const opened = debruijnSubst(body, 0, mv)
  // build premise with 'opened'; unification determines mv
}
```

- [ ] `npm run build:bundle` — verify ∃/∀ in `out/ill.json`

## TODO_0004.Phase_5 — Focusing

No code changes needed in `focusing.js` — it reads descriptors and explicit polarity, both already set in Phase 4. `findInvertible` and `chooseFocus` dispatch on polarity metadata, not on hardcoded connective names.

- [ ] Verify: `findInvertible` picks up ∃ on left (positive = invertible on left), ∀ on right (negative = invertible on right)
- [ ] Verify: `chooseFocus` allows ∃ on right (positive = focusable on right), ∀ on left (negative = focusable on left)

**Eigenvariable safety in backward prover:** The eigenvariable condition (fresh name must not appear in conclusion) is automatic in locally nameless. Fresh evars are created during proof search and are fresh by construction (monotonic counter). `applyRule` returns `theta: []` for structural rules — no substitution flows back to the conclusion. Eigenvariable leakage is structurally impossible.

## TODO_0004.Phase_6 — Backward Prover

- [ ] `generic.js`: `connective()` cases for `exists`/`forall`, dispatch by side
- [ ] ∃L: `debruijnSubst(body, 0, freshEvar())`, continue on left — populate `state.nameHints`
- [ ] ∃R: `debruijnSubst(body, 0, metavar)`, continue on right — logic variable, resolved by unification
- [ ] ∀R: `debruijnSubst(body, 0, freshEvar())`, continue on right — same mechanism as ∃L
- [ ] ∀L: `debruijnSubst(body, 0, metavar)`, continue on left — same mechanism as ∃R
- [ ] Manual prover: expose witness choice for ∃R/∀L to user (user provides witness term)
- [ ] Witness strategy for ∃R/∀L in auto prover: introduce logic variable (Celf approach — delay choice, let unification determine)
- [ ] Tests: backward proofs, focused and unfocused

## TODO_0004.Phase_7 — Forward Engine: ∃ Decomposition + Eager Resolution

Only ∃ — ∀ is negative, doesn't appear inside `{A}`.

### Compile-time: expandItem

**Key insight** (from [TODO_0002](0002_symexec-expression-decision.md)): ∃ in rule consequents is immediately decomposed by `expandItem` at compile time. It never persists as a formula in state. ∃-bound variables are just metavar slots not matched by any antecedent — existing `metavarSlots` infrastructure suffices.

- [ ] `expandItem` case for `exists` in `compile.js`:

```javascript
if (t === 'exists') {
  const body = Store.child(h, 0)
  const slotVar = createMetavar()               // new freevar for this slot
  const opened = debruijnSubst(body, 0, slotVar) // open binder
  return expandItem(opened)                       // continue expanding
}
```

The metavar gets a slot in `metavarSlots` but appears in NO antecedent pattern. After `tryMatch`, this slot is unbound.

- [ ] Mark existential slots in compiled rule metadata: `rule.existentialSlots = [slotIdx, ...]`

### Runtime: eager resolution (between tryMatch and mutateState)

After `tryMatch` binds antecedent vars, existential slots are unbound. Resolve them before calling `mutateState`:

```
tryMatch completes → antecedent vars bound, ∃-slots unbound
  ↓
for each unbound existential slot:
  substitute known vars into the slot's associated persistent pattern
  try FFI(pattern)     → succeeds: bind slot to concrete result
  try state lookup     → succeeds: bind slot
  try backward proving → succeeds: bind slot
  all fail             → bind slot to freshEvar(), pattern becomes constraint
  ↓
mutateState (all slots now bound)
```

- [ ] In symexec.js exploration loop: after `tryMatch` succeeds, call `resolveExistentials(theta, slots, rule, state, calc)` before `mutateState`
- [ ] `resolveExistentials`: for each `rule.existentialSlots[i]`, substitute theta into the persistent consequent pattern, try three-level fallback (reuses `provePersistentGoals` machinery). Success → `theta[slot] = result`. Failure → `theta[slot] = freshEvar()`, populate `state.nameHints`.
- [ ] Same flow in `forward.js` `run()` (committed-choice path)

**Ground execution:** FFI succeeds immediately for all 11 EVM arithmetic rules → concrete value → zero overhead vs current behavior. Evars never enter state.

**Symbolic execution:** FFI fails → evar created → persistent constraint `!plus(A, B, evar(N))` emitted to state. Execution continues.

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
| NQ9 | Name hints? | `state.nameHints: Map<hash, string>` on proof state (~15 LOC threading) | 1,6,7 |

## Name Hints: `state.nameHints`

Display-name association for eigenvariables. `Map<hash, string>` on the proof/execution state. Populated when opening a binder with `freshEvar()`. Renderer reads from it to display `evar(42)` as its original source name.

**Threading cost (~15 lines):** nameHints is monotonic (append-only), so the Map reference is **shared** (not copied) across state copies.

- `createState()` / `decomposeQuery()`: `nameHints: new Map()` — 2 lines
- `applyMatch()`, `snapshotState()`, `applyMatchChoice()`: `nameHints: state.nameHints` (shared reference) — 3 lines
- `explore()` init: `nameHints: new Map(initialState.nameHints)` — 1 line
- `mutateState()`: no change (monotonic, no undo needed) — 0 lines
- Renderer: `state.nameHints.get(hash) || generateName(depth)` — 1 line
- Producers (makePremises, resolveExistentials): `state.nameHints.set(evarHash, name)` — ~3 lines

## Cross-References

- [TODO_0002](0002_symexec-expression-decision.md) — decision and rationale
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (after this)
- [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) — three isolated problems, theoretical foundations
- [RES_0021](../research/0021_fresh-variable-generation.md) — fresh variable survey (8 systems, Celf/Lean/Coq/Isabelle)
- [RES_0007](../research/0007_chr-linear-logic.md) §2.5 — QCHR framework, ω_l^{∃∀}
- [THY_0001](../theory/0001_exhaustive-forward-chaining.md) — exhaustive forward chaining, Q1 existentials
