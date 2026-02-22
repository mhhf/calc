---
title: "Add ∃ and ∀ Quantifiers to CALC — Full First-Class Support"
created: 2026-02-18
modified: 2026-02-22
summary: "Add explicit existential and universal quantifiers as proper first-class connectives: de Bruijn binders, alpha-equivalence, unification, backward prover, focusing, forward engine eigenvariables — sound and complete"
tags: [symexec, existential, universal, eigenvariable, clf, implementation, de-bruijn]
type: implementation
cluster: Symexec
status: done
priority: 9
depends_on: []
required_by: [TODO_0005]
---

# Add ∃ and ∀ Quantifiers to CALC

Decided in [TODO_0002](0002_symexec-expression-decision.md): explicit ∃ with eigenvariables and eager resolution. ∀ added in the same leg — shared de Bruijn infrastructure, ~25 LOC incremental, completes first-order linear logic (MALL₁).

**Polarity:** ∃ is **positive** (like ⊗, 1, ⊕), ∀ is **negative** (like ⊸, &). Duality: ∃ is to ⊕ as ∀ is to &.

**Forward engine:** Only ∃ appears inside the monad `{A}` (positive). ∀ is negative — quantifies over rule variables at the outer level (already implicit). No forward engine changes for ∀.

**Arity:** Store representation is arity-1 (`Store.put('exists', [body])`). Grammar syntax is arity-2 (`exists X. body`). Parser closes: named variable → `bound(0)` in body. Renderer opens: generates fresh display name, substitutes via `debruijnSubst`.

## Implementation Status

| Phase | Status | Notes |
|-------|--------|-------|
| 1. Store Foundation | **done** | `bound`, `exists`, `forall`, `evar` tags; `debruijnSubst`; `fresh.js` |
| 2. Grammar & Parser | **done** | grammar, cst-to-ast, convert.js binder stack, ill.calc declarations |
| 3. Unification | **done** | No changes needed (locally nameless) |
| 4. Sequent Rules | **done** | ill.rules, rules2-parser `@binding`, rule-interpreter `makePremises` |
| 5. Focusing | **done** | Polarity verified via tests |
| 6. Backward Prover | **done** | Works via rule-interpreter `makePremises` + focusing |
| 7. Forward Engine | **done** | `expandItem` + compile-time analysis + `resolveExistentials` three-level fallback via `provePersistentGoals` |
| 8. EVM Restructuring | **done** | 12 rules restructured with `exists`; 210 nodes, 4 STOP, matches master |
| 9. Tests | **done** | 557 tests pass; Store, parser, backward prover, forward engine, integration |

### Bugs Found During Phase 7/8 Attempt

**Bug 1 — Loli variables classified as existential slots:** `compileRule` walked into loli patterns collecting metavars, treating loli-only variables (e.g. `Z` in `unblockConcatMemory Z -o {...}`) as existential. `resolveExistentials` bound them to `evar(N)`, making loli triggers unmatchable. **Fix:** Track `loliMetavars` separately, exclude from `existentialSlots`.

**Bug 2 — resolveExistentials only does FFI (level 1 of 3):** The spec says: FFI → state lookup → backward chaining → freshEvar fallback. Implementation only tries FFI, then rejects. EVM predicates like `gt`, `and`, `or` have backward chaining clauses for symbolic decomposition (e.g. `gt/s_ii` does bit-level case splitting). FFI-only resolution rejects these, causing 0 STOP leaves. **Fix:** Reuse `provePersistentGoals` which already implements the full three-level fallback.

**Bug 3 — Deterministic metavar naming:** `rule-interpreter.js` used `Date.now() + Math.random()` for ∃R/∀L metavars — nondeterministic. **Fix:** Replaced with monotonic counter `freshMetavar()`.

**Bug 4 — Existential goal dependency ordering:** `resolveExistentials` collected goals by iterating `existentialSlots` (Set insertion order), which didn't respect dependency chains. For `evm/gt`: `to256(Z,Z')` was tried before `gt(X,Y,0,Z)`, so Z was unbound when to256 needed it. **Fix:** Collect goals from `rule.consequent.persistent` (preserves .ill syntax order = dependency order).

## TODO_0004.Phase_1 — Store Foundation: Locally Nameless Binders

Bound variables are de Bruijn indices (`bound(0)`), free variables keep their Store hashes unchanged. Alpha-equivalence for free: `∃X.p(X)` and `∃Y.p(Y)` get the same hash. No shifting needed for free variables under substitution (Aydemir et al. 2008, §2.3).

- [x] New Store tag `bound`: `Store.put('bound', [index])` — de Bruijn index (add to `BIGINT_CHILD_TAGS`)
- [x] New Store tag `exists`: `Store.put('exists', [body])` — arity-1, body uses `bound(0)`
- [x] New Store tag `forall`: `Store.put('forall', [body])` — same representation as `exists`
- [x] New Store tag `evar`: `Store.put('evar', [N])` — fresh eigenvariable (add to `BIGINT_CHILD_TAGS`)
- [x] `lib/kernel/fresh.js`: monotonic counter. `freshEvar()` → `Store.put('evar', [next++])`. `resetFresh()` for tests.
- [x] `debruijnSubst(bodyHash, index, replacement)` in `lib/kernel/substitute.js`
- [ ] `state.nameHints: Map<hash, string>` — deferred (display-only, not blocking)
- [x] Tests: `tests/store-quantifiers.test.js` — alpha-equivalence, substitution, nested binders

## TODO_0004.Phase_2 — Grammar and Parser

- [x] Grammar: `expr_exists` / `expr_forall` in `lib/tree-sitter-mde/grammar.js`
- [x] Rebuild: `npm run build:ts:wasm`
- [x] CST→AST: `lib/meta-parser/cst-to-ast.js` — quantifier handling
- [x] Program parser (`lib/engine/convert.js`): `binderStack` for de Bruijn encoding
- [x] Rules parser (`lib/rules/rules2-parser.js`): `@binding` annotation extraction
- [x] `ill.calc`: `exists` and `forall` declarations with polarity/precedence
- [ ] Renderer: `@binding quantifier` annotation — deferred (display-only)

## TODO_0004.Phase_3 — Unification and Substitution Under Binders

No shifting needed (locally nameless): `apply(exists(body), θ)` = `exists(apply(body, θ))`. θ maps free variables (hashes) to terms. `bound(k)` is a distinct tag, never in θ. Existing `matchIndexed`/`applyIndexed`/`subCompiled` need zero changes.

**Why this is safe:** If θ[X] = some_term and some_term contains `bound(k)`, that `bound(k)` refers to a binder *within* some_term's own structure, not to the enclosing exists/forall. All Store values are locally closed (no dangling bound vars). This is the core invariant of locally nameless.

**Occurs check:** CALC's `unifyUF()` already has an eager occurs check (`occursInUF()`, unify.js line 264). No changes needed — prevents `X = f(X)` circularity when unifying quantified formulas.

- [x] No changes needed — locally nameless means `exists`/`forall` are structural nodes, `bound(k)` is a leaf. `matchIndexed`/`applyIndexed`/`subCompiled` work unchanged.
- [x] Tests: backward prover tests verify unification through quantified formulas

## TODO_0004.Phase_4 — ill.rules: Sequent Rules

**∃ rules:**
- [ ] ∃R: `G ; D |- exists x . B  <-  G ; D |- B[t/x]` — provide witness (non-invertible)
- [ ] ∃L: `G ; D, exists x . B |- C  <-  G ; D, B[a/x] |- C` — eigenvariable (invertible)

**∀ rules:**
- [ ] ∀R: `G ; D |- forall x . B  <-  G ; D |- B[a/x]` — eigenvariable (invertible)
- [ ] ∀L: `G ; D, forall x . B |- C  <-  G ; D, B[t/x] |- C` — instantiate (non-invertible)

**Symmetry:** ∃L ↔ ∀R (eigenvariable), ∃R ↔ ∀L (choose term).

- [x] Rules with `@binding eigenvariable` (∃L, ∀R) / `@binding metavar` (∃R, ∀L) in `ill.rules`
- [x] `@polarity positive` on ∃ in `ill.calc`
- [x] `binding` field on descriptor via `rules2-parser.js`
- [x] Rule interpreter `makePremises` — reads `binding`, opens binder with `freshEvar()` or `freshMetavar()`:

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

- [x] `npm run build:bundle` — ∃/∀ in `out/ill.json`

## TODO_0004.Phase_5 — Focusing

No code changes needed in `focusing.js` — it reads descriptors and explicit polarity, both already set in Phase 4. `findInvertible` and `chooseFocus` dispatch on polarity metadata, not on hardcoded connective names.

- [x] Verified via `tests/quantifiers.test.js`: `exists` positive, `forall` negative
- [x] Invertibility: `exists_l` invertible, `exists_r` non-invertible; `forall_r` invertible, `forall_l` non-invertible

**Eigenvariable safety in backward prover:** The eigenvariable condition (fresh name must not appear in conclusion) is automatic in locally nameless. Fresh evars are created during proof search and are fresh by construction (monotonic counter). `applyRule` returns `theta: []` for structural rules — no substitution flows back to the conclusion. Eigenvariable leakage is structurally impossible.

## TODO_0004.Phase_6 — Backward Prover

Handled via rule-interpreter `makePremises` with `@binding` annotations. No changes to `generic.js` needed — the descriptor-driven architecture dispatches automatically.

- [x] ∃L/∀R: `debruijnSubst(body, 0n, freshEvar())` via `makePremises` when `d.binding === 'eigenvariable'`
- [x] ∃R/∀L: `debruijnSubst(body, 0n, freshMetavar())` via `makePremises` when `d.binding === 'metavar'`
- [x] Tests: `tests/quantifiers.test.js` — identity, ∃-introduction, ∀-elimination, invertibility
- [ ] Manual prover: expose witness choice for ∃R/∀L to user — deferred
- [ ] Witness strategy for auto prover — deferred (current approach: fresh metavar + unification)

## TODO_0004.Phase_7 — Forward Engine: ∃ Decomposition + Eager Resolution

Only ∃ — ∀ is negative, doesn't appear inside `{A}`.

### Compile-time: expandItem

**Key insight** (from [TODO_0002](0002_symexec-expression-decision.md)): ∃ in rule consequents is immediately decomposed by `expandItem` at compile time. It never persists as a formula in state. ∃-bound variables are just metavar slots not matched by any antecedent — existing `metavarSlots` infrastructure suffices.

- [x] `expandItem` case for `exists` in `compile.js` — opens binder with fresh `_exN` metavar
- [x] `existentialSlots` detection in `compileRule` — metavars in consequent but NOT in antecedent
- [x] Loli variable exclusion — loli-only metavars excluded from existentialSlots (bug fix)
- [x] `existentialGoals` mapping — existential slot → persistent consequent patterns

### Runtime: eager resolution (between tryMatch and mutateState)

After `tryMatch` binds antecedent vars, existential slots are unbound. Resolve them before committing:

```
tryMatch completes → antecedent vars bound, ∃-slots unbound
  ↓
for each unbound existential slot:
  collect persistent consequent patterns that use this slot
  call provePersistentGoals(patterns, ..., theta, slots, state, calc)
    → FFI direct       → succeeds: bind slot to concrete result
    → state lookup     → succeeds: bind slot
    → backward proving → succeeds: bind slot (critical for gt/and/or/not!)
  all fail → bind slot to freshEvar(), pattern becomes symbolic constraint
  ↓
mutateState (all slots now bound)
```

- [x] Integration point in `tryMatch` — calls `resolveExistentials` after persistent proof, before returning match
- [x] `resolveExistentials` uses `provePersistentGoals` (three-level fallback: FFI → state → backward chaining → freshEvar)

**Ground execution:** FFI succeeds immediately for all 11 EVM arithmetic rules → concrete value → zero overhead vs current behavior. Evars never enter state.

**Symbolic execution:** FFI fails → evar created → persistent constraint `!plus(A, B, evar(N))` emitted to state. Execution continues.

- [x] Counter is monotonic (no undo). `fork(n)` for future parallel symexec.

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

- [x] Rewrite 12 rules in evm.ill (add, mul, sub, exp, lt, gt, and, or, not, concatMemory/s, calldatacopy/s, evm/calldatacopy)
- [x] Verify ground execution unchanged (same FFI path, same results)
- [x] Verify symbolic execution: tree shape matches master (210 nodes, 19 leaves, 4 STOP)
- [x] Symexec benchmark: 4.92ms median (-14% vs baseline)

## TODO_0004.Phase_9 — Tests

- [x] Store: de Bruijn, alpha-equivalence, `debruijnSubst`, mixed nested binders (`tests/store-quantifiers.test.js`)
- [x] Parser: `exists X. A` / `forall X. A` de Bruijn encoding (`tests/quantifiers.test.js`)
- [x] Backward prover: identity, ∃-intro, ∀-elim, invertibility (`tests/quantifiers.test.js`)
- [x] Forward engine: `expandItem` with ∃, existential slot detection, loli exclusion (`tests/quantifiers.test.js`)
- [x] Polarity: exists positive, forall negative (`tests/quantifiers.test.js`)
- [x] Regression: all 557 tests pass
- [x] Integration: EVM multisig with ∃-restructured rules, full three-level resolution
- [ ] Integration: symbolic ADD chain, branching (⊕ + ∃), evar accumulation

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
