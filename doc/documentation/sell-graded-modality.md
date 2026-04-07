# SELL Graded Modality Implementation

How the parameterized bang `!_a` with {0,1,ω} semiring works in code.

## Grade Constants

`lib/engine/grades.js` defines the two explicit grade atoms:

```js
GRADE_0 = Store.put('atom', ['g0'])   // compile-time (composed away)
GRADE_W = Store.put('atom', ['gw'])   // persistent (weakening + contraction)
```

Grade-1 (linear) is **implicit** — a bare formula without a bang wrapper. No `GRADE_1` constant exists in the store tree.

Grades are content-addressed atoms: O(1) equality via hash comparison. The `Store.onClear()` hook re-registers them after store resets so destructured captures (`const { GRADE_0, GRADE_W } = require('./grades')`) remain valid.

## Bang Arity

Bang is arity-2: `bang(grade, formula)`.

```
bang(gw, A)  =  !A   =  !_ω A   (persistent)
bang(g0, A)  =  !_0 A            (compile-time)
```

Defined in `calculus/ill/ill.calc`:
```
grade : type.
bang: grade -> formula -> formula
```

And `lib/engine/ill/connectives.js`: `bang: { category: 'exponential', arity: 2 }`.

## Parser

`lib/parser/earley-grammar.js` hardcodes three grammar rules for bang (since arity-2 doesn't fit the standard unary-prefix pattern):

| Syntax | Emitted AST |
|--------|-------------|
| `!A` | `bang(GRADE_W, A)` |
| `!_0 A` | `bang(GRADE_0, A)` |
| `!_ω A` | `bang(GRADE_W, A)` |

`!_0` and `!_ω` are registered as operator tokens (longest-match lexing). Bare `!` defaults to grade ω for backward compatibility.

## Compilation: Three-Way Grade Classification

`lib/engine/compile.js:flattenAntecedent()` classifies bang-wrapped formulas into three buckets:

```
bang(GRADE_0, X) → grade0[]
bang(GRADE_W, X) → persistent[]
bare formula     → linear[]
```

Returns `{ linear: number[], persistent: number[], grade0: number[] }`.

The same classification applies in `expandChoiceItem()` for consequent expansion through additive choices.

## hasGrade0 Flag

`compile.js:compileRule()` sets `hasGrade0: true` on any compiled rule whose antecedent or any consequent alternative contains grade-0 patterns. This is a compile-time flag — no runtime cost.

## Runtime Filtering

`lib/engine/index.js:filterRules()` excludes grade-0 rules before runtime execution:

```js
rules = rules.filter(r => !r.hasGrade0);
```

This runs once per `exec()`/`explore()` call, before the filtered array is passed to the generic engine. Grade-0 rules are compile-time only — they are composed away by `compose.js` before reaching the runtime filter. See `doc/documentation/grade0-composition.md`.

## Store Stability

Grade constants are content-addressed hashes that depend on store state. The `Store.onClear()` hook in `grades.js` ensures constants are re-registered immediately after `Store.clear()`, getting stable IDs (1 and 2) because the hook fires first.

This matters for binary cache deserialization: `Store.restore()` calls `Store.clear()` internally, which triggers the hook, so grade constants are always valid after cache load.

## CACHE_VERSION

`lib/engine/index.js` defines `CACHE_VERSION = 2` (bumped from 1 when bang changed from arity-1 to arity-2). This invalidates stale binary caches that were compiled with the old arity. The version is mixed into the content hash of the import tree.

## Display

`lib/engine/show.js` inspects `child(0)` of a bang node to determine the grade:

- `child(0) === GRADE_0` → displays as `!_0 X`
- otherwise → displays as `!X` (standard notation)

## Backward Prover

No changes to `calculus/ill/ill.rules`. The rules use `!A` syntax, which the parser emits as `bang(GRADE_W, A)`. The rule-interpreter works generically on child indices derived from arity. Promotion, dereliction, absorption, and copy all work unchanged.

## Theory

This is SELL (Nigam-Miller PPDP 2009) with label set = QTT semiring {0,1,ω} and partial order {0 ≤ ω, 1 ≤ ω, 0 ∥ 1} (V-shape):

| Grade | Structural rules | Promotion context |
|-------|-----------------|-------------------|
| ω | weakening + contraction | all (≤ ω = everything) |
| 1 | none | grade-1 only |
| 0 | weakening + contraction | grade-0 only |

See THY_0015 for the grade-0 staging interpretation and stratified cut elimination.

## Files

| File | Role |
|------|------|
| `lib/engine/grades.js` | Grade constants + Store.onClear() stability |
| `lib/engine/compile.js` | flattenAntecedent 3-way split, hasGrade0 flag |
| `lib/engine/compose.js` | Grade-0 cut elimination (compose pass) |
| `lib/engine/index.js` | filterRules grade-0 exclusion, compose integration, CACHE_VERSION |
| `lib/engine/show.js` | Grade-aware bang display |
| `lib/engine/convert.js` | desugarPreserved child(1), decomposeQuery child(1) |
| `lib/engine/ill/connectives.js` | bang arity: 2 |
| `lib/engine/ill/backchain-ill.js` | GRADE_W in buildClauseTerm |
| `lib/engine/ill/loli-drain.js` | GRADE_W in isAllPersistentAntecedent |
| `lib/parser/earley-grammar.js` | Hardcoded !, !_0, !_ω grammar rules |
| `lib/calculus/builders.js` | deriveRoles arity === 2 detection |
| `calculus/ill/ill.calc` | grade type, bang: grade -> formula -> formula |
| `tests/engine/sell.test.js` | SELL graded modality test suite |
