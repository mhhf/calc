---
title: "Grade-0 Cut Elimination — Compile-Time Composition"
created: 2026-04-07
modified: 2026-04-07
summary: How the compose pass eliminates grade-0 intermediate types at compile time, producing specialized rules via cut elimination.
tags: [cut-elimination, forward-chaining, graded-types, QTT, implementation, architecture]
---

# Grade-0 Cut Elimination

`lib/engine/compose.js` implements compile-time cut elimination for grade-0 intermediate types (`!_0`). Rules connected through grade-0 predicates are composed into specialized rules before runtime. The intermediates disappear — the engine only sees the composed rules.

## Motivation

Factor shared rule preambles into a producer rule that outputs a grade-0 type, consumed by specialized target rules. The compiler glues them together.

```ill
% Producer: shared preamble → grade-0 intermediate
step/make:
  $bytecode BC * pc PC * !arr_get BC PC OP * !inc PC PC'
  -o { !_0 step OP PC' }.

% Consumer: specialized behavior
evm/add: !_0 step 0x01 PC' * stack [A, B | REST]
  -o { pc PC' * ... }.

% Composed result (produced automatically):
evm/add:step/make:
  $bytecode BC * pc PC * !arr_get BC PC 0x01 * !inc PC PC' * stack [A, B | REST]
  -o { pc PC' * ... }.
```

The `!_0` type `step` is a compile-time scaffold — it helps factor rules, then gets eliminated.

## Three-Layer API

```
L1: composePair(producer, consumer, cutPredHead, rc) → rawRule | null
L2: buildPredicateMap(compiledRules) → Map<pred, {producers[], consumers[], bridges[]}>
L3: composeGrade0(compiledRules, connectives) → ComposeResult
```

**L1 — Atomic cut elimination.** Grade-agnostic. One cut step: alpha-rename producer, flatten both sides, locate cut formula, unify, merge with θ applied. Returns a raw rule or null on unification failure. Reused unchanged by v2–v4.

**L2 — Analysis.** Scans compiled rules with `hasGrade0: true`. Classifies each as producer (grade-0 in consequent), consumer (grade-0 in antecedent), or bridge (both). Returns a map keyed by grade-0 predicate head.

**L3 — v1 scheduler.** Validates (no bridges, all predicates have both producers and consumers), iterates N×M pairs per predicate, calls L1, filters residuals, returns `ComposeResult`.

## Pipeline Position

```
Parse → Compile → Compose → Compile² → Filter → Execute
                  (compose.js)
```

In `_buildCalc()` (index.js):
1. First compile: `compileRule()` produces `hasGrade0` flags and `grade0[]` arrays
2. **Compose**: `composeGrade0()` pairs producers with consumers, eliminates grade-0
3. Second compile: composed raw rules go through `compileRule()`
4. Runtime filter: `rules.filter(r => !r.hasGrade0)` excludes original grade-0 rules

Lazy-loaded: `require('./compose')` only executes when grade-0 rules exist. Zero cost otherwise.

## Algorithm (composePair)

Given producer E and consumer T sharing cut formula M:

1. **Alpha-rename E** — fresh metavars via `freshMetavar()` prevent variable capture
2. **Flatten** — `flattenAntecedent` on both sides → `{ linear[], persistent[], grade0[] }`
3. **Locate M** — find M by predicate head in E's consequent `grade0[]` and T's antecedent `grade0[]`
4. **Unify** — `unify(E_output, T_input) → θ` (substitution mapping metavars)
5. **Merge + apply θ** — combine antecedents and consequents, remove M from both
6. **Reassemble** — re-wrap persistent with `!_ω`, residual grade-0 with `!_0`, build loli

Returns `{ name, hash, antecedent, consequent, sourceLabel }` or `null` on unification failure.

## Validation

**Pre-composition (L3):**
- Every grade-0 predicate needs at least one producer AND one consumer
- Bridge rules (consume pred A, produce pred B) rejected in v1 — needs multi-stage (TODO_0158)

**Post-composition (defense-in-depth):**
- Composed rules with grade-0 residuals are filtered out with diagnostic errors
- Catches multi-predicate edge cases (rule produces `!_0 M * !_0 N`)

## Diagnostics

`ComposeResult.diagnostics`:

| Field | Meaning |
|-------|---------|
| `pairsAttempted` | Total (producer, consumer) pairs tried |
| `pairsSucceeded` | Pairs that produced composed rules |
| `pairsSkipped` | Unification failures (normal, not errors) |
| `grade0Predicates` | Predicate names that were composed through |
| `errors` | Validation failures (bridges, missing producers/consumers, residuals) |

## Theory

Each `composePair` call is one cut step on the grade-0 fragment of SELL (Nigam-Miller PPDP 2009). Grade-0 non-interference (Choudhury et al. POPL 2021, Lemma 6.2) guarantees composed rules are observationally equivalent. See THY_0015 for the stratified cut elimination proof.

N producers × M consumers yield N×M composed rules — the grade-0 modality admits contraction (SELL structural rule W=C={0,ω}), so one producer serves many consumers.

## Version Chain

| Version | TODO | What changes |
|---------|------|-------------|
| v1 | TODO_0156 | Single-pass, no bridges. L1 + L2 + L3 |
| v2 | TODO_0158 | Multi-stage DAG composition. Reuses L1 + L2, replaces L3 scheduler |
| v3 | TODO_0159 | Grade-0 persistent facts. New post-compose pass |
| v4 | TODO_0160 | Futamura projection. Demand-driven BFS from entry points |

## Files

| File | Role |
|------|------|
| `lib/engine/compose.js` | Three-layer API: composePair, buildPredicateMap, composeGrade0 |
| `lib/engine/index.js` | Integration: compose pass in `_buildCalc()` |
| `lib/engine/grades.js` | Grade constants (GRADE_0, GRADE_W) |
| `lib/engine/compile.js` | flattenAntecedent 3-way split, hasGrade0 flag |
| `tests/engine/compose.test.js` | 21 tests: L1, L2, L3, integration |
