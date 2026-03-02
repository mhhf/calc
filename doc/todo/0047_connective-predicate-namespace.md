---
title: "Separate connective and predicate tag namespaces"
created: 2026-02-22
modified: 2026-02-22
summary: "Connectives and user-defined predicates shared a flat Store tag namespace. The `plus` connective (⊕) and `plus` predicate (arithmetic) collided. Fixed by renaming connective to `oplus` + structural tag ID boundary."
tags: [store, architecture, qol]
type: design
status: done
priority: 4
cluster: Performance
depends_on: []
required_by: []
---

# Separate Connective and Predicate Tag Namespaces

## Solution: Rename + Tag ID Boundary

Combined Option D (rename) with Option A (numeric boundary):

1. **Renamed connective `plus` → `oplus`** in the Store. User-facing `+` syntax unchanged (via `@ascii "_ + _"`). `oplus` matches the standard mathematical name (LaTeX `\oplus`).

2. **Tag ID boundary** (`Store.PRED_BOUNDARY`): Pre-registered tags (IDs 0–25) are built-in (connectives, structural, quantifiers). Dynamically registered tags (IDs 26+) are user-defined predicates. Replaces the manually-maintained `NON_PRED_TAGS` Set with a numeric comparison.

`getPredicateHead` now uses `Store.tagId(h) >= Store.PRED_BOUNDARY` instead of `!NON_PRED_TAGS.has(t)`. New `isPredTag(tagName)` helper exported from ast.js.

### Bug found during implementation

`Store.tagId()` returns 0 for both invalid IDs and `atom` (tag 0). The initial `getPredicateHead` used `if (!tid)` as guard — this made ALL atoms return null. Fix: use `Store.isTerm(h)` for validity, then numeric comparison for classification.

### Files changed

- `calculus/ill/ill.calc` — constructor `plus` → `oplus`
- `calculus/ill/ill.rules` — rules `plus_r1/r2/l` → `oplus_r1/r2/l`
- `lib/kernel/store.js` — pre-register `oplus`, export `PRED_BOUNDARY`
- `lib/kernel/ast.js` — replace `NON_PRED_TAGS` Set with `isPredTag()` + boundary check
- `lib/engine/convert.js` — `Store.put('oplus', ...)`
- `lib/engine/compile.js` — `t === 'oplus'` in expandChoiceItem
- `lib/engine/forward.js` — `isPredTag()` in tryFFIDirect
- `lib/engine/prove.js` — `isPredTag()` in getFirstArgHead, getArgs
- `lib/meta-parser/cst-to-ast.js` — `'expr_plus': 'oplus'`
- Tests: explore.test.js, tree-sitter.js
- `out/ill.json` — regenerated

## Original Problem

Store tags were a flat namespace. Connectives and user-defined predicates shared it:

- `plus` (⊕, arity 2): ILL internal choice connective — `Store.put('plus', [A, B])`
- `plus` (arithmetic, arity 3): user predicate — `Store.put('plus', [X, Y, Z])`

`getPredicateHead` returned `'plus'` for both. `NON_PRED_TAGS` couldn't include `'plus'` without breaking FFI resolution for arithmetic. If ⊕ appeared as a bare fact in state, `buildStateIndex` would index it alongside arithmetic `plus` facts.
