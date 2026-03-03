---
title: "Type Checking — Enforce LF-Style Type Declarations"
created: 2026-03-03
modified: 2026-03-03
summary: "CALC has LF-style type declarations (bin: type, plus: bin -> bin -> bin -> type) but doesn't check them. Implement actual type checking to catch malformed rules and programs."
tags: [type-checking, type-system, lf, sort-system, error-detection, architecture, implementation, content-addressing]
type: implementation
status: done
priority: 7
cluster: Theory
depends_on: []
required_by: [TODO_0011, TODO_0064]
starred: true
---

# Type Checking — Enforce LF-Style Type Declarations

## Problem

CALC's .ill files declare types in LF syntax:

```ill
bin: type.
e: bin.
i: bin -> bin.
plus: bin -> bin -> bin -> type.
plus/z1: plus e e e.
```

But NOTHING enforces these. The loader reads them only for parser generation (constructor names, arities) and tag assignment. You can write `plus empty_mem (bit0 z) X` and CALC happily tries to match it — failing silently because no clause pattern matches, not because of a type error.

## Goal

Enforce type declarations at rule compilation time. Catch malformed rules/programs before execution, not as silent matching failures. Zero runtime cost — all checking happens once at load time.

## Existing Infrastructure

### What the Loader Already Extracts

`convert.loadFile()` populates a `types` Map from declarations without premises or monads:

```javascript
types = Map {
  'bin'  → hash_of(type),                         // bin: type
  'e'    → hash_of(atom('bin')),                   // e: bin
  'o'    → hash_of(arrow(atom('bin'), atom('bin'))), // o: bin -> bin
  'plus' → hash_of(arrow(bin, arrow(bin, arrow(bin, type)))), // plus: bin -> bin -> bin -> type
  'plus/z1' → hash_of(tag_plus(e, e, e)),          // plus/z1: plus e e e  (axiom, not a type sig)
}
```

Type signatures are arrow chains in the Store. Axioms are predicate applications. We can distinguish them by walking the Store structure.

### What's Available But Unused

| Data | Where | Status |
|---|---|---|
| `types` Map (name → hash) | `convert.loadFile` output | Preserved but unused after compile |
| Arrow-chain structure | Store (tag `arrow`, children are left/right) | Walkable via `Store.tag`/`Store.child` |
| Constructor arities | `Store.arity(hash)` | Available at any time |
| Predicate head | `getPredicateHead(h)` in `ast.js` | Works for atoms + pred tags |
| `isGround`, `collectMetavars` | `pattern-utils.js` | Available |

### How Terms Appear in the Engine

Two representations for predicates:
- **Nullary:** `atom('stop')` — tag `atom`, child is string `'stop'`
- **With args:** `tag_plus(X, Y, Z)` — tag `plus` (ID ≥ `PRED_BOUNDARY`), children are term hashes

Constructors and predicates share the same tag namespace (IDs ≥ 26). The Store doesn't distinguish them — the distinction is at the type level (constructors return a base type, predicates return `type`).

---

## Architecture

### New Module: `lib/engine/type-check.js`

Single module, pure functions, no side effects. ~400 LOC total across all stages.

```
types Map (from convert.js)
    ↓
buildSortTable(types)          ← O(T), one-time, ~50 LOC
    ↓
sortTable: { baseTypes, signatures }
    ↓
checkForwardRule(rule, sortTable)  ← O(n) per rule
checkClause(name, hash, premises, sortTable)
    ↓
issues: [{ rule, kind, message }]
```

### Sort Table Structure

```javascript
{
  baseTypes: Set(['bin', 'nat', 'bool', 'mem', ...]),
  signatures: Map {
    'e':    { arity: 0, argTypes: [],                returnType: 'bin' },
    'i':    { arity: 1, argTypes: ['bin'],            returnType: 'bin' },
    'o':    { arity: 1, argTypes: ['bin'],            returnType: 'bin' },
    'plus': { arity: 3, argTypes: ['bin','bin','bin'], returnType: 'type' },
    'pc':   { arity: 1, argTypes: ['bin'],            returnType: 'type' },
    'stop': { arity: 0, argTypes: [],                returnType: 'type' },
    'write':{ arity: 3, argTypes: ['bin','bin','bin'], returnType: 'bin' },
    // ...
  }
}
```

Built once from `types` Map by walking arrow chains in the Store. Entries whose body hash isn't an arrow chain or base type reference (i.e., axioms like `plus/z1: plus e e e`) are skipped.

### Sort Table Construction Algorithm

```javascript
function buildSortTable(types) {
  const baseTypes = new Set();
  const signatures = new Map();

  for (const [name, hash] of types) {
    const sig = parseTypeSignature(hash);
    if (!sig) continue;  // axiom or unparseable — skip

    if (sig.returnType === 'type' && sig.argTypes.length === 0) {
      baseTypes.add(name);  // bin: type → base type
    } else {
      signatures.set(name, {
        arity: sig.argTypes.length,
        argTypes: sig.argTypes,
        returnType: sig.returnType
      });
    }
  }
  return { baseTypes, signatures };
}

function parseTypeSignature(hash) {
  const tag = Store.tag(hash);
  if (tag === 'arrow') {
    // Walk: arrow(atom('bin'), arrow(atom('bin'), atom('type')))
    //   → argTypes: ['bin', 'bin'], returnType: 'type'
    const argTypes = [];
    let cur = hash;
    while (Store.isTerm(cur) && Store.tag(cur) === 'arrow') {
      const left = Store.child(cur, 0);
      const typeName = extractTypeName(left);
      if (typeName === null) return null;  // complex type expr — not a simple sig
      argTypes.push(typeName);
      cur = Store.child(cur, 1);
    }
    const ret = extractTypeName(cur);
    return ret ? { argTypes, returnType: ret } : null;
  }
  if (tag === 'type') return { argTypes: [], returnType: 'type' };
  if (tag === 'atom') return { argTypes: [], returnType: Store.child(hash, 0) };
  return null;  // predicate application or other — not a type sig
}

function extractTypeName(hash) {
  const tag = Store.tag(hash);
  if (tag === 'atom') return Store.child(hash, 0);  // atom('bin') → 'bin'
  if (tag === 'type') return 'type';
  return null;
}
```

### Integration Point: `lib/engine/index.js` → `_buildCalc()`

After rule compilation, before returning `calc`:

```javascript
function _buildCalc(types, clauses, forwardRules, queries, opts = {}) {
  const compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r));
  // ... existing persistent step regeneration ...

  // Type checking (always runs, <1ms for 73 EVM rules)
  const { buildSortTable, checkAll } = require('./type-check');
  const sortTable = buildSortTable(types);
  const typeIssues = checkAll(compiledRules, clauses, sortTable);

  if (typeIssues.arity.length > 0) {
    throw new TypeError(
      `Arity errors:\n${typeIssues.arity.map(i => `  ${i.rule}: ${i.message}`).join('\n')}`
    );
  }
  // Sort issues: warn for now, hard error with opts.strictTypes
  if (typeIssues.sort.length > 0 && opts.strictTypes) {
    throw new TypeError(
      `Sort errors:\n${typeIssues.sort.map(i => `  ${i.rule}: ${i.message}`).join('\n')}`
    );
  }

  return { types, clauses, queries, forwardRules: compiledRules, sortTable, typeIssues, ... };
}
```

### Sort Inference for Arbitrary Terms

```javascript
function inferSort(hash, sortTable) {
  if (!Store.isTerm(hash)) return null;
  const tag = Store.tag(hash);

  // Metavar — unconstrained
  if (tag === 'freevar') return null;

  // Built-in literals
  if (tag === 'binlit') return 'bin';  // ephemeral-expands to o/i/e
  if (tag === 'strlit') return 'string';
  if (tag === 'charlit') return 'char';

  // Built-in connectives → formula
  if (['tensor','loli','with','oplus','bang','one','zero','exists','forall','atom'].includes(tag))
    return 'formula';

  // User-defined constructors/predicates
  const sig = sortTable.signatures.get(tag);
  return sig ? sig.returnType : null;  // null = undeclared
}
```

---

## Stages

### TODO_0065.Stage_1 — Sort Table + Arity Checking (~120 LOC)

**What:** Build sort table from `types` Map. Check every predicate/constructor application has correct argument count. Recursive — checks nested subterms.

**Algorithm:**

```javascript
function checkTermArity(hash, sortTable, issues, ruleName) {
  if (!Store.isTerm(hash)) return;
  const tag = Store.tag(hash);
  if (!tag || tag === 'freevar') return;
  if (['binlit','strlit','charlit'].includes(tag)) return;

  // Look up signature
  let sig = null, predName = null;
  if (tag === 'atom') {
    // Nullary atom — check it's not declared with args
    predName = Store.child(hash, 0);
    sig = sortTable.signatures.get(predName);
    if (sig && sig.arity > 0) {
      issues.push({ rule: ruleName, kind: 'arity', pred: predName,
        expected: sig.arity, actual: 0,
        message: `${predName} expects ${sig.arity} args, used as nullary atom` });
    }
    return;  // atom has no term children
  }
  if (Store.tagId(hash) >= Store.PRED_BOUNDARY) {
    predName = tag;
    sig = sortTable.signatures.get(tag);
  }

  if (sig) {
    const actual = Store.arity(hash);
    if (actual !== sig.arity) {
      issues.push({ rule: ruleName, kind: 'arity', pred: predName,
        expected: sig.arity, actual,
        message: `${predName} expects ${sig.arity} args, got ${actual}` });
    }
  }

  // Recurse into children
  for (let i = 0; i < Store.arity(hash); i++) {
    const c = Store.child(hash, i);
    if (Store.isTermChild(c)) checkTermArity(c, sortTable, issues, ruleName);
  }
}
```

**What it catches:**
- `plus e e` → "plus expects 3 args, got 2"
- `i e e` → "i expects 1 args, got 2"
- Nullary atom used for declared-with-args predicate

**Integration:** Called from `checkForwardRule()` and `checkClause()`.

**Error severity:** Hard error (arity mismatches are always bugs).

**Files touched:**
- NEW: `lib/engine/type-check.js` (~120 LOC)
- EDIT: `lib/engine/index.js` — add `buildSortTable` + `checkAll` call in `_buildCalc`

**Tests:**
- `tests/engine/type-check.test.js` (new file)
- Positive: well-typed EVM rules pass
- Negative: hand-crafted arity mismatches caught
- Edge: nullary predicates, built-in connectives, metavar-only patterns

---

### TODO_0065.Stage_2 — Sort Checking (~150 LOC, cumulative ~270 LOC)

**What:** For every ground subterm, check its inferred sort matches the expected sort from the parent's type signature. For metavars, infer sort from context and check consistency across the rule.

**Algorithm — ground sort checking:**

```javascript
function checkTermSort(hash, expectedSort, sortTable, issues, ruleName) {
  if (!Store.isTerm(hash)) return;
  const tag = Store.tag(hash);

  // Metavar — record expected sort, check consistency
  if (tag === 'freevar') {
    if (Store.child(hash, 0)?.startsWith('_') && expectedSort) {
      recordMetavarSort(hash, expectedSort, issues, ruleName);
    }
    return;
  }

  // Infer sort of this term
  const inferred = inferSort(hash, sortTable);
  if (inferred && expectedSort && inferred !== expectedSort) {
    issues.push({ rule: ruleName, kind: 'sort',
      message: `expected ${expectedSort}, got ${inferred} (${Store.tag(hash)})` });
  }

  // Recurse: check children against parent's expected arg types
  const sig = sortTable.signatures.get(tag);
  if (sig) {
    for (let i = 0; i < Math.min(Store.arity(hash), sig.argTypes.length); i++) {
      const child = Store.child(hash, i);
      if (Store.isTermChild(child)) {
        checkTermSort(child, sig.argTypes[i], sortTable, issues, ruleName);
      }
    }
  }
}
```

**Algorithm — metavar sort consistency:**

```javascript
// Per-rule Map<metavarHash, expectedSort>
const metavarSorts = new Map();

function recordMetavarSort(hash, expectedSort, issues, ruleName) {
  const existing = metavarSorts.get(hash);
  if (existing && existing !== expectedSort) {
    const name = Store.child(hash, 0);
    issues.push({ rule: ruleName, kind: 'sort-conflict',
      message: `metavar ${name} used as both ${existing} and ${expectedSort}` });
  } else {
    metavarSorts.set(hash, expectedSort);
  }
}
```

**What it catches:**
- `plus empty_mem e e` → "expected bin, got bin" only if `empty_mem` returns wrong type (it returns `bin`, so this actually passes — the memory write-log IS encoded as `bin`)
- `stack A B` where A is bound as `bin` elsewhere but `stack` expects `nat` → sort conflict on metavar
- `code PC (o e)` → arg 1 of `code` expects `bin`, `o e` returns `bin` ✓ (no error)

**Error severity:** Warnings initially (promote to errors after verifying all existing programs pass).

**Files touched:**
- EDIT: `lib/engine/type-check.js` — add `checkTermSort`, `recordMetavarSort`, `inferSort`

**Tests:**
- Positive: `plus (o M) (i N) R` — all bin ✓
- Negative: hand-crafted sort mismatches
- Metavar consistency: M used as bin in antecedent, same M used as nat in consequent → conflict

---

### TODO_0065.Stage_3 — Cross-Rule Type Consistency (~80 LOC, cumulative ~350 LOC)

**What:** Check that metavar sorts flow correctly from antecedent to consequent in forward rules. Check existential variable sorts. Check loli consequent patterns.

**Algorithm:**

```javascript
function checkForwardRule(compiledRule, sortTable) {
  const issues = [];
  const metavarSorts = new Map();

  // Phase 1: Check antecedent patterns (bind metavar sorts)
  const ante = compiledRule.antecedent;
  for (const h of ante.linear) {
    checkTermArity(h, sortTable, issues, compiledRule.name);
    checkTermSort(h, null, sortTable, issues, compiledRule.name, metavarSorts);
  }
  for (const h of ante.persistent) {
    checkTermArity(h, sortTable, issues, compiledRule.name);
    checkTermSort(h, null, sortTable, issues, compiledRule.name, metavarSorts);
  }

  // Phase 2: Check consequent patterns (verify metavar sorts match)
  for (const alt of compiledRule.consequentAlts || [compiledRule.consequent]) {
    for (const h of (alt.linear || [])) {
      checkTermArity(h, sortTable, issues, compiledRule.name);
      checkTermSort(h, null, sortTable, issues, compiledRule.name, metavarSorts);
    }
    for (const h of (alt.persistent || [])) {
      checkTermArity(h, sortTable, issues, compiledRule.name);
      checkTermSort(h, null, sortTable, issues, compiledRule.name, metavarSorts);
    }
  }

  return issues;
}
```

**What it catches:**
- Metavar bound as `bin` in antecedent, used where `nat` is expected in consequent
- Existential variable introduced in wrong-sort position
- Consequent pattern with wrong arity (same as Stage 1, but for produced facts)

**Error severity:** Same as sort checking — warnings upgradeable to errors.

**Files touched:**
- EDIT: `lib/engine/type-check.js` — add `checkForwardRule` orchestrator

**Tests:**
- Existing EVM rules all pass (regression)
- Hand-crafted rule with antecedent binding M as `bin`, consequent using M where `nat` expected

---

### TODO_0065.Stage_4 — Backward Clause Checking (~50 LOC, cumulative ~400 LOC)

**What:** Check backward clauses (`<-` syntax) for arity and sort correctness.

**Algorithm:**

```javascript
function checkClause(name, clauseData, sortTable) {
  const issues = [];
  // Check clause head
  checkTermArity(clauseData.hash, sortTable, issues, name);
  checkTermSort(clauseData.hash, null, sortTable, issues, name, new Map());

  // Check each premise
  for (const premise of clauseData.premises) {
    checkTermArity(premise, sortTable, issues, name);
    checkTermSort(premise, null, sortTable, issues, name, new Map());
  }
  return issues;
}
```

**What it catches:**
- Clause with wrong arity in head: `plus/bad: plus e e` (2 args, expected 3)
- Clause premise with sort mismatch: `inc/bad: inc (o M) N <- plus M N Q` where Q has no type constraint but plus expects 3 bin args

**Files touched:**
- EDIT: `lib/engine/type-check.js` — add `checkClause`

**Tests:**
- Existing bin.ill clauses all pass
- Hand-crafted malformed clauses caught

---

## The `checkAll` Entry Point

```javascript
function checkAll(forwardRules, clauses, sortTable) {
  const arity = [], sort = [], consistency = [];

  for (const rule of forwardRules) {
    const issues = checkForwardRule(rule, sortTable);
    for (const i of issues) {
      (i.kind === 'arity' ? arity : i.kind === 'sort-conflict' ? consistency : sort).push(i);
    }
  }

  for (const [name, clause] of clauses) {
    const issues = checkClause(name, clause, sortTable);
    for (const i of issues) {
      (i.kind === 'arity' ? arity : sort).push(i);
    }
  }

  return { arity, sort, consistency };
}
```

---

## Edge Cases & Gotchas

### 1. Atoms vs Pred Tags

Nullary predicates appear as `atom('stop')` (tag `atom`). Predicates with args appear as `tag_plus(X,Y,Z)` (tag `plus`, ID ≥ 26). The sort table keys by name — `checkTermArity` handles both representations: atom-child lookup for nullary, tag-name lookup for others.

### 2. `binlit` Ephemeral Expansion

`binlit(42n)` has sort `bin` (it unifies with `o`/`i`/`e` structure via ephemeral expansion). The sort inferrer returns `'bin'` for `binlit` unconditionally.

### 3. Axioms in the Types Map

`convert.loadFile` puts BOTH type signatures AND axioms into `types`. E.g., `plus/z1: plus e e e` (no premises, no monad) → types. `parseTypeSignature` returns null for predicate applications, filtering them out. Only arrow chains and base type refs become sort table entries.

### 4. Undeclared Predicates

Some predicates might lack type declarations (declared by usage only). `checkTermArity` skips terms whose tag isn't in the sort table (sig === null). No false positives from undeclared predicates.

### 5. Built-in Connectives

`tensor`, `loli`, `with`, `oplus`, `bang`, `one`, `zero` — arities enforced by the parser and Store. The type checker skips them (tag ID < PRED_BOUNDARY, except `atom`). No redundant checking.

### 6. `exists` in Consequent

Forward rules with `exists C. (...)` are expanded in compile.js Phase E before we see them. The compiled rule has concrete metavar references (freshened freevars). Type checking works on the post-expansion form — exists binders are transparent.

### 7. Multiple Consequent Alternatives

Rules with `oplus`/`with` expand to `compiledRule.consequentAlts`. Each alternative is checked independently.

### 8. Loli in Consequent

Rules producing loli facts (`... -o { A -o B }`) create forward sub-rules. These appear as `loli(A, B)` in consequent patterns. For Stage 3, we check loli children recursively like any other term. The sub-rule itself would be type-checked when it fires (future work).

### 9. `Store.tagId()` Returns 0 for Invalid AND `atom`

Use `Store.isTerm(h)` before `Store.tagId(h)`. The type checker only processes valid terms (guaranteed by compile.js).

### 10. Metavar Sort Polymorphism

A metavar M might legitimately appear at different sorts in different pattern positions IF the sorts are compatible (e.g., same base type). The simple approach: flag any inconsistency. If false positives arise, we can add an exception list.

---

## Test Plan

### File: `tests/engine/type-check.test.js`

**Sort table construction (5 tests):**
1. `buildSortTable` from bin.ill types → correct baseTypes and signatures
2. Arrow chain `bin -> bin -> bin -> type` → `{ arity: 3, argTypes: ['bin','bin','bin'], returnType: 'type' }`
3. Simple ref `e: bin` → `{ arity: 0, argTypes: [], returnType: 'bin' }`
4. Base type `bin: type` → added to `baseTypes` set, NOT to signatures
5. Axiom `plus/z1: plus e e e` → skipped (parseTypeSignature returns null)

**Arity checking (5 tests):**
6. `plus(e, e, e)` → no issues
7. `plus(e, e)` → arity error: expected 3, got 2
8. `i(e, e)` → arity error: expected 1, got 2
9. Nested: `plus(o(e), i(e), e)` → no issues (recursive check)
10. Metavar-only: `plus(M, N, R)` → no arity issues

**Sort checking (5 tests):**
11. `plus(o(M), i(N), R)` → all args have sort bin ✓
12. `inferSort` on `o(e)` → `'bin'`
13. `inferSort` on `binlit(42n)` → `'bin'`
14. `inferSort` on metavar → null (unconstrained)
15. Sort mismatch in hand-crafted term → sort issue reported

**Cross-rule consistency (3 tests):**
16. Well-typed EVM rule (e.g., evm/add) → no issues
17. Rule with metavar sort conflict → consistency issue reported
18. Rule with existential in correct position → no issues

**Backward clause checking (3 tests):**
19. `plus/z1: plus e e e` → no issues
20. `inc/s: inc (i X) (o Y) <- inc X Y` → no issues
21. Hand-crafted malformed clause → arity error

**Integration (2 tests):**
22. `mde.load('bin.ill')` → no type issues (sortTable populated, typeIssues empty)
23. `mde.load('evm.ill')` → no type issues

---

## Performance

| Operation | Cost | When | Frequency |
|---|---|---|---|
| `buildSortTable` | O(T) walk arrow chains | Load time | Once per load |
| `checkTermArity` | O(n) per term | After compile | Once per rule |
| `checkTermSort` | O(n) per term | After compile | Once per rule |
| `checkForwardRule` | O(n) per rule | After compile | Once per rule |
| `checkAll` | O(R × n̄) total | After compile | Once per load |

For EVM (73 forward rules, ~50 clauses, ~80 type declarations): **<1ms total**. Zero runtime cost.

---

## Non-Goals

- **Dependent type checking** (Π x:A.B where B depends on x) — that's TODO_0011.Stage_4
- **Polymorphic type checking** (∀X.A) — separate extension on Axis 1
- **Runtime type tagging** — types are checked statically, not at runtime
- **Type inference from usage** — declarations have explicit signatures; we check, not infer
- **Hereditary substitution** — CALC's types are first-order (no type-level lambdas), so type checking degenerates to structural comparison. See [RES_0076](../research/0076_lf-type-checking.md) §3.
- **Bidirectional type checking** — full bidirectional is overkill for first-order types. Our `checkTermSort` with `inferSort` achieves the same result with simpler code.

## Connection to TODO_0064

This is TODO_0064.Phase_2.B3 (Sort System + Arity Checking). The four stages here cover:
- B3 arity checking → Stage 1
- B3 sort system → Stage 2
- Forward rule type safety → Stage 3
- Backward clause type safety → Stage 4

Implementing this is a prerequisite for:
- **Polymorphism** (TODO_0064.A1) — need the sort table to extend with type variables
- **Indexed families** (TODO_0064.C4) — need sort checking to extend with index constraints
- **Dependent types** (TODO_0011.Stage_4) — need the full checking infrastructure

## References

- [RES_0076](../research/0076_lf-type-checking.md) — LF type checking algorithms, hereditary substitution, bidirectional typing
- [TODO_0064](0064_higher-order-extensions-overview.md) — Master plan for higher-order extensions
- [TODO_0011](0011_clf-dependent-types.md) — CLF dependent types (future)
- Harper, Honsell, Plotkin (1993). "A Framework for Defining Logics." JACM 40(1).
- Watkins et al. (2004). "A Concurrent Logical Framework." TYPES 2003.
