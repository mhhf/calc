# Sort Checking

`lib/engine/type-check.js` — load-time verification of arity and sort consistency for forward rules and backward clauses.

## Overview

CALC's `.ill` files declare types in LF syntax:

```ill
bin: type.
e: bin.
i: bin -> bin.
plus: bin -> bin -> bin -> type.
```

The sort checker enforces these declarations at load time. It catches arity errors, sort mismatches, and metavariable inconsistencies before execution — zero runtime cost.

## Sort Table

`buildSortTable(types)` walks the `types` Map and parses arrow-chain hashes into sort entries:

```
bin:  type              → { argSorts: [],                returnSort: 'type' }
e:    bin               → { argSorts: [],                returnSort: 'bin'  }
i:    bin -> bin        → { argSorts: ['bin'],           returnSort: 'bin'  }
plus: bin -> bin -> bin -> type → { argSorts: ['bin','bin','bin'], returnSort: 'type' }
```

Axioms like `plus/z1: plus e e e` (predicate applications, not arrow chains) are filtered out — `_parseSignature` returns null for them.

## Checking

`_checkTerm(h, expectedSort, sortTable, metavarSorts, errors, path)` is the core recursive walker. For each term hash:

| Tag | Behavior |
|-----|----------|
| **freevar** | Record expected sort on first encounter; flag inconsistency if same metavar appears at different sorts |
| **binlit** | Sort is `'bin'`; error if expected sort differs |
| **atom** | Look up name in sort table; check returnSort vs expected |
| **predicate** (tag >= `PRED_BOUNDARY`) | Check arity matches `argSorts.length`, check returnSort, recurse into children with their `argSorts` |
| **connective** (tensor, loli, bang, etc.) | Recurse into children with unconstrained sort (`'_'`) |
| **not in sort table** | Skip silently (handles FFI-only predicates like `sub`, `div`, `mod`) |

## Error Types

- **Arity mismatch**: `rule 'foo': 'plus' expects 3 args, got 2`
- **Sort mismatch**: `rule 'foo': expected sort 'bin', got 'nat' for 'ee'`
- **Metavar inconsistency**: `rule 'foo': metavar _M used as 'bin' and 'nat'`

## Integration

Runs in `_buildCalc()` (in `lib/engine/index.js`) after rule compilation, before backward index construction:

```javascript
const diagnostics = checkAll(types, compiledRules, clauses, opts);
```

Errors are logged to stderr as warnings. With `opts.strict`, errors throw.

## API

| Function | Signature | Purpose |
|----------|-----------|---------|
| `buildSortTable` | `(types: Map) → Map<string, SortEntry>` | Build sort table from type declarations |
| `inferSort` | `(h, sortTable, metavarSorts) → string` | Infer sort of a term |
| `checkForwardRule` | `(rule, sortTable) → string[]` | Check one compiled forward rule |
| `checkClause` | `(name, clause, sortTable) → string[]` | Check one backward clause |
| `checkAll` | `(types, rules, clauses, opts?) → {errors, warnings}` | Check everything |

## Performance

O(n) per rule, one pass per term AST node. ~73 forward rules + ~40 clauses in EVM SDK completes in <1ms.
