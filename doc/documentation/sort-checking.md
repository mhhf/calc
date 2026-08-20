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

`sortTable(types)` walks the `types` Map and parses arrow-chain hashes into sort entries:

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

## Two layers: base checker + refinement sorts (TODO_0011 rung 1)

`type-check.js` is the **base checker** (arity + LF-signature sort consistency,
above). The **refinement-sort** machinery lives in a separate module,
`lib/engine/sorts.js`, and the two are composed through the checker context
`cx.sorts`:

- **Sortless mode** (`cx.sorts == null` — ILL and any calculus without a
  `cc.sorts` config): sort checking is exact — a term at a `bin` position must
  be `bin`. `type-check.js` runs standalone; `sorts.js` is never engaged.
- **Sorted mode** (`cx.sorts` = a sort system from `sorts.js` — till, gated
  twice: the calculus supplies `cc.sorts` AND the program declares sorts):
  sort equality relaxes to **subsumption ≤**. The single hook is
  `cx.sorts.subsort(actual, expected)` (`type-check.js:101`): a `frac` satisfies
  a `q` position because `frac <: q`, a classifier member satisfies its
  classifier, and every declared sort is `<: 'type'`.

What each module owns:

| Module | Owns |
|--------|------|
| `type-check.js` | the WALK — arity, per-node sort obligations, metavar-consistency, and **bounded sort-variable solving** (`f: (s <: q) …`): solve `s := lub(arg sorts)`, then require a clause INSTANCE at `s` (`type-check.js:360,368`). Strictness = instance absence. |
| `sorts.js` | the SORT SYSTEM — the subsort DAG index built from `A <: B.` sedge facts, its materialized reflexive-transitive closure, the `subsort(a,b)` query, classifier membership, and the `SORT_PREDS` name constants. |

The DAG is a **dual representation**: `sorts.js` keeps an ancestors index for
O(1) `subsort` queries by the checker AND injects each closure pair as a ground
`subsort a b` fact so in-logic `!subsort X s` premises are total lookups. No
sort name or edge appears in engine JS — edges live in logic files
(`bin <: q.`); only literal classification and value fences live in a
calculus config. See `doc/theory/0020_refinement-sorts.md` and the CLAUDE.md
"Refinement Sorts" section.

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
| `sortTable` | `(types: Map) → Map<string, SortEntry>` | Build sort table from type declarations |
| `inferSort` | `(h, sortTable, metavarSorts) → string` | Infer sort of a term |
| `checkForwardRule` | `(rule, sortTable) → string[]` | Check one compiled forward rule |
| `checkClause` | `(name, clause, sortTable) → string[]` | Check one backward clause |
| `checkAll` | `(types, rules, clauses, opts?) → {errors, warnings}` | Check everything |

## Performance

O(n) per rule, one pass per term AST node. ~73 forward rules + ~40 clauses in EVM SDK completes in <1ms.
