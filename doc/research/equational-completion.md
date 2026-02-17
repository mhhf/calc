# Equational Completion for Arithmetic in ILL

**Status:** Theoretical analysis. Applies only if expression constructors (`plus_expr`, etc.) are adopted (approaches R1, R3-R5). The alternative — keeping all computation in backward chaining via loli-freeze (T6) and eigenvariables (R2) — avoids expression terms entirely and does not require equational completion. See `doc/dev/todo.md` Phase 3 for the decision checkpoint.

## What Is Equational Completion?

A relation `plus(X, Y, Z)` in CALC's backward prover has partial coverage:
- **FFI** handles ground inputs: `plus(3, 5, Z)` → Z = 8 via BigInt arithmetic
- **Structural clauses** handle binary patterns: `plus(e, Y, Y)`, `plus(i(X), ...)` (Peano-style)

When inputs are symbolic (e.g. `plus(calldata_val, 5, Z)`), neither FFI nor structural clauses apply. The relation is **undefined** for these inputs — the prover fails and the forward rule is skipped.

A **catch-all clause** extends the relation to total coverage:

```
plus_sym: plus X Y (plus_expr X Y).
```

This is standard Knuth-Bendix completion applied to ILL backward clauses: every input pair `(X, Y)` now has a result. For inputs where FFI or structural clauses succeed, those fire first (by fallback ordering). For all other inputs, the catch-all produces a symbolic expression term.

## Why Catch-Alls Are Universal Facts

`plus_expr(X, Y)` is NOT a "symbolic placeholder." It IS the canonical result of plus for inputs where no other clause applies. Just as `succ(succ(zero))` represents 2 in Peano arithmetic, `plus_expr(X, Y)` represents the sum of X and Y in the completed relation.

The term enters the content-addressed Store as a concrete node with tag `plus_expr` and two children. It has a deterministic hash. Subsequent operations can inspect its structure (for normalization) or treat it opaquely (as a value flowing through state).

This is the standard approach across symbolic execution tools:
- hevm: `Add(Var x, Lit 3)` — ADT constructor
- K/KEVM: stuck `+Int` application — function that didn't reduce
- Rosette: hash-consed symbolic term

## Confluence

Two paths to the same result must produce identical Store hashes. Consider `plus(3, 5, Z)`:

**Path 1 (FFI):** FFI fires first in the fallback chain. `binToInt(3) + binToInt(5) = 8`. Returns `Store.put('binlit', [8n])`.

**Path 2 (catch-all):** If FFI were skipped, catch-all produces `plus_expr(binlit(3), binlit(5))`. With restricted Store.put normalization (see below), this redirects to `Store.put('binlit', [8n])` — same hash.

**Restriction:** Normalization fires only when tag ∈ `{plus_expr, mul_expr, ...}` AND all children have tag `binlit`. This ensures:
- Both paths produce the same hash for ground inputs (confluence)
- Non-ground inputs (containing metavars/freevars) are never normalized (safety)

Without this normalization, path 2 would produce a different hash (`plus_expr(3,5)` ≠ `binlit(8)`), breaking the confluence property. State facts from different execution paths would not deduplicate correctly.

## Conservative Extension

The catch-all clauses add no new ground theorems.

**Argument:** For ground inputs where all arguments are `binlit`/`i`/`o`/`e`, FFI always succeeds — `binToInt` converts any of these tags to BigInt. The FFI fires first in the fallback chain (FFI → state lookup → backward clauses). Catch-all clauses are tried last.

Therefore, catch-alls only produce results for inputs where the relation was previously **undefined** (symbolic terms, non-numeric atoms). No existing ground computation is altered.

## Why Boolean Catch-Alls Are Unsound

Arithmetic predicates are **total functions**: for every `(X, Y)` there is exactly one `Z` such that `plus(X, Y, Z)`. A catch-all safely assigns the unique missing result.

Boolean predicates are **partial relations**: `neq(X, Y)` succeeds when X ≠ Y and fails when X = Y. A catch-all `neq_sym: neq X Y.` would assert `neq(X, X)` for all X — contradicting `neq(5, 5) → false`.

**Rule:** Catch-alls are safe only for total functions (predicates with an output argument that is always uniquely determined). Boolean/relational predicates (where success/failure IS the result) must not have catch-alls.

| Predicate | Type | Catch-all safe? |
|-----------|------|-----------------|
| `plus X Y Z` | total function (Z determined by X,Y) | Yes |
| `mul X Y Z` | total function | Yes |
| `inc X Y` | total function | Yes |
| `to256 X Y` | total function | Yes |
| `neq X Y` | partial relation | **No** |
| `lt X Y` | partial relation | **No** |
| `eq X Y` | partial relation | **No** |

## Backward Prover Semantics

CALC's backward prover uses first-match-wins with a three-level fallback chain:

1. **FFI** (fallback 1): Dispatched via `tryFFIDirect`. Returns result for ground numeric inputs. Returns `null` for non-applicable inputs (after bug fix).
2. **State lookup** (fallback 2): Searches `state.persistent` for matching facts.
3. **Backward clauses** (fallback 3): Tries clauses in import order. First match wins.

Catch-all clauses are imported last (in a `symbolic.ill` file imported after `bin.ill` and `evm.ill`). This ensures they are tried last — after all structural clauses for binary arithmetic. The import order determines fallback priority:

```
% In evm.ill:
#import(bin.ill)        % structural clauses: plus(e,Y,Y), plus(i(X),...)
#import(symbolic.ill)   % catch-alls: plus_sym: plus X Y (plus_expr X Y).
```

## Restricted Store.put Normalization

**Safety argument for ground folding at Store.put time:**

When `Store.put('plus_expr', children)` is called:
1. Check: tag ∈ `{plus_expr, mul_expr, minus_expr, ...}` (expression constructors)
2. Check: ALL children have tag `binlit`
3. If both: compute the result via BigInt arithmetic, return `Store.put('binlit', [result])` instead

**Why this is safe for rule patterns:**

Rule patterns in `.rules` and `.ill` files contain metavariables (`_X`, `_Y`, `_C`) as children. Metavariables have tag `freevar`, not `binlit`. Therefore, condition 2 is never satisfied for rule patterns. Normalization only fires on fully ground expression terms produced during execution.

**Why content-addressing is preserved:**

The `plus_expr(binlit(3), binlit(5))` node is never actually stored — the `Store.put` call is intercepted and redirected to `binlit(8)`. There is no hash/content mismatch because the original node was never assigned a hash.

**What this achieves:**

Ground folding ensures that `plus_expr(3, 5)` and `binlit(8)` are the same Store hash. This is essential for:
- State deduplication (symexec hashState)
- Pattern matching (facts with `8` match regardless of how `8` was produced)
- Confluence (catch-all path = FFI path for ground inputs)

## References

- Knuth & Bendix (1970) — *Simple Word Problems in Universal Algebras*
- Baader & Nipkow (1998) — *Term Rewriting and All That*
- Eker (2003) — *Associative-Commutative Rewriting on Large Terms* (Maude)
- `doc/dev/evm-modeling-approaches.md` — design space (R1-R5, S1-S3)
- `doc/research/expression-simplification.md` — simplification techniques survey
- `doc/research/symbolic-arithmetic-design-space.md` — tool comparison
