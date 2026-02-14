# Hybrid Addressing for Forward Chaining Optimization

Optimizing forward chaining execution while keeping everything as plain linear logic. The engine detects patterns at compile time and applies transparent shortcuts at runtime.

## The Core Idea

Forward chaining rules like `f(X) * !plus(X, 2, X') -o f(X') * B()` preserve the predicate `f` — it appears on both sides of `-o` with a small change to its argument. The engine can detect this at compile time and, instead of full match + consume + substitute + produce, just navigate to the changed argument, apply the transform, and swap the hash.

For deeply nested types like `a(b(c(X), d(...)), e(f(Y, g(...))))` where a rule changes X and Y but preserves the structure — paths `[0,0,0]` and `[1,0,0]` identify the changed positions. Only nodes along those paths need new hashes (incremental Merkle update). Everything else keeps its content-addressed hash.

The hybrid: **content-addressed values everywhere, path-based access for navigating to what changes.**

## Quantified: Where the Waste Is

Analysis of all 44 EVM rules (`evm.ill`):

| Category | Facts | % of LHS | Description |
|----------|-------|----------|-------------|
| **Preserved** | 57 | 27% | Same predicate, identical args both sides |
| **Delta** | 97 | 46% | Same predicate, arg(s) change. In-place update possible |
| **Consumed** | 56 | 27% | Left-only, truly removed |
| **Produced** | 32 | — | Right-only, truly new |

**73.4% of all antecedent patterns** (154 of 210) could be optimized away or reduced to cheap field access.

Top preserved predicates:
- `code PC (opcode)` — **42 of 44 rules**. Every step consumes+reproduces the SAME bytecode fact.
- `address`, `sender`, `callvalue`, `timestamp`, `gaslimit`, `calldatasize` — environment singletons, read-only lookups disguised as consume+produce.

Top delta predicates:
- `pc` — 38 rules. arg0: PC → PC' (via `!inc` or jump target)
- `sh` — 34 rules. arg0: unwrap `s()` constructor (functionally `-1`)
- `gas` — 19 rules. arg0: GAS → GAS' (via `!inc` or `!plus`)

## Three Optimization Levels

All three are transparent — rules don't change, the engine just gets smarter.

### Level 1: Preserved Predicate Optimization

At compile time, detect predicates that appear identically on both sides of `-o`. Skip the consume/reproduce/index-update cycle.

Two sub-cases:
1. **All vars already bound** (by non-preserved patterns): verification-only — O(1) index check.
2. **Some vars not yet bound**: must match to bind variables, but still skip consume/produce.

**Note:** For `code PC OPCODE` specifically, the opcodeLayer strategy already handles the existence verification via `codeByPC` index.

### Level 2: Delta Application

At compile time, compare antecedent and consequent patterns for same-predicate facts. Extract which arguments change and what transforms them.

Example — rule `evm/add` has `pc PC` → `pc PC'` where `!inc PC PC'`:
```
1. find pc fact in state              — O(1) index lookup
2. read arg0 (current PC value)      — Store.child (flat store: 4ns)
3. apply inc                          — FFI, O(1)
4. create pc(PC')                     — Store.put('pc', [newPC])
5. swap in state: old hash → new hash — O(1)
```

All O(1). No full pattern matching, no unification, no full substitution.

**`sh` as delta:** `arg0 → Store.child(arg0, 0)` is O(1). Unwraps one `s()` constructor.

### Level 3: Path-Based Access for Nested Types

For deeply nested linear terms where a rule preserves the outer structure but changes values at specific paths. Precompute paths at compile time, rebuild only along changed paths.

For term size N with K changes at depth D: O(K*D) vs O(N).

## Resolved Research Questions

### 1. Full Theta Elimination for Deltas

**Answer: Yes, conditionally safe. Decidable at compile time.**

A delta predicate's transform reads inputs from the matched state fact and computes outputs via FFI. If the delta's variables don't flow to other unprocessed patterns, no theta is needed.

**Example — `evm/add` rule:**
- `pc`: delta, `PC` bound by matching, `PC'` = `inc(PC)` via FFI. **Theta-free.**
- `code`: preserved, vars already bound by `pc` and opcodeLayer. **Verification only.**
- `sh`: preserved, `SH` flows to consumed `stack SH ...`. **Must bind into theta.**
- `gas`: delta, `GAS` bound by matching, `GAS'` = `plus(GAS, ...)` via FFI. **Theta-free.**
- `stack`: consumed, needs `SH`, `X`, `Y`, `REST` from theta. **Full match needed.**

### 2. sh/Stack Representation

**Answer: Keep Peano encoding.** The delta optimization handles it efficiently. Runtime access is O(1) per step regardless of encoding.

### 3. When Are Preserved Predicates Truly Free?

**Answer: Determinable at compile time via variable dependency analysis.** If all variables in the preserved predicate are bound by earlier patterns, it reduces to an existence check (O(1) via state index).

## How Delta Extraction Works

At compile time, for each forward rule:

```
For each linear predicate P in antecedent:
  If P also in consequent with same predicate head and arity:
    Compare argument patterns pairwise:
      invariant | delta (with transform) | full recomputation
    Classification:
      All positions invariant → PRESERVED
      Some positions have deltas → DELTA
      Structure changes → FULL (regular match)
```

Output per rule:
```javascript
{
  preserved: [{ pred: 'code', freeVars: false }],
  deltas: [
    { pred: 'pc', position: 0, transform: 'inc', thetaFree: true },
    { pred: 'gas', position: 0, transform: 'plus', args: ['gas_cost'], thetaFree: true },
  ],
  consumed: ['stack'],
  produced: ['stack'],
}
```

## Implementation

### Stage 1: Flat Array Store (done)

Replaced `Map<hash, {tag, children}>` with TypedArray SoA arena in `lib/kernel/store.js`. Migrated hot-path callers (unify.js, substitute.js, forward.js, symexec.js) to direct accessors.

**Result:** symexec median 5.59ms → 3.47ms (**38% faster**). +138 LOC in store.js, -22 LOC across callers.

See `lib/kernel/store.js` for implementation details.

### Stage 2: Preserved/Delta Detection (next)

Add analysis pass in `compileRule()` or a new module. Each compiled rule gets `preserved: [...]`, `deltas: [...]` metadata. No execution changes yet — just metadata generation.

**Scope:** ~200 LOC. **Risk:** Very low (pure addition).

### Stage 3: Optimized Execution

Modify `tryMatch` and `applyMatch` to use Stage 2 metadata. Skip consume/produce for preserved. Apply deltas for delta predicates. Fallback to full match for unclassified.

**Scope:** ~200 LOC. **Benefit:** ~2-5x on forward chaining. **Risk:** Medium (must verify correctness).

### Stage 4: Path-Based Nested Access (future)

For deeply nested preserved types, precompute paths to changed leaves. Becomes valuable when EVM facts are merged into one `evm(...)` type or other calculi use deeply nested linear types.

**Scope:** ~300 LOC. **Benefit:** O(K*D) vs O(N).

## Relation to Content vs Path Addressing

**Content-addressed:** All values. Essential for O(1) equality, structural sharing, multiset keys. Does NOT change.

**Path-addressed:** Access patterns within preserved terms. Precomputed at compile time from rule structure.

## References

- Baader & Nipkow (1998) — Term rewriting positions and paths
- Stickel (1989) — Path indexing for theorem provers
- Conchon & Filliatre (2006) — Type-safe modular hash-consing
- Sampson (2019) — Flattening ASTs (arena allocation)
- BitECS — SoA TypedArray architecture for JS
- See also: `doc/research/flat-array-store.md`, `doc/research/path-addressed-trees.md`
