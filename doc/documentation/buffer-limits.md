# Buffer Limits & Allocation Reduction

Precomputed buffer sizes and flat data formats for the forward chaining hot path.

## Precomputed Limits (`rule-analysis.js`)

`analyzeBufferLimits(compiledRule)` computes per-rule:

- **maxWorklist**: upper bound on match worklist depth (sum of pattern node counts)
- **maxTheta**: upper bound on theta entries (distinct metavar count across all patterns)
- **linearCount** / **persistentCount**: antecedent pattern counts

`computeGlobalLimits(rules)` computes the cross-rule max for pre-sizing module-level buffers.

These are **tight bounds** derived from static rule structure — a pattern tree of N nodes produces at most N worklist entries; theta can never exceed the total distinct metavar count.

Stored on `compiled.limits` (plain numbers, JSON-serializable).

## Flat Data Formats

### Flat theta (`[v0, t0, v1, t1, ...]`)

The hot path (forward.js, symexec.js) uses **flat interleaved theta** instead of pair arrays `[[v,t],...]`. This eliminates ~1,500 pair allocations per symexec run.

- `match()` in unify.js: pushes `theta.push(p, t)`, scans `theta[ti]` stepping by 2
- `applyFlat()` in substitute.js: scans `theta[i]` stepping by 2
- `tryMatch()` in forward.js: scans/pushes in flat format
- FFI/backward prover results: converted at boundary (`ft[fi][0], ft[fi][1]`)

Cold paths (backward prover, sequent prover, UI) still use pair format with `apply()`.

### Flat match worklist (`_Gp[]`, `_Gt[]`)

Module-level parallel arrays in unify.js replace `[[pattern, term]]` pairs. Eliminates ~2,000 pair allocations per run. Non-reentrant (match is iterative, never recursive).

### Arity-specialized `applyFlat`

Arity 0/1/2 paths avoid `newChildren[]` allocation — only allocates the `[n0, n1]` array for `Store.put` when the term actually changes.

## Security Considerations

### Buffer overflow: not possible

Limits are derived from rule structure (finite, statically known). The match worklist uses dynamic growth (`if (gLen + ap > _Gp.length)`) as a safety fallback, but the precomputed `maxWorklist` is a provable upper bound.

### Non-reentrancy assumption

The flat worklist (`_Gp`/`_Gt`) is module-level, shared across all `match()` calls. This is safe because:
- `match()` is iterative (worklist loop, no recursion)
- Forward chaining is single-threaded
- No callback inside match calls match again

**Risk**: If a future prover makes `match()` reentrant (e.g., calls match inside a match callback), the module-level buffer would corrupt. Mitigations:
- Document the invariant clearly
- The backward prover (`prove.js`) doesn't call `match()` — it uses `unify()` (separate code path)
- If reentrancy is needed, allocate a local buffer (opt-out of optimization)

### Theta format divergence

Two theta formats coexist: flat `[v,t,v,t,...]` (hot path) and paired `[[v,t],...]` (cold path). The boundary conversion happens in `tryMatch()` when consuming FFI/backward prover results.

**Risk**: Passing wrong format to wrong consumer causes silent corruption (pairs interpreted as flat entries or vice versa). Mitigations:
- `applyFlat()` is a separate function from `apply()` — type confusion is a compile-time error
- Forward.js always uses `subApply` → `applyFlat`; cold paths use `apply` directly
- Future: TypeScript types could enforce format separation

### Content-addressed Store mutation

`Store.put()` inside `applyFlat` creates new content-addressed entries. The arity-specialized paths call `Store.put(t, [n0, n1])` — this allocates a small array for the Store API, but Store deduplicates, so it's a cache hit for repeated substitutions on the same structure.

## Future Optimizations

### Pre-sized theta buffer

Currently theta is `[]` (growable array). With `maxTheta` known, we could pre-size: `new Array(maxTheta * 2)` with a length counter. This would eliminate V8's backing store resizes but adds complexity (length tracking instead of `.push()`).

### Worklist pre-sizing from limits

Currently the worklist starts at 64 and grows. With `globalLimits.maxWorklist` known at init time, we could pre-size exactly. Marginal gain since growth is rare and amortized.

### Store.put without children array

The arity-specialized paths still allocate `[n0, n1]` for `Store.put`. A future `Store.put2(tag, c0, c1)` API could accept children as arguments, eliminating the last allocation in the substitution hot path.

### Flat theta Map for large substitutions

For theta sizes > ~16, linear scan becomes expensive. A flat `Map<var, val>` or hash table could give O(1) lookup. Not needed for current EVM rules (max ~8 bindings per match) but relevant for larger calculi.

### Compile-time substitution specialization

For rules where the consequent structure is fully known at compile time, the substitution could be compiled to a direct Store.put chain (no traversal, no theta scan). This is the "ahead-of-time" path for the future Zig port.

## Where to Add New Limit Analysis

1. Add analysis functions to `lib/prover/strategy/rule-analysis.js`
2. Call from `compileRule()` in `lib/prover/strategy/forward.js`
3. Store on `compiled.limits` or `compiled.analysis`
4. Consume in the relevant hot-path function

All limit data should be plain numbers/objects (JSON-serializable) for future `.ill → JSON` compilation.
