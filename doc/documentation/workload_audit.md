# noFFI Workload Audit

Audit of all JS engine changes introduced in commits `03dceb2` and `1f7d144`
(branch `feat/zk-stark-backend-spikes`, 2026-03-12).

Goal: make the forward engine produce identical results with `noFFI: true`
(clause-only backward proving) vs FFI, so the ZK verifier can certify proofs
without trusting FFI black boxes.

---

## Change inventory

| ID | File | Scope | Lines | Affects default path? |
|----|------|-------|-------|-----------------------|
| C1 | `store.js` | Hash collision handling | +13 -6 | **YES** |
| C2 | `unify.js` | Bound-slot structural comparison | +3 -1 | **YES** |
| C3 | `unify.js` | Reverse binlit ephemeral expansion | +23 | **YES** |
| C4 | `prove.js` | `deepApply` replaces `subApply` | +50 | **YES** |
| C5 | `prove.js` | `getCandidates` allBuckets + catch-all change | +12 -2 | **YES** (bug) |
| C6 | `prove.js` | Iterative `_resolveHash` + `_chaseFreevar` | +80 -37 | **YES** |
| C7 | `match.js` | `setNoFFI` flag + branching | ~15 | no (gated) |
| C8 | `match.js` | `_normalizeBin` | ~35 | no (gated) |
| C9 | `match.js` | `_tryBackwardCache` | ~100 | no (gated) |
| C10 | `match.js` | `_resolveBackwardTheta` | ~45 | no (gated) |
| C11 | `forward.js` | noFFI flag threading | +2 | no (opt-in) |
| C12 | `ffi/index.js` | `not256` registration | +1 | no (additive) |

"Affects default path" = changes behavior when `noFFI` is `false` (production).

---

## C1 — Store hash collision: crash → linear probing

### What changed

`store.js:put()` — on FNV-1a 32-bit hash collision (`DEDUP.get(h)` returns a
structurally different entry), instead of throwing, we now linear-probe up to
64 slots to find an empty one. Throws only after 64 failed probes.

### Motivation

During noFFI execution with large derivations, more terms enter the store,
increasing collision probability. A crash would halt execution.

### Soundness analysis

**This is NOT a soundness fix. It is a liveness fix with a soundness caveat.**

Two distinct problems were conflated:

1. **Hash table slot collision** — two distinct terms map to the same
   `DEDUP` Map key. Linear probing correctly resolves this by placing the
   second term at `(h + probe) >>> 0`. Lookup via `matchesEntry` verifies
   structural equality, so retrieval is correct.

2. **Content-address identity** — the store uses the sequential allocation ID
   (`nextId++`) as the term's identity, NOT the hash itself. So even if two
   terms collide in the hash table, they get distinct sequential IDs. This
   means **the sequential ID is the canonical identity, not the hash**. Hash
   is only used for dedup lookup.

**Conclusion:** Linear probing is correct here because identity = sequential ID.
The hash is only a lookup key for `DEDUP`. Two colliding terms get different
sequential IDs and are never confused. Soundness is preserved.

### Collision probability

| Store size (terms) | P(any collision), 32-bit FNV-1a |
|-------|------|
| 2,032 (multisig load) | 4.8 × 10⁻⁴ |
| 10,000 | 0.012 |
| 77,000 | 0.50 |
| 100,000 | 1.16 (expected >1 collision) |

For the 279-step multisig execution, the store grows to ~15K–20K terms during
noFFI mode. Collision probability is low (~0.02) but nonzero. Without linear
probing, execution would crash ~2% of the time on large inputs.

### Alternatives

| Alternative | Soundness | Performance | Complexity |
|---|---|---|---|
| **Crash on collision** (original) | Safe (fail-stop) | N/A (crashes) | Minimal |
| **Linear probing** (current) | Sound (ID = seqId) | O(1) amortized | Low |
| **Upgrade to 64-bit FNV-1a** | Sound + negligible P(collision) | Same | Moderate (bigint or split-hash) |
| **Separate chaining** | Sound | Slightly worse cache | Low |

### Risks

- **Lookup correctness**: `DEDUP.get(h)` only checks the primary hash slot.
  If a term was stored at `h + probe`, a subsequent `put()` of the same term
  would re-check `h`, find a different entry, probe forward, and eventually
  find the existing match via `matchesEntry`. This is correct.
  BUT: any code that calls `computeHash` directly and uses it as an ID would
  break. **Verify no external code uses `computeHash` as identity.**

- **Probe chain length**: linear probing degrades under clustering. With 64
  max probes and typical load factor < 0.01%, this is not a practical concern.

### Recommendation

**Keep for now.** But schedule C1-ALT: upgrade to 64-bit FNV-1a or xxHash64
to eliminate collisions entirely. The linear probing is a correct stopgap but
adds complexity to the store contract (hash ≠ DEDUP key for collided terms).

### Test plan

```
# Verify dedup correctness under forced collisions:
# 1. Monkey-patch computeHash to return constant 42 for N terms
# 2. Verify all N terms get distinct sequential IDs
# 3. Verify Store.get(id) returns correct structural data for each
# 4. Verify put(same_term) returns existing ID (dedup works through probes)
```

---

## C2 — Bound-slot structural comparison in `matchIndexed`

### What changed

`unify.js:matchIndexed()` — when a metavar slot is already bound and the
existing value differs from the new candidate (`existing !== t`), instead of
returning `false` immediately, we push `[existing, t]` back onto the worklist
for structural comparison.

```javascript
// Before:
if (existing !== t) return false;

// After:
if (existing !== t) {
  _Gp[gLen] = existing; _Gt[gLen] = t; gLen++;
}
```

### Motivation

Needed for cross-representation matching: `binlit(5n)` vs `i(o(i(e)))`.
Same value, different store entries. Without this, a metavar bound to
`binlit(5n)` would reject `i(o(i(e)))` even though they represent the same
number.

### Soundness analysis

**This makes matching more permissive.** Previously, `matchIndexed` was a
one-way pattern matcher (pattern against term). The identity check
`existing !== t` is correct when all values have canonical representations —
which they DO in the content-addressed store for most term types.

The exception is binary numbers: `binlit(5n)` and `i(o(i(e)))` are the same
number but different store entries. This change allows structural comparison
to resolve such cases, but ONLY if an ephemeral expansion handler exists
further down the worklist processing (C3 provides this).

**Soundness holds IF:**
1. The structural comparison correctly identifies equivalent representations
   (binlit vs structural binary).
2. No non-equivalent terms are falsely identified as equal.

The structural comparison dispatches to existing ephemeral expansion code
(binlit vs `i`/`o`/`e`), which correctly implements binary arithmetic
(parity check + recursive decomposition). So soundness holds.

**Completeness:** This change makes matching MORE complete — it accepts
pairs that were previously rejected. This cannot introduce false positives
(unsound matches), only false negatives that are now correctly handled.

### Risks

- **Performance**: every already-bound slot mismatch now enters the worklist
  instead of failing fast. If mismatches are common and the structural
  comparison is expensive, this could slow down matching.

  In practice, slot mismatches for non-equivalent values will fail quickly
  in the structural comparison (different tags → immediate `return false`).
  Only the binlit-vs-structural case takes extra work.

- **Interaction with undo**: the push doesn't create new bindings, so the
  undo stack is unaffected. If the structural comparison fails, the
  `return false` at the bottom of the loop fires, and the caller's
  `undoRestore` handles cleanup.

### Alternatives

| Alternative | Soundness | Performance | Complexity |
|---|---|---|---|
| **Normalize all binary to binlit on store entry** | Sound + fast | Best (no runtime check) | High (touch all Store.put callers) |
| **Structural comparison on mismatch** (current) | Sound | Good (rare case) | Low |
| **Explicit `binEquals(a, b)` helper** | Sound | Good | Medium |

### Recommendation

**Keep, but consider C2-ALT: normalize on store entry.** If all binary
values were stored as `binlit`, this check would never trigger, and we could
revert to the fast `existing !== t` check. `_normalizeBin` (C8) already does
this post-hoc — moving it to store entry would be cleaner.

### Test plan

```
# Unit test: matchIndexed with pre-bound slot
# 1. Bind slot 0 to binlit(5n)
# 2. Match pattern with slot 0 against i(o(i(e)))  → should succeed
# 3. Match pattern with slot 0 against i(o(o(e)))  → should fail (value 4 ≠ 5)
# 4. Match pattern with slot 0 against atom('foo') → should fail (different type)
```

---

## C3 — Reverse binlit ephemeral expansion in `matchIndexed`

### What changed

`unify.js:matchIndexed()` — added a new case at the end of the worklist loop:
when the PATTERN is `binlit(N)` and the TERM is structural binary (`i(X)`,
`o(X)`, or `e`), decompose the binlit and match bit-by-bit.

Previously, only "forward" expansion existed (structural pattern vs binlit term).
Now both directions work.

### Motivation

Clause resolution produces structural binary results (`i(o(i(e)))`), but
the forward engine may store values as `binlit(5n)`. When a compiled pattern
references a `binlit` and the backward prover returns structural binary in
theta, the pattern match fails without reverse expansion.

### Soundness analysis

**Sound.** The expansion is correct:
- `binlit(0n)` matches `e` (zero = empty binary)
- `binlit(N)` where `N` is odd matches `i(X)` if `binlit(N/2n)` matches `X`
- `binlit(N)` where `N` is even and `N > 0` matches `o(X)` if `binlit(N/2n)` matches `X`
- `binlit(N)` where `N` is even and `N = 0` does NOT match `o(X)` (structural `o(...)` represents at least 1 bit)

This is the exact inverse of the existing forward expansion. The two
directions are symmetric and both preserve the bijection between binary
number values and their structural representations.

**Termination:** each recursive step halves `N`, so the expansion terminates
in O(log N) steps. For 256-bit numbers, this is at most 256 steps.

### Literature context

No established precedent in Twelf/Celf/Ceptre for ephemeral expansion between
compact and structural representations during unification. The closest analogy
is CLP(FD) constraint arithmetic, where native integers and relational
specifications coexist. The standard sound approach (CLP) treats native
arithmetic as a black-box oracle consistent with the relational spec.

Our ephemeral expansion is more tightly integrated — it occurs WITHIN
unification, not as a separate constraint solver. This is non-standard but
sound because the expansion is a decision procedure for a specific
equational theory (binary number equality), and it's embedded in a matching
algorithm (not full unification), so it doesn't affect occurs-check or
other unification properties.

### Risks

- **Performance**: creates intermediate `binlit` terms via `Store.put('binlit', [value / 2n])`
  for each bit. For a 256-bit number, this creates up to 256 intermediate terms.
  These are content-addressed (deduped), so repeated matches with the same
  values reuse existing entries.

- **Missing case**: `binlit(0n)` vs `o(X)` correctly returns `false`.
  But `binlit(0n)` vs `e` correctly returns `true`. Edge case verified.

### Alternatives

Same as C2 — normalize on store entry would eliminate the need.

### Recommendation

**Keep.** The expansion is correct, terminates, and handles a real
representation mismatch. Combined with C2, it completes the bidirectional
matching contract between binlit and structural binary.

### Test plan

```
# Unit test: reverse ephemeral expansion
# 1. matchIndexed(binlit(5n), i(o(i(e))), ...) → true
# 2. matchIndexed(binlit(0n), e, ...) → true
# 3. matchIndexed(binlit(0n), o(e), ...) → false
# 4. matchIndexed(binlit(3n), o(i(e)), ...) → false (3 ≠ 2)
# 5. matchIndexed(binlit(255n), i(i(i(i(i(i(i(i(e)))))))), ...) → true
```

---

## C4 — `deepApply` replaces `subApply` in backward prover

### What changed

`prove.js:search()` — replaced `subApply(g, theta)` (kernel `substitute.apply`)
with `deepApply(h, theta)` which builds a `Map` from the theta array for O(1)
freevar lookup, then walks the term tree resolving all freevars transitively.

### Motivation

The backward prover's theta is a flat array of `[var, val]` pairs. As the
proof deepens, theta grows. `subApply` does a linear scan of theta for each
freevar → O(n) per freevar, O(n×m) total for a term with m freevars.
`deepApply` builds a Map once (O(n)), then resolves in O(m) with O(1) lookups.

Additionally, `subApply` is NOT transitive: if `_X → o(_Y)` and `_Y → i(e)`,
`subApply` resolves `_X` to `o(_Y)` but not further. `deepApply` resolves
transitively to `o(i(e))`. This is critical for noFFI mode where clause
resolution produces deep freevar chains.

### Soundness analysis

**Semantically equivalent for idempotent theta** (where all values are ground).
For non-idempotent theta (chains), `deepApply` is MORE correct — it resolves
to the fully ground value, which is what the prover needs to construct the
instantiated goal for the next search step.

**This is a behavioral change for all backward proving**, not just noFFI.
Previously, non-idempotent theta would leave partially-resolved terms, which
could cause clause matching to fail (false negatives) or match the wrong
clause (if a partially-resolved term happens to unify with an unintended
clause head).

In practice, the existing FFI-enhanced path rarely encounters non-idempotent
theta because FFI returns ground values. But clause-only resolution routinely
produces chains.

### WAM literature context

In the WAM, `deref` (the analog of `subApply`) follows reference chains to
completion — it IS transitive. The standard WAM does not use path compression
because it would interfere with the trail/backtracking mechanism. Our system
does not use WAM-style trailing (theta is append-only, no backtracking within
`prove`), so path compression via Map memoization is safe.

The `deepApply` approach (Map + transitive resolution) is closer to the
"offline" or "persistent" union-find variant described by Jaffar (1984),
which achieves near-linear O(n·α(n)) amortized complexity. Our implementation
achieves O(n) for Map construction + O(m) for resolution (assuming O(1) Map
lookups), which is O(n+m) total — better than the O(n×m) of `subApply`.

### Risks

- **Map rebuild on every call**: `deepApply` rebuilds the Map when
  `theta.length` changes. Since `theta` only grows during a proof, the Map
  is rebuilt at most O(depth) times. Each rebuild is O(|theta|). Total cost
  is O(depth × |theta|) in the worst case. For shallow proofs (depth < 50),
  this is negligible. For deep noFFI proofs (depth ~ 20000), this could be
  significant.

  **Mitigation**: the rebuild check `_thetaMapLen !== th.length` ensures we
  only rebuild when theta actually grew. Within a single `search` call, if
  theta hasn't changed, the cached Map is reused.

- **Correctness of transitive resolution**: `_resolveHash` (C6) handles
  freevars, leaf types, arrays, and compound terms. The iterative version
  was carefully tested against the recursive version. All 769 tests pass.

### Alternatives

| Alternative | Complexity | Transitive? | Backtrack-safe? |
|---|---|---|---|
| **`subApply`** (original) | O(n×m) per call | No | Yes |
| **`deepApply` (Map)** (current) | O(n+m) per call | Yes | Yes (no trail) |
| **Eager substitution** (substitute in-place during unification) | O(1) per binding | Yes | No (destructive) |
| **Incremental Map** (add new entries instead of rebuild) | O(1) per binding, O(m) per resolve | Yes | Yes |

### Recommendation

**Keep.** The Map-based approach is a clear algorithmic improvement. However,
consider C4-ALT: incremental Map updates instead of full rebuild. Append new
theta entries to the existing Map instead of rebuilding from scratch:

```javascript
function deepApply(h, th) {
  if (th.length === 0) return h;
  if (_thetaMap === null) _thetaMap = new Map();
  for (let i = _thetaMapLen + 1; i < th.length; i++) {
    _thetaMap.set(th[i][0], th[i][1]);
  }
  _thetaMapLen = th.length - 1;
  return _resolveHash(h);
}
```

### Test plan

```
# 1. Verify transitive resolution:
#    theta = [[_X, o(_Y)], [_Y, i(_Z)], [_Z, binlit(1n)]]
#    deepApply(_X, theta) === o(i(binlit(1n)))  (not o(_Y))
#
# 2. Benchmark: prove plus(binlit(100), binlit(200), X) × 1000
#    Compare deepApply vs subApply timing
#
# 3. Regression: run npm run test:all, verify 0 failures
```

---

## C5 — `getCandidates` allBuckets + catch-all change

### What changed

`prove.js:getCandidates()` — two changes:

1. **Added `allBuckets` parameter**: when `fa === '_'` (freevar first arg)
   AND `allBuckets` is true, return ALL indexed buckets instead of just the
   catch-all bucket. Needed for noFFI clause resolution where output args
   are freevars.

2. **Removed `fa !== '_'` guard on catch-all inclusion**: the return statement
   changed from:
   ```javascript
   types: [...(ti[fa] || []), ...(fa !== '_' ? ti['_'] || [] : [])],
   ```
   to:
   ```javascript
   types: [...(ti[fa] || []), ...(ti['_'] || [])],
   ```

### Bug identified

**Change (2) introduces duplicate candidates when `fa === '_'`.**

When `fa === '_'`:
- Old: returns `ti['_']` only (the guard `fa !== '_'` prevents the second spread)
- New: returns `ti['_'] + ti['_']` — DUPLICATES

This affects the non-allBuckets path (production FFI mode). When a goal's
first argument is a freevar and `allBuckets` is false, the same clause
candidates appear twice. This causes redundant work (each clause is tried
twice) but not incorrect results (the first successful unification wins).

### Soundness analysis

**Not unsound (redundant, not incorrect).** Duplicate candidates only cause
the same clause to be tried twice. Since unification is deterministic and
`search` returns the first success, the redundant attempt is harmless.

However, it doubles the work for freevar-first-arg goals in the default path.

### Completeness analysis

The OLD code was actually **INCOMPLETE** for freevar-first-arg goals. When
`fa === '_'` and `!allBuckets`, it only returned the `'_'` bucket. But a
freevar CAN unify with any constructor, so clauses indexed under specific
constructors (like `'e'`, `'i'`, etc.) should also be candidates.

The `allBuckets` path fixes this for noFFI mode. But the default path
remains incomplete (only returns `'_'` bucket for freevar first args).

In practice, this incompleteness rarely manifests because:
1. FFI handles most predicates before clause resolution
2. Goals reaching clause resolution typically have ground first args
3. `maxDepth: 50` limits search anyway

### Recommendation

**Fix the bug.** Restore the `fa !== '_'` guard to prevent duplicates:

```javascript
return {
  types: [...(ti[fa] || []), ...(fa !== '_' ? ti['_'] || [] : [])],
  clauses: [...(ci[fa] || []), ...(fa !== '_' ? ci['_'] || [] : [])],
};
```

The `allBuckets` path (above the return) already handles the noFFI case
correctly.

### Test plan

```
# 1. Unit test: getCandidates with freevar first arg
#    Verify no duplicate entries in returned arrays
#    Verify allBuckets=true returns all indexed clauses
#    Verify allBuckets=false returns only catch-all bucket
#
# 2. Benchmark: prove a predicate with freevar first arg (e.g., plus(X, 3, 8))
#    Compare with and without the fix — should be ~2x faster with fix
```

---

## C6 — Iterative `_resolveHash` + `_chaseFreevar`

### What changed

`prove.js` — the recursive `_resolveHash` function was converted to an
iterative implementation using an explicit stack. A helper `_chaseFreevar`
was added to follow freevar chains iteratively with path compression.

### Motivation

`mod(1024, 1)` via clause resolution triggers 1024 `divmod` iterations, each
creating ~10 freevars. The recursive `_resolveHash` overflows the call stack
when resolving the resulting 10,000+ freevar chain.

### Implementation

**`_chaseFreevar(h)`**: follows `_thetaMap` entries while the value is a
freevar. Returns the ultimate non-freevar value (or last unbound freevar).
Path-compresses by writing `_thetaMap.set(h, ultimate)`.

**`_resolveHash(startH)`**: explicit stack with frames
`[hash, childIndex, childResults, changed]`:
- Phase 1 (`childIndex === -1`): classify the node (leaf? freevar? compound?)
  and set up child iteration.
- Phase 2 (`childIndex >= 0`): collect child results, advance to next child,
  rebuild parent term if any child changed.

### Soundness analysis

**Functionally identical to the recursive version.** The explicit stack
simulates the call stack exactly. Post-order traversal ensures children are
resolved before parents. The `_chaseFreevar` path compression is safe because:
1. Theta is append-only (no backtracking in `prove`)
2. Path compression only shortcuts freevar→freevar chains, preserving the
   ultimate binding

### WAM literature context

Standard WAM `deref` does NOT use path compression (it would corrupt the
trail). Our system doesn't use trailing, so path compression is safe.
Jaffar (1984) established that union-find with path compression achieves
near-linear O(n·α(n)) amortized complexity for unification — our
`_chaseFreevar` implements exactly this pattern.

### Risks

- **Complexity**: the iterative version is ~80 lines vs ~35 for the recursive
  version. The state machine is harder to reason about. Bug risk is higher.

- **Performance**: each stack frame is a 4-element array allocated on the heap.
  For shallow terms (arity 1-2, depth 3-4), this is ~12 allocations vs 0 for
  the recursive version. The GC pressure could make the iterative version
  SLOWER for typical (shallow) inputs.

- **Edge cases**: the child advancement logic has special cases for
  non-term children (strings, bigints) that skip `_resolveHash`. If a new
  child type is added to the store, this code must be updated.

### Alternatives

| Alternative | Stack safety | Performance | Readability |
|---|---|---|---|
| **Recursive** (original) | No (stack overflow on deep chains) | Best for shallow | Best |
| **Iterative explicit stack** (current) | Yes | Good | Poor |
| **Trampoline** | Yes | ~2-5x slower (closure allocation per step) | Medium |
| **Recursive + `--stack-size`** | Fragile (depends on Node config) | Best | Best |
| **Hybrid**: recursive with iterative freevar chase | Mostly safe | Good | Good |

### Recommendation

**Consider C6-ALT: hybrid approach.** Keep the recursive `_resolveHash` for
term structure (shallow — max depth = term arity nesting, typically < 10),
but use iterative `_chaseFreevar` for freevar chains (deep — can be 10,000+).
The overflow only occurs in freevar chains, not term structure:

```javascript
function _resolveHash(h) {
  if (!Store.isTerm(h)) return h;
  const tag = Store.tag(h);
  if (!tag) return h;
  if (tag === 'freevar') {
    const v = _chaseFreevar(h);  // iterative
    if (!Store.isTerm(v) || Store.tag(v) === 'freevar') return v;
    return _resolveHash(v);  // recursive on the resolved value
  }
  // ... rest is standard recursive tree walk (bounded depth)
}
```

This preserves readability of the recursive version while fixing the
stack overflow. Term structure depth is bounded by the calculus (max arity 4,
typical nesting < 20 for binary numbers), so the recursive part never
overflows.

### Test plan

```
# 1. Stress test: mod(randBigInt(12), 1n) via clause-only backward proving
#    (creates ~4000 freevar chain). Must not overflow.
#
# 2. Correctness: compare _resolveHash output against recursive version
#    for 1000 random terms with random theta chains
#
# 3. Benchmark: time _resolveHash for shallow terms (arity 2, depth 3)
#    Compare iterative vs recursive vs hybrid — measure GC pressure
```

---

## C7 — `setNoFFI` flag + branching in `match.js`

### What changed

Module-level `_noFFI` boolean in `match.js`, set by `forward.js` via
`setNoFFI(v)`. When true:
1. Skip compiled persistent steps (`executePersistentStep`)
2. Use `provePersistentNaive` instead of `provePersistentGoals`
   (which is `provePersistentWithFFI`)
3. Pass `maxDepth: 20000`, `allBuckets: true`, `useFFI: false` to
   backward prover

### Soundness analysis

**Sound.** The noFFI path uses the same clause definitions and backward prover,
just without FFI acceleration. The principle "FFI is optimization, theory is
semantics" is maintained — disabling FFI falls back to the theory (clauses).

### Architectural concern: mutable module-level state

`_noFFI` is a module-level `let` variable, set globally. This means:
- Not thread-safe (irrelevant in single-threaded Node.js)
- Persists across calls (must be explicitly reset)
- Not composable (can't run FFI and noFFI in parallel)

### Alternatives

| Alternative | Thread-safe | Composable | Complexity |
|---|---|---|---|
| **Module-level flag** (current) | No | No | Minimal |
| **Pass as parameter through call chain** | Yes | Yes | High (touches many signatures) |
| **Options object on engine instance** | Yes | Yes | Medium |
| **Profile object** (like existing optimizations) | Yes | Yes | Medium |

### Recommendation

**Refactor to options-based.** The `_noFFI` flag should be part of an options
object passed through the call chain, similar to how `evidenceOut` is threaded.
This would eliminate mutable module state and enable composability.

However, this is a significant refactor touching `matchAllLinear`,
`provePersistentNaive`, `resolveExistentials`, and `matchLoli`. Defer to a
separate PR.

For now, **keep** — the module-level flag works correctly in the single-threaded
execution model.

---

## C8 — `_normalizeBin` in `match.js`

### What changed

New function `_normalizeBin(h)`: walks a term tree, converting any structural
binary subtree (`i(o(i(...e)))`) to compact `binlit(N)` form via
`ffi.convert.binToInt` → `ffi.convert.intToBin`.

Called after backward clause resolution binds output values, to prevent
structural binary from bloating the forward engine state.

### Motivation

Clause resolution returns structural binary. If this is stored directly in
the forward engine's fact set, subsequent pattern matching must handle mixed
representations everywhere. Normalizing to binlit ensures a single canonical
form.

### Soundness analysis

**Sound.** `binToInt` followed by `intToBin` is the identity function on
binary number values. The normalization preserves the numeric value and
produces the canonical `binlit` representation that the rest of the engine
expects.

### Risks

- **Recursive**: `_normalizeBin` is recursive. For deeply nested terms
  (not binary numbers, but terms containing binary numbers at depth),
  this could overflow. In practice, term nesting in the forward engine
  is shallow (< 10 levels).

- **Performance**: calls `binToInt` for every `i`/`o`-tagged subterm.
  `binToInt` walks the structural binary to compute the integer value.
  For 256-bit numbers, this is 256 steps per normalization.

### Relationship to C2/C3

If normalization were done at store entry (C2-ALT), C8 would be unnecessary.
`_normalizeBin` is a post-hoc fix for the same representation mismatch that
C2 and C3 address at match time.

### Recommendation

**Keep for now**, but consider consolidating with a store-entry normalization
(C2-ALT) in a future refactor. All three changes (C2, C3, C8) address the
same fundamental issue: binlit vs structural binary coexistence.

---

## C9 — `_tryBackwardCache` in `match.js`

### What changed

New function implementing tabling/memoization for backward proof results.
Caches `(predicate, input_args) → output_values` for deterministic predicates
with known mode declarations (from `ffi.parsedModes`).

### How it works

1. Check if the predicate has a known mode (e.g., `plus: '+ + -'`).
2. Build cache key from predicate name + ground input args.
3. On cache hit: bind cached output values to theta slots. Return immediately.
4. On cache miss: create probe goal with fresh freevars for output positions,
   run full backward clause resolution, cache the result.

### Soundness analysis — CRITICAL

**Sound ONLY for deterministic predicates in classical (persistent) context.**

The tabling literature establishes that caching is sound when:
1. The predicate is referentially transparent (same inputs → same outputs)
2. No resource consumption is involved (classical/persistent, not linear)

Both conditions hold for the cached predicates (`plus`, `mul`, `sub`, etc.):
- They are defined by structural induction on binary numbers — deterministic
- They are proved against persistent (`!`-prefixed) antecedents — no resource consumption

**Fundamental tension with linear logic**: in a linear logic setting, caching
a proof and reusing it amounts to duplicating the consumed resources. But
`_tryBackwardCache` is ONLY used for persistent goals (the `!`-prefixed
antecedents), which are freely duplicable by the `!`-modality. So the cache
is sound.

**Non-deterministic predicates**: if a predicate has multiple valid outputs
for the same inputs (e.g., `member(X, [1,2,3])` could return X=1, X=2, or
X=3), the cache would only store the first result. This is INCOMPLETE but
not UNSOUND — it misses valid answers but never produces invalid ones.

Currently, all cached predicates are deterministic, so this is not an issue.

### Risks

- **Cache invalidation**: the cache is never cleared during execution.
  If the clause definitions could change dynamically, cached results might
  become stale. In CALC, clause definitions are static after loading, so
  this is safe.

- **Memory growth**: each unique `(pred, input_args)` combination creates
  a cache entry. For the 279-step multisig execution, this is ~500 entries
  (one per unique arithmetic operation). Negligible.

- **Probe freevar aliasing** (lines 168-178): after backward proving, the
  code tries to find the probe freevar in the resolved theta. If the freevar
  was aliased (unified with another freevar during proof), the code falls
  back to name-based search. This fallback is O(|theta|) and fragile —
  if two freevars have the same name prefix, it could match the wrong one.

  **Recommendation**: use unique names for probe freevars (e.g., include
  a monotonic counter) and assert that the fallback never triggers in
  production.

### Alternatives

| Alternative | Soundness | Performance | Complexity |
|---|---|---|---|
| **No caching** | Sound | Slow (re-prove every time) | None |
| **`_tryBackwardCache`** (current) | Sound for deterministic persistent preds | Fast (O(1) on hit) | Medium |
| **Full SLG tabling** (XSB-style) | Sound for all preds (handles non-det) | Fast | Very high |
| **Compile predicates to JS functions** | Sound | Fastest | High (code generation) |

### Recommendation

**Keep, but add guards:**
1. Assert that cached predicates are deterministic (check at registration)
2. Use unique probe freevar names with monotonic counter
3. Add `clearBackwardCache()` call in `Store.clear()` for safety
4. Consider making this a toggleable optimization (like other `opt/` modules)

### Test plan

```
# 1. Cache hit correctness:
#    Prove plus(5, 3, X) → cache entry created with output [8]
#    Prove plus(5, 3, Y) → cache hit, Y bound to 8
#    Prove plus(5, 3, 8) → cache hit, ground check passes
#    Prove plus(5, 3, 9) → cache hit, ground check fails → return null
#
# 2. Cache miss + population:
#    Clear cache, prove mul(7, 6, X) → cache miss, backward resolve, populate
#    Prove mul(7, 6, Y) → cache hit
#
# 3. Non-deterministic predicate (if any exist):
#    Verify that caching first answer doesn't hide other valid answers
#
# 4. Performance: benchmark 279-step multisig with and without cache
#    Measure number of backward proofs avoided
```

---

## C10 — `_resolveBackwardTheta` in `match.js`

### What changed

New function that resolves transitive freevar references in backward prover
theta. The backward prover returns theta as `[[var, val], ...]` where values
may contain freevars resolved by later entries. This builds a Map with
fully-resolved values.

### Implementation

1. Process theta entries in reverse order (later entries resolve earlier ones)
2. For each entry, resolve the value's freevars against already-processed entries
3. Fixpoint loop: re-resolve until no changes (handles out-of-order dependencies)

### Soundness analysis

**Sound.** This is equivalent to computing the most general unifier (MGU)
from a non-idempotent substitution. The fixpoint loop guarantees all
transitive references are resolved. The reverse processing order is an
optimization (most dependencies are resolved in one pass), not a correctness
requirement — the fixpoint loop handles any remaining cases.

### Risks

- **Fixpoint termination**: the loop terminates because each iteration either
  resolves a freevar (reducing the number of unresolved references) or
  finds no changes (`changed = false`). The number of iterations is bounded
  by the longest chain in the substitution, which is at most `|theta|`.

- **Quadratic worst case**: each fixpoint iteration scans all entries.
  With `|theta|` entries and up to `|theta|` iterations, worst case is
  O(|theta|²). For the 279-step multisig (~500 entries per backward proof),
  this is manageable. For pathological cases (deeply nested chains of 10,000+
  entries from `mod`/`div`), this could be slow.

  **Mitigation**: `_tryBackwardCache` (C9) prevents the same expensive proof
  from running twice, limiting how often `_resolveBackwardTheta` sees large
  thetas.

### Alternatives

The `deepApply` function (C4) in `prove.js` does the same thing but with a
Map + iterative tree walk. `_resolveBackwardTheta` is a separate
implementation that works on the raw theta array.

**This is code duplication.** Both `deepApply` and `_resolveBackwardTheta`
solve the same problem: transitive freevar resolution in a flat theta.

### Recommendation

**Consolidate.** Extract a shared `resolveTheta(theta) → Map` utility used
by both `prove.js` (for `deepApply`) and `match.js` (for result extraction).
This eliminates the duplicated logic and ensures both paths use the same
algorithm.

---

## C11 — noFFI flag threading in `forward.js`

### What changed

Two lines in `forward.js:run()`:
```javascript
const noFFI = opts.noFFI || false;
match.setNoFFI(noFFI);
```

### Analysis

**Trivially correct.** Reads an opt-in flag, passes it to `match.js`.
No default behavior change.

### Risk

`match.setNoFFI` is never reset after `run()` completes. If a caller runs
`run({ noFFI: true })` followed by `run()` (no noFFI), the flag persists.

**Fix**: add cleanup at end of `run()`:
```javascript
try { ... } finally { match.setNoFFI(false); }
```

Or better: pass noFFI through the call chain (see C7 recommendation).

---

## C12 — `not256` FFI registration

### What changed

One line in `ffi/index.js`:
```javascript
not256: { ffi: 'arithmetic.bitwiseNot', mode: '+ -' },
```

### Analysis

**Trivially correct.** Maps `not256` to the same FFI handler as `not`.
Both `not` and `not256` perform bitwise NOT, but `not256` has clause
definitions that XOR with `2^256-1` (EVM 256-bit NOT), while `not` has
structural bit-flip clauses. The FFI handler already does 256-bit NOT,
so the mapping is correct.

---

## Cross-cutting concerns

### 1. Binlit vs structural binary: the root cause

Changes C2, C3, C8 all address the same fundamental issue: the store can
hold the same binary number in two different representations (`binlit(5n)` vs
`i(o(i(e)))`), and the engine's matching, unification, and state management
must handle both.

**Root fix (C-ALT-NORM)**: normalize ALL binary values to `binlit` at store
entry time. This would:
- Eliminate C2 (bound-slot comparison — always identity-equal)
- Eliminate C3 (reverse ephemeral — never occurs)
- Simplify C8 (normalization — already done at store entry)
- Simplify C4 (deepApply — resolved values are already canonical)

**Tradeoff**: this requires touching `Store.put` to detect `i(X)`, `o(X)`, `e`
patterns and convert to `binlit`. The detection is O(depth) for each put of a
structural binary term. But this cost is paid once (at store entry) instead
of repeatedly (at every match).

### 2. Code duplication: theta resolution

`deepApply` (prove.js) and `_resolveBackwardTheta` (match.js) both implement
transitive freevar resolution. Consolidate into a shared utility.

### 3. Module-level mutable state

`_noFFI`, `_backwardCache`, `_thetaMap`, `_thetaMapLen` are all module-level
mutable state. This prevents:
- Composability (can't run FFI and noFFI simultaneously)
- Testing (must manage global state in tests)
- Reentrancy (single-threaded only)

**Recommendation**: encapsulate in an options/context object threaded through
the call chain. This is a significant refactor but would improve the
architecture.

### 4. Modularity: opt-in profile

The noFFI changes should follow the same pattern as other optimizations in
`opt/`. Create `opt/no-ffi.js` that encapsulates:
- The backward cache
- The normalization
- The theta resolution
- The branching logic

This keeps the hot path (FFI mode) clean and makes the noFFI behavior
explicitly opt-in.

---

## Action items

| Priority | ID | Action | Effort |
|----------|-----|--------|--------|
| P0 (bug) | C5-FIX | Restore `fa !== '_'` guard in getCandidates | 1 line |
| P0 (cleanup) | C11-FIX | Reset `_noFFI` after `run()` completes | 2 lines |
| P1 | C6-ALT | Replace full iterative `_resolveHash` with hybrid (iterative freevar chase + recursive term walk) | ~30 lines |
| P1 | C10-DEDUP | Consolidate theta resolution into shared utility | ~50 lines |
| P2 | C-ALT-NORM | Normalize binary at store entry | ~30 lines + audit all callers |
| P2 | C7-REFACTOR | Thread noFFI via options object instead of module state | ~100 lines |
| P2 | C9-GUARD | Add determinism assertion + unique probe freevar names | ~10 lines |
| P3 | C1-ALT | Upgrade to 64-bit hash (xxHash64 or FNV-1a 64) | ~50 lines |

---

## Measured performance baselines

| Measurement | Result |
|---|---|
| Full test suite (927 tests) | 2.07s wall clock, 0 failures |
| Fuzz test (480 checks, seed 42) | 3.85s, 0 mismatches |
| Store size after multisig load | 1,955 terms |
| P(collision) at 1,955 terms, 32-bit FNV-1a | 4.4 × 10⁻⁴ (0.044%) |
| P(collision) at 77,000 terms | 50% (birthday bound) |
| Backward prove `plus(5,3,X)` avg (1000 reps) | 0.084 ms |
| `subApply` share of backward prove time | 0.7–3.7% |

## Literature references

- **WAM substitution chains**: Ait-Kaci, *Warren's Abstract Machine: A Tutorial Reconstruction*. Standard WAM `deref` is O(chain depth), no path compression (would corrupt trail). Path compression is safe only in persistent (non-backtrackable) contexts — our case, since `prove.js` theta is append-only.
- **Union-Find**: Jaffar (1984) — union-find with path compression achieves O(n·α(n)) amortized for unification. Our `_chaseFreevar` implements this pattern.
- **Content-addressed collisions**: FNV-1a 32-bit reaches 50% collision at ~77K entries (Preshing). Git/IPFS use SHA-1/SHA-256. Our store uses sequential IDs as identity (not the hash), so linear probing is a correct slot-conflict resolution, not a soundness patch.
- **Tabling soundness**: SLG resolution (XSB) requires referential transparency and monotonicity. Sound for persistent (`!`-modality) goals in linear logic — the `_backwardCache` only caches persistent predicates, so reuse doesn't duplicate linear resources. (Harland & Pym, *Forward and Backward Chaining in Linear Logic*.)
- **Ephemeral expansion**: No established precedent in Twelf/Celf/Ceptre. Closest analog is CLP(FD) constraint arithmetic where native integers coexist with relational spec via oracle pattern.
- **Iterative traversal**: Explicit stack is standard for JS/Node.js (no TCO). Trampoline is 2-5x slower due to closure allocation. Hybrid (iterative freevar chase + recursive term walk) is optimal for our use case.

---

## Zig friendliness analysis

### Zig stack model and recursion

Zig uses OS thread stacks (default 8MB on Linux). Deep recursion causes
**segfault** (not a caught panic) — there is no safe stack overflow detection
at runtime. Zig's long-term plan ([issue #1006](https://github.com/ziglang/zig/issues/1006),
[issue #1639](https://github.com/ziglang/zig/issues/1639)) is:

1. **Compile-time recursion detection**: the compiler performs call-graph
   analysis and emits errors for recursive call cycles. You must annotate
   recursive functions with a maximum recursion depth, and the compiler
   multiplies the stack frame size by that limit to compute worst-case
   stack usage.

2. **Async/coroutines**: recursive functions that might be unbounded should
   use stackless coroutines that grow heap memory instead of stack memory.
   This is the "correct" solution for unbounded recursion in Zig.

3. **Explicit tail calls**: `@call(.always_tail, fn, args)` reuses the
   current stack frame, but only works when the `@call` is the operand of
   a `return` statement and there are no `defer` statements. Not general
   enough for post-order tree traversal.

**Implications for our code:**

- **Bounded recursion** (term structure walks: `_normalizeBin`, `_resolveValue`,
  `isGround`, `show`, `binToInt`): Zig can handle these with a compile-time
  depth annotation. Term depth is bounded by the calculus (max arity 4,
  binary numbers ≤ 256 bits, typical nesting < 20). These are safe as
  recursive functions in Zig with `@setRuntimeSafety(true)` and a sensible
  max-depth annotation (e.g., 512).

- **Unbounded recursion** (freevar theta chains, proof search depth): these
  MUST be iterative in Zig. The `_chaseFreevar` approach (iterative chain
  following) is the correct pattern. The `_resolveHash` iterative conversion
  (C6) was necessary for JS but would also be necessary in Zig. However,
  the C6-ALT hybrid approach (iterative freevar chase + recursive term walk)
  would be the **natural Zig idiom**: bounded recursion for the structural
  part, explicit iteration for the unbounded part.

- **The backward prover `search()`**: this is unbounded recursion
  (`maxDepth: 20000`). In Zig, this would need to be iterative or use
  async/coroutines. The current JS implementation uses the call stack
  implicitly — a Zig port would need an explicit work stack.

### Zig InternPool as precedent

The Zig compiler's own [`InternPool`](https://github.com/ziglang/zig/blob/master/src/InternPool.zig)
is directly analogous to our content-addressed store:

| Feature | Our `store.js` | Zig `InternPool` |
|---------|----------------|-------------------|
| Layout | SoA TypedArrays (`tags[]`, `child0[]`, ...) | SoA via `MultiArrayList` |
| Identity | Sequential `u32` IDs | Sequential `Index` (u32) |
| Dedup | FNV-1a 32-bit → `Map<u32, u32>` | Wyhash → sharded hash table |
| Children | Side tables (STRING, BIGINT, ARRAY) | Tagged union `Key` enum |
| Thread safety | Single-threaded (module-level state) | Sharded for multi-threaded sema |

Key differences and what we can learn:

1. **Hash function**: Zig's InternPool uses **Wyhash** (64-bit), not FNV-1a.
   Wyhash is faster AND has 64-bit output — collision probability drops from
   ~1/77K (32-bit) to ~1/5×10⁹ (64-bit). Our C1 linear probing is a stopgap;
   switching to Wyhash or xxHash64 is the proper fix (see C1-ALT).

2. **Sharded hash table**: InternPool uses sharding for thread safety.
   Irrelevant for our single-threaded JS engine, but relevant for a future
   Zig port that might parallelize compilation.

3. **`MultiArrayList`**: Zig's `MultiArrayList(T)` is the idiomatic SoA
   container. Our `tags[]`, `child0[]`, `child1[]`, etc. TypedArrays are
   essentially a manual MultiArrayList. A Zig port would use
   `MultiArrayList(struct { tag: u8, arity: u8, c0: u32, c1: u32, c2: u32, c3: u32 })`.

4. **Tagged union for children**: InternPool uses a `Key` union(enum) to
   represent all possible interned values. Our side-table dispatch
   (`STRING_CHILD_TAGS[t]`, etc.) would become a Zig `union(enum)` with
   comptime dispatch — cleaner and type-safe.

### Recursive vs iterative: the Zig verdict

**Recursive is cleaner and should be preferred when depth is bounded.**

In Zig, the compile-time call-graph analysis means recursive functions have
explicit depth budgets. This is actually BETTER than JS, where the stack
limit is implicit and discovered at runtime via crash. The Zig compiler
itself uses recursive AST walking extensively for bounded-depth traversals.

**Iterative is required when depth is unbounded** (freevar chains, proof
search). The pattern is an explicit `ArrayList`-based work stack with a
state machine loop — the same pattern as our C6 iterative `_resolveHash`.

**Our recommendation for the JS codebase**: adopt the C6-ALT hybrid for
`_resolveHash` (recursive term walk + iterative freevar chase). This is:
- The natural Zig idiom (bounded recursion ok, unbounded needs iteration)
- Cleaner than the full iterative version
- Equally safe (term depth is bounded)
- Easier to verify

For `_normalizeBin`, `_resolveValue`, `isGround`, `binToInt`: keep recursive.
These walk term structure (depth ≤ 256 for binary, ≤ 20 for typical terms).
Converting them to iterative would hurt readability for no safety benefit.

---

## Generalization opportunities

### G1 — Store-entry normalization (eliminate runtime normalization)

There are **three representation dualities** in the store, each handled
differently:

| Duality | Compact | Structural | Where normalized |
|---------|---------|-----------|-----------------|
| Binary numbers | `binlit(N)` | `i(o(i(e)))` | Parser (builders.js), post-hoc (`_normalizeBin` in match.js) |
| Arrays | `arrlit([...])` | `acons(H, acons(H2, ae))` | **Store.put** (eagerly at write time) |
| Strings | `strlit("...")` | `cons(charlit(c), ...)` | **Nowhere** (only unify expansion) |

The array case is the gold standard: `Store.put('acons', ...)` eagerly
normalizes to `arrlit`. No runtime normalization needed. No matching edge
cases.

**Proposal G1**: do the same for binary in `Store.put`:

```javascript
// In Store.put(), before hashing:
if (tagName === 'i' && children.length === 1) {
  const c = children[0];
  if (typeof c === 'number' && c >= 1 && c < nextId) {
    if (tags[c] === TAG.binlit) {
      return put('binlit', [getBigInt(child0[c]) * 2n + 1n]);
    }
    if (tags[c] === TAG.atom && stringTable.get(child0[c]) === 'e') {
      return put('binlit', [1n]);
    }
  }
}
if (tagName === 'o' && children.length === 1) {
  const c = children[0];
  if (typeof c === 'number' && c >= 1 && c < nextId) {
    if (tags[c] === TAG.binlit) {
      return put('binlit', [getBigInt(child0[c]) * 2n]);
    }
  }
}
```

This eliminates:
- **C8 `_normalizeBin`** entirely — never needed if structural binary can't
  exist in the store
- **C3 reverse ephemeral expansion** — never triggers if pattern side is
  always `binlit`
- **C2 bound-slot comparison** — `binlit(5)` vs `i(o(i(e)))` can't happen
  if the latter is normalized to `binlit(5)` on entry

**Impact on clause resolution**: clause premises like `plus/s1: plus (o M) (o N) (o R)`
pattern-match on structural `o(M)`. With store-entry normalization, the
backward prover's `unify` would need to expand `binlit(N)` to match `o(M)`.
This already works via the existing forward ephemeral expansion in `unify`.
So clause resolution is unaffected.

**Impact on `getFirstArgHead`**: this function already handles `binlit` by
returning `'i'`/`'o'`/`'e'` based on parity — it simulates the structural
form for indexing. So the backward index continues to work.

**String normalization (G1-STR)**: similarly, `Store.put('cons', [charlit, strlit])` could
normalize to `strlit`. Lower priority since strings are rare in EVM programs.

### G2 — General `termMap` / term visitor

**11+ functions** in the codebase follow the same recursive pattern:

```javascript
function walkTerm(h) {
  if (!Store.isTerm(h)) return h;
  const tag = Store.tag(h);
  if (isLeaf(tag)) return leafHandler(h, tag);
  if (tag === 'arrlit') { /* walk elements */ }
  const arity = Store.arity(h);
  for (let i = 0; i < arity; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) walkTerm(c);
  }
}
```

Instances: `_normalizeBin`, `_resolveHash`, `_resolveValue`, `isGround`,
`freeVars`, `collectMetavars`, `show`, `formatTerm`, `binToInt`,
`flattenPattern`, `collectFreevars`.

**Proposal G2**: extract a reusable `termMap(h, visitor)`:

```javascript
// termMap: walk a term, calling visitor on each node, bottom-up.
// visitor(h, tag, mappedChildren) → newH
// Returns the (possibly new) root term.
function termMap(h, visitor) {
  if (!Store.isTerm(h)) return visitor(h, null, null);
  const tag = Store.tag(h);
  const tagId = Store.tagId(h);
  if (LEAF_TAG_SET[tagId]) return visitor(h, tag, null);
  if (tagId === TAG_ARRLIT) {
    const elems = Store.getArrayElements(h);
    let changed = false;
    const mapped = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      mapped[i] = termMap(elems[i], visitor);
      if (mapped[i] !== elems[i]) changed = true;
    }
    return visitor(changed ? Store.putArray(mapped) : h, tag, mapped);
  }
  const arity = Store.arity(h);
  let changed = false;
  const mc = new Array(arity);
  for (let i = 0; i < arity; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      mc[i] = termMap(c, visitor);
      if (mc[i] !== c) changed = true;
    } else {
      mc[i] = c;
    }
  }
  return visitor(changed ? Store.put(tag, mc) : h, tag, mc);
}
```

Then `_normalizeBin` becomes:

```javascript
const _normalizeBin = h => termMap(h, (node, tag) => {
  if (tag === 'i' || tag === 'o') {
    const v = binToInt(node);
    if (v !== null) return intToBin(v);
  }
  return node;
});
```

**Zig translation**: in Zig, this would be a `fn termMap(comptime Visitor: type, h: TermId, ctx: *Visitor) TermId`
using comptime generics for zero-cost abstraction.

**Tradeoff**: the generic version allocates `new Array(arity)` per node.
The specialized versions can avoid this (e.g., `isGround` returns `bool`,
doesn't build new terms). So `termMap` is best for transformations, not
queries. For queries, a `termFold(h, init, combine)` or `termWalk(h, visit)`
(void visitor, side-effecting) would be better.

### G3 — Leaf tag classification

The pattern `tag === 'atom' || tag === 'binlit' || tag === 'strlit' || tag === 'charlit'`
appears 3+ times with slight variations (`freevar` included or not, `arrlit`
included or not). Each instance uses `Store.tag()` which allocates a string.

**Proposal G3**: a precomputed bitset:

```javascript
// In store.js:
const LEAF_TAGS = new Uint8Array(256);
LEAF_TAGS[TAG.atom] = 1;
LEAF_TAGS[TAG.binlit] = 1;
LEAF_TAGS[TAG.strlit] = 1;
LEAF_TAGS[TAG.charlit] = 1;
// freevar is a "variable leaf" — callers choose whether to include it

function isLeaf(tagId) { return LEAF_TAGS[tagId]; }
```

This replaces 4 string comparisons + string allocations with a single
`u8` array lookup. In Zig: `const is_leaf = leaf_tags[@intFromEnum(tag)]`.

### G4 — Avoid `Store.tag()` string allocation in hot paths

The new code uses `Store.tag(h)` (returns string, allocates via
`TAG_NAMES[tags[h]]`) in several hot-path locations:

| Location | Calls `Store.tag()` | Could use `Store.tagId()` |
|----------|--------------------|-----------------------|
| `_chaseFreevar` (prove.js:232) | `Store.tag(v) !== 'freevar'` | `Store.tagId(v) !== TAG.freevar` |
| `_resolveHash` (prove.js:254,258,262,263,293) | 5 calls per frame | All replaceable with tagId |
| `_normalizeBin` (match.js:40,42,46) | 3 calls per node | All replaceable with tagId |
| `_resolveValue` (match.js:406,407,412) | 3 calls per node | All replaceable with tagId |

**Proposal G4**: replace all `Store.tag()` calls in hot paths with
`Store.tagId()` + numeric `TAG.*` comparisons. This eliminates string
allocation and enables integer comparison (single CPU instruction) instead
of string comparison (loop over chars).

**Estimated impact**: in tight loops (e.g., normalizing a 256-bit binary),
this eliminates ~256 × 3 = ~768 unnecessary string allocations per
normalization pass. With V8's generational GC, these short-lived strings
are cheap but not free.

### G5 — Incremental `deepApply` Map

Currently `deepApply` rebuilds the entire `Map` from the theta array when
`theta.length` changes:

```javascript
if (_thetaMapLen !== th.length) {
  _thetaMap = new Map();
  for (let i = 0; i < th.length; i++) _thetaMap.set(th[i][0], th[i][1]);
  _thetaMapLen = th.length;
}
```

For a proof of depth D with average branching B, this rebuilds the Map
D times with growing size. Total: O(Σ(i=1..D) i) = O(D²/2).

**Proposal G5**: incremental append:

```javascript
function deepApply(h, th) {
  if (th.length === 0) return h;
  if (_thetaMap === null) { _thetaMap = new Map(); _thetaMapLen = 0; }
  // Append only new entries
  for (let i = _thetaMapLen; i < th.length; i++) {
    _thetaMap.set(th[i][0], th[i][1]);
  }
  _thetaMapLen = th.length;
  return _resolveHash(h);
}
```

This reduces Map construction from O(D²/2) to O(|theta|) total — each
entry is added exactly once.

**Caveat**: path compression in `_chaseFreevar` writes to `_thetaMap`,
potentially overwriting entries. This is fine — path compression values
are always refinements (more resolved) of the original, so no information
is lost. But the `_thetaMapLen` tracking assumes entries are only added
by `deepApply`, not by path compression. Since path compression only
overwrites existing keys (never adds new ones), this is safe.

### G6 — `_resolveBackwardTheta` fixpoint → topological sort

The current fixpoint loop is O(|theta|²) worst case:

```javascript
let changed = true;
while (changed) {
  changed = false;
  for (const [v, val] of resolved) {
    const newVal = _resolveValue(val, resolved);
    if (newVal !== val) { resolved.set(v, newVal); changed = true; }
  }
}
```

**Proposal G6**: topological sort over the dependency graph:

1. Build a dependency graph: for each `[v, val]` entry, record which
   freevars appear in `val`.
2. Process entries in reverse topological order (leaves first).
3. Single pass: O(|theta| × avg_term_size).

This is what `deepApply` effectively does via path compression — it resolves
lazily on demand and memoizes. So the real fix is **C10-DEDUP**: use the same
Map+resolve approach for both prove.js and match.js, eliminating the separate
fixpoint loop entirely.

### G7 — Store-entry normalization for cons/strlit

Like G1 for binary, `Store.put('cons', [charlit_h, strlit_h])` could
normalize to `strlit(char + rest)`. This would close the strlit matching
gap (currently `match`/`matchIndexed` don't handle strlit expansion, only
`unify` does).

Lower priority — strings are rare in EVM programs. But for
completeness and Zig-friendliness (unified normalization layer), it's
worth having.

---

## Performance optimization opportunities

### P-OPT-1: Store.tag() → Store.tagId() in hot paths

See G4. Eliminates ~768 string allocations per binary normalization pass.
Simple mechanical change.

### P-OPT-2: Pre-allocated frame arrays in iterative _resolveHash

The iterative `_resolveHash` allocates `[hash, -1, null, false]` frame
arrays on each stack push. For a term with arity 2 and depth 10, this is
~20 array allocations per call.

**Fix**: use a pre-allocated frame pool (circular buffer of fixed-size
frames). Reset on each `_resolveHash` entry. Eliminates GC pressure.

In Zig: stack-allocated fixed-size buffer with fallback to heap allocator.

### P-OPT-3: binToInt fast path for already-binlit

`_normalizeBin` calls `binToInt(h)` for every `i`/`o` node. `binToInt`
first checks `tag === 'binlit'` (string comparison). If the child is already
`binlit`, the entire chain collapses in one step. But if the child is
structural, `binToInt` recurses through the whole chain.

**Optimization**: check if the immediate child is `binlit` first (O(1)),
avoiding the full recursive walk when the chain is short:

```javascript
if (tag === 'i' || tag === 'o') {
  const childId = Store.rawChild(h, 0);  // no reconstruction
  const childTag = Store.tagId(childId);
  if (childTag === TAG.binlit) {
    // Single-level: i(binlit(N)) → binlit(2N+1)
    const val = getBigInt(Store.rawChild(childId, 0));
    return intToBin(tag === 'i' ? val * 2n + 1n : val * 2n);
  }
  // Fall through to full binToInt
}
```

### P-OPT-4: Avoid Store.get() in _tryBackwardCache

`_tryBackwardCache` calls `Store.get(goal)` which allocates a
`{ tag, children }` object. It then reads `node.children`. This allocation
can be avoided by using `Store.arity()` + `Store.child()` directly:

```javascript
const arity = Store.arity(goal);
const args = [];
for (let i = 0; i < arity; i++) args.push(Store.child(goal, i));
```

Or better: use `Store.rawChild()` and only reconstruct when needed.

---

## Summary of generalizations

| ID | Description | Eliminates | Effort |
|----|-------------|-----------|--------|
| G1 | Store-entry binary normalization | C2, C3, C8 | Medium |
| G2 | Generic `termMap` / term visitor | Code duplication in 11+ functions | Medium |
| G3 | Leaf tag bitset (`LEAF_TAGS[]`) | String comparisons in hot paths | Small |
| G4 | `Store.tag()` → `Store.tagId()` in hot paths | String allocations | Small |
| G5 | Incremental `deepApply` Map | O(D²) rebuild overhead | Small |
| G6 | Topological sort for theta resolution | O(|theta|²) fixpoint loop | Medium (or merge with C10-DEDUP) |
| G7 | Store-entry string normalization | strlit matching gap | Low priority |

### Zig port readiness

| Component | Zig-friendly? | Notes |
|-----------|--------------|-------|
| Store (SoA layout) | Excellent | Direct `MultiArrayList` translation |
| Side tables | Good | `union(enum)` for child types |
| Hash function | Needs upgrade | FNV-1a 32-bit → Wyhash 64-bit (Zig stdlib) |
| Dedup table | Good | `std.HashMap` with custom context |
| `matchIndexed` (iterative worklist) | Excellent | Stack-allocated fixed buffer |
| `_chaseFreevar` (iterative) | Excellent | Simple while loop |
| `_resolveHash` (full iterative) | Over-engineered | Hybrid (recursive term + iterative freevar) is the Zig idiom |
| `_normalizeBin` (recursive) | Fine | Bounded depth (≤ 256), use `@setRuntimeSafety` |
| `search()` in prove.js (recursive, depth 20K) | **Needs rewrite** | Must be iterative explicit stack in Zig |
| Module-level mutable state | **Anti-pattern** | Zig uses explicit context/allocator threading |
| `_backwardCache` (Map) | Good | `std.HashMap` with custom key |

## Benchmark plan

```bash
# 1. Default path regression (FFI mode)
npm run bench:diff   # cross-commit benchmark comparison

# 2. noFFI path timing
node -e "
  const mde = require('./lib/engine');
  const Store = require('./lib/kernel/store');
  const match = require('./lib/engine/match');
  Store.clear();
  const ec = mde.load('calculus/ill/programs/multisig_nocall_solc.ill');
  const s = mde.decomposeQuery(ec.queries.get('symex'));
  // FFI baseline
  let t0 = Date.now();
  ec.exec(s, { maxSteps: 300 });
  console.log('FFI:', Date.now() - t0, 'ms');
  // noFFI
  Store.clear();
  const ec2 = mde.load('calculus/ill/programs/multisig_nocall_solc.ill');
  const s2 = mde.decomposeQuery(ec2.queries.get('symex'));
  t0 = Date.now();
  ec2.exec(s2, { maxSteps: 300, noFFI: true });
  console.log('noFFI:', Date.now() - t0, 'ms');
"

# 3. Fuzz correctness
node tools/fuzz-ffi.js --seed 42 --count 50

# 4. getCandidates duplicate check (after C5-FIX)
node -e "
  const prove = require('./lib/engine/prove');
  // Build index, query with freevar first arg, verify no duplicates
"
```

---

## Software Engineering & Architecture Audit

Independent audit of the engine code from a purely software engineering perspective.
Covers: modularity, coupling, duplication, design patterns, abstraction boundaries,
file organization, and actionable refactoring proposals.

---

### SE-1: `match.js` is a god module (1050 lines, 10 responsibilities)

`match.js` handles:
1. FFI control (`setNoFFI`, `clearBackwardCache`)
2. Binary normalization (`_normalizeBin`)
3. Backward proof caching (`_tryBackwardCache`)
4. Backward theta resolution (`_resolveBackwardTheta`, `_resolveValue`)
5. Profiling instrumentation
6. Rule indexing (`buildDiscriminatorIndex`, `detectFingerprintConfig`, `findFingerprintValue`)
7. Persistent proving — two implementations (`provePersistentGoals`, `provePersistentNaive`)
8. Existential resolution (`resolveExistentials`)
9. Pattern matching (`tryMatch`, `matchOnePattern`, `matchAllLinear`)
10. Loli matching (`matchLoli`, `matchFirstLoli`)

**Diagnosis**: Single Responsibility Principle violation. The file is hard to navigate,
hard to test in isolation, and changes to one concern (e.g., caching) risk
destabilizing another (e.g., pattern matching).

**Proposed split**:

```
match.js           → core pattern matching only (tryMatch, matchOnePattern, matchAllLinear)
persistent.js      → provePersistentGoals/Naive, state lookup, backward dispatch
backward-cache.js  → _tryBackwardCache, _resolveBackwardTheta, _resolveValue
normalize.js       → _normalizeBin (+ future normalizers for arrlit, strlit)
indexing.js        → buildDiscriminatorIndex, detectFingerprintConfig, findFingerprintValue
```

The `indexing.js` functions are already almost standalone — they have no dependency
on `_noFFI` or `_backwardCache`. Extraction is zero-risk.

`persistent.js` would unify `provePersistentWithFFI` (currently in `opt/ffi.js`)
and `provePersistentNaive` (currently in `match.js`) into a single configurable
pipeline — see SE-4.

**Effort**: Medium. No behavioral change, pure file restructuring + re-exports.

---

### SE-2: Module-level mutable state (`_noFFI`, `_backwardCache`)

**Current pattern**:
```javascript
// match.js
let _noFFI = false;
function setNoFFI(v) { _noFFI = !!v; }

// forward.js
match.setNoFFI(opts.noFFI || false);
// ... run() exits without resetting _noFFI (C11 bug)
```

**Problems**:
- **Temporal coupling**: caller must set before use and reset after. The C11 bug
  (flag not reset) is a direct consequence.
- **Non-composable**: can't run two concurrent executions with different settings.
- **Untestable**: tests must manually manage global state between cases.
- **Anti-pattern for Zig port**: Zig uses explicit context/allocator threading;
  module-level mutable state doesn't translate.

**Fix — Context object pattern**:
```javascript
// Execution context threaded through the call chain
function createExecContext(opts = {}) {
  return {
    noFFI: !!opts.noFFI,
    backwardCache: opts.noFFI ? new Map() : null,
    calc: opts.calc || null,
    backward: require('./prove'),
  };
}

// forward.js
function run(inputState, rules, opts) {
  const ctx = createExecContext(opts);
  // ... pass ctx to matchAllLinear, provePersistent, etc.
}
```

This eliminates `setNoFFI`, `clearBackwardCache`, and the C11 bug entirely.
Each call to `run()` or `explore()` gets its own context, which is discarded
when the function returns. No cleanup needed.

**Effort**: Medium. Threading `ctx` through match.js functions is mechanical but
touches many call sites. Can be done incrementally — pass `ctx` alongside existing
params, then remove the globals once all callers use `ctx`.

---

### SE-3: Circular dependency (match.js ↔ prove.js)

Five lazy `require('./prove')` calls exist in the engine, all inside function
bodies to break circular dependencies:

| File | Line | Inside |
|------|------|--------|
| `match.js` | 152 | `_tryBackwardCache` |
| `match.js` | 489 | `provePersistentNaive` |
| `forward.js` | 73 | `run()` |
| `explore.js` | 98 | `explore()` |
| `opt/ffi.js` | 152 | `provePersistentWithFFI` |

The root cause: `prove.js` is a backward chaining engine that knows nothing about
the forward engine, but the forward engine needs backward proving for persistent
goals. The lazy require avoids the circular dependency at module load time.

**Fix — Dependency Injection**:
```javascript
// In forward.js run() or explore():
const backward = require('./prove');
const ctx = createExecContext({ ...opts, backward });

// In persistent.js:
function provePersistent(patterns, ..., ctx) {
  const result = ctx.backward.prove(goal, ...);
}
```

The backward prover becomes an explicit dependency injected via the execution
context. No more lazy requires. This also enables testing persistent proving
with a mock backward prover.

**Effort**: Small. Only the injection site and 5 usage sites change.

---

### SE-4: `provePersistentWithFFI` / `provePersistentNaive` duplication

These two functions (`opt/ffi.js:94` and `match.js:440`) share nearly identical
state-lookup code (20+ lines). The only difference is the pipeline order:

| Step | `provePersistentWithFFI` | `provePersistentNaive` |
|------|--------------------------|------------------------|
| 1 | FFI | State lookup |
| 2 | State lookup | Backward cache (optional) |
| 3 | Clause resolution | Clause resolution |

**Fix — Unified pipeline with configurable phases**:
```javascript
function provePersistent(patterns, startIdx, theta, slots, state, ctx, evidenceOut) {
  let idx = startIdx;
  while (idx < patterns.length) {
    const goal = subApplyIdx(patterns[idx], theta, slots);
    let proved = false;

    for (const phase of ctx.persistentPipeline) {
      const result = phase(goal, patterns[idx], theta, slots, state, ctx, evidenceOut);
      if (result === 'proved') { proved = true; break; }
      if (result === 'failed') break;
      // result === 'skip' → try next phase
    }

    if (!proved) break;
    idx++;
  }
  return idx;
}
```

Pipeline configuration:
```javascript
// FFI mode (default)
ctx.persistentPipeline = [phaseFFI, phaseStateLookup, phaseClauseResolution];

// noFFI mode
ctx.persistentPipeline = [phaseStateLookup, phaseBackwardCache, phaseClauseResolution];
```

This eliminates the duplication, makes the pipeline composable, and allows
easy experimentation with different phase orders. Each phase is a pure function
with a simple contract: `(goal, ...) → 'proved' | 'failed' | 'skip'`.

**Effort**: Medium. Factor out phases, wire up pipeline in `createExecContext`.

---

### SE-5: 22+ duplicated term-walking functions

The recursive pattern of tag-dispatch + arrlit-guard + arity-loop over
`Store.child()` appears in at least 22 functions across the codebase:

**lib/kernel/substitute.js** (5):
`sub`, `apply::go`, `occurs`, `debruijnSubst::go`, `applyIndexed::go`

**lib/engine/pattern-utils.js** (3):
`isGround`, `collectMetavars`, `collectFreevars::walk`

**lib/engine/match.js** (2):
`_normalizeBin`, `_resolveValue`

**lib/engine/prove.js** (3):
`_resolveHash` (iterative), `makeFreshener::freshen`, `formatTerm`

**lib/engine/compile.js** (3):
`flattenTensor::walk`, `expandChoiceItem`, `compilePatternMatch::emit`

**lib/engine/disc-tree.js** (2):
`flattenPattern::walk`, `flattenFact::walk`

**lib/engine/ffi/convert.js** (1):
`isGround` — **exact duplicate** of `pattern-utils.js:isGround`

**lib/prover/** (3):
`check-term.js:expand`, `generic-term.js:collectVarHashes::visit`,
`guided-term.js:buildAntecedentProof`

**lib/zk/** (2):
`witness.js:emitSubstTree`, `flat-witness.js:emitSubstTree` — **near-duplicates**

All share the same skeleton:
```javascript
function walk(h) {
  const tag = Store.tag(h);
  if (tag === 'arrlit') { /* handle array elements */ }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) { /* recurse */ }
  }
}
```

**Proposed abstraction — `termMap` and `termFold`** (in `lib/kernel/store.js`):

```javascript
/** Map over term children, returning new term if any changed. */
function termMap(h, fn) {
  if (!isTerm(h)) return h;
  const tid = tagId(h);
  if (ARRAY_CHILD_TAGS[tid]) {
    const elems = getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const ne = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      ne[i] = fn(elems[i]);
      if (ne[i] !== elems[i]) changed = true;
    }
    return changed ? putArray(ne) : h;
  }
  const a = arities[h];
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = reconstructChild(h, i);
    if (typeof c === 'number' && c >= 1 && c < nextId) {
      const r = fn(c);
      nc.push(r);
      if (r !== c) changed = true;
    } else nc.push(c);
  }
  return changed ? put(TAG_NAMES[tid], nc) : h;
}
```

With `termMap`, many walkers become one-liners:
```javascript
// _normalizeBin:
function normalizeBin(h) {
  const tag = Store.tag(h);
  if (tag === 'i' || tag === 'o') {
    const v = binToInt(h); if (v !== null) return intToBin(v);
  }
  return Store.termMap(h, normalizeBin);
}
```

**Tradeoffs**:
- Pro: eliminates ~200 lines of duplicated boilerplate
- Pro: arrlit/compound handling centralized — one place to fix/extend
- Pro: new literal types automatically handled
- Con: small overhead from callback dispatch (~5-10% on micro-benchmarks)
- Con: hot-path functions (`applyIndexed`, `matchIndexed`) should keep inline code

**Recommendation**: Introduce `termMap`/`termFold` in Store, use in cold/warm
paths (normalization, metavar collection, formatting, ZK witness), keep inline
code in the 3-4 hottest functions.

**Effort**: Medium. Add 30 lines to Store, rewrite 10-15 functions.

---

### SE-6: `isGround` — exact duplicate across modules

`lib/engine/pattern-utils.js:isGround` (line 10) and `lib/engine/ffi/convert.js:isGround`
(line 90) are duplicates. The convert.js version is re-exported and used by
`opt/ffi.js` and match.js. The pattern-utils version is used by compile.js and
rule-analysis.js.

**Fix**: Delete the convert.js duplicate, import from pattern-utils.js.

**Effort**: Tiny — 1 line change + test verification.

---

### SE-7: Three theta representations

The engine uses three different substitution representations:

| Representation | Used by | Lookup | Insert |
|---|---|---|---|
| `[[var, val], ...]` pairs | prove.js backward prover | O(n) scan | O(1) push |
| `theta[slot] = val` indexed | match.js forward engine | O(1) | O(1) |
| `UnionFind` (Map) | unify.js | O(α(n)) | O(α(n)) |

**Problem**: The backward prover returns pair-list theta, but the forward engine
needs indexed theta. Translation requires `_resolveBackwardTheta` (match.js:383),
which does an O(|theta|²) fixpoint loop because pair-list theta is not idempotent
(values contain internal freevars resolved by later entries).

**Root cause**: `UnionFind.toTheta()` dumps the parent map without resolving chains.

**Fix — make `toTheta()` return resolved pairs**:
```javascript
toTheta() {
  const theta = [];
  for (const [v] of this.parent) {
    const root = this.find(v);
    if (root !== v) theta.push([v, root]);
  }
  return theta;
}
```

Wait — `find()` already resolves to the root. The issue is that the root may be
a compound term containing other variables that also have bindings. `find()` only
follows the parent chain for freevars, it doesn't recursively substitute inside
compound terms. This is inherent to union-find: the data structure tracks variable
equivalences, not full term resolution.

The real fix is to post-process theta pairs with a single-pass substitution:
walk each value, replacing any freevar that has a binding. This is what
`_resolveBackwardTheta` does, but it needs a fixpoint loop because pairs are
processed in arbitrary order. Processing in reverse order (bindings closer to
leaves first) would make it single-pass.

**Recommendation**: Sort theta pairs in reverse-dependency order (topological
sort on the dependency DAG), then do a single forward pass. This eliminates the
fixpoint loop. Fall back to fixpoint only if cycles exist (shouldn't happen in
unification, but defensive).

**Effort**: Small-medium. Change `_resolveBackwardTheta` to topo-sort + single pass.

---

### SE-8: `deepApply` Map rebuilt on every theta growth

`prove.js:350`:
```javascript
if (_thetaMapLen !== th.length) {
  _thetaMap = new Map();
  for (let i = 0; i < th.length; i++) _thetaMap.set(th[i][0], th[i][1]);
  _thetaMapLen = th.length;
}
```

Every time a new binding is added to theta, the entire Map is rebuilt from scratch.

**Fix — Incremental update with shrink detection**:
```javascript
if (th.length < _thetaMapLen) {
  _thetaMap = new Map();
  _thetaMapLen = 0;
}
for (let i = _thetaMapLen; i < th.length; i++) {
  _thetaMap.set(th[i][0], th[i][1]);
}
_thetaMapLen = th.length;
```

**Caveat**: `search()` creates `currentTheta = [...theta, ...newTheta]`, so
`th` is always a new array. The length comparison detects when a different
branch is being explored (shorter theta = backtracked). Full rebuild on shrink
is correct.

**Effort**: Small. ~5 lines.

---

### SE-9: `opt/` directory — misleading name

Half the modules in `lib/engine/opt/` are always-on (not optional):
`compiled-sub.js`, `constraint.js`, `delta-bypass.js`, `loli-drain.js`, `preserved.js`.

**Recommendation**: Merge non-optional modules into their parent files, or
rename `opt/` to clarify its meaning.

**Effort**: Small.

---

### SE-10: `prove.js` mixes backward search with proof term construction

`prove.js` has three distinct concerns: backward chaining search, proof term
construction (`buildTensorRSpine`, `buildClauseTerm`), and first-argument
indexing (`buildIndex`, `getCandidates`). These could be separate files.

**Effort**: Small.

---

### SE-11: `Store.get()` allocations in warm paths

`Store.get(h)` allocates `{ tag, children }` on every call. Several warm-path
functions still use it:

- `prove.js:getFirstArgHead` (line 20) — called per goal in backward search
- `prove.js:makeFreshener` (line 450) — called per clause candidate
- `prove.js:tryFFI` → `getArgs()` (line 117) — allocates array
- `match.js:_tryBackwardCache` (line 101) — `Store.get(goal)`

**Fix**: Replace with `Store.tag()` / `Store.child()` / `Store.arity()` directly.

**Effort**: Tiny.

---

### SE-12: Missing invariant assertions

| Buffer | Size | Max in practice | Risk |
|--------|------|----------------|------|
| `_undoStack` | 32 bytes | ~20 | Silent overflow |
| `_poolTheta` | 64 slots | ~32 | Out-of-bounds |
| `_psArgs` | 4 slots | 4 | Checked at load |
| `child0..child3` | 4 columns | 3 | Silent drop |

**Fix**: Add debug-mode assertions at critical points.

**Effort**: Tiny.

---

### SE-13: `buildFingerprintIndex` duplicated 3 times

The fingerprint index building code appears in:
1. `forward.js:143` (`buildFingerprintIndex`)
2. `forward.js:87` (inline rebuild in main loop)
3. `strategy.js:197` (inline rebuild in `findMatch`)

**Fix**: Single source of truth, called from one place.

**Effort**: Small.

---

### SE-14: Naming inconsistencies

Several concepts have multiple names:

| Concept | Names used |
|---------|-----------|
| Apply substitution | `deepApply`, `subApply`, `applyIndexed`, `subCompiled` |
| Resolve theta | `_resolveHash`, `_resolveValue`, `_resolveBackwardTheta` |
| Prove persistent | `provePersistentGoals`, `provePersistentNaive`, `provePersistentWithFFI` |
| Content hash | `hash`, `h`, `goalInst`, `goal`, `fact` |

**Recommendation**: Adopt consistent naming:
- `applyTheta*` for all substitution application
- `resolveTheta*` for all theta resolution
- `provePersistent` (unified, pipeline-based — SE-4)

---

### SE-15: Proposed priority

| Priority | ID | Description | Risk | Effort |
|---|---|---|---|---|
| P0 | SE-6 | Remove `isGround` duplicate | None | Tiny |
| P0 | SE-12 | Debug assertions for overflows | None | Tiny |
| P0 | SE-11 | Replace `Store.get()` in warm paths | None | Tiny |
| P1 | SE-2 | Context object (fixes C11 bug) | None | Medium |
| P1 | SE-1 | Split match.js into focused modules | Low | Medium |
| P1 | SE-4 | Unified persistent proving pipeline | Low | Medium |
| P1 | SE-3 | Dependency injection for backward prover | Low | Small |
| P2 | SE-5 | `termMap`/`termFold` abstraction | Low | Medium |
| P2 | SE-7 | Idempotent theta from unifier | Low | Small |
| P2 | SE-8 | Incremental `deepApply` Map | Low | Small |
| P3 | SE-9 | Reorganize `opt/` directory | None | Small |
| P3 | SE-10 | Extract proof terms from prove.js | None | Small |
| P3 | SE-13 | Centralize fingerprint index | Low | Small |
| P3 | SE-14 | Naming consistency pass | None | Small |

**Recommended execution order**:
1. SE-6, SE-12, SE-11 (tiny, zero-risk wins)
2. SE-2 + SE-3 (context object + DI — fixes C11, improves testability)
3. SE-1 + SE-4 (match.js decomposition + unified persistent pipeline)
4. SE-5, SE-7, SE-8 (generalization and cleanup)
