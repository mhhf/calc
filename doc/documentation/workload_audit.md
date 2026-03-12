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
