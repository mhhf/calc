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

---

## Proof-Theoretic Audit (Pfenning Lens)

Audit of the forward engine from the perspective of proof theory and logical frameworks. Focuses on naming fidelity, theoretical justification, and correspondence between code and established literature (CLF, Andreoli focusing, Twelf mode declarations, SLD resolution).

### TH-1: Variable Taxonomy Conflation

**Code**: `lib/kernel/store.js` uses a single `freevar` tag for two proof-theoretically distinct species. `lib/kernel/unify.js:156` distinguishes them at runtime by name convention (`name.startsWith('_')`).

**Theory**: Proof theory carefully separates:
- **Metavariables** (schematic variables, unification variables) — stand for unknown terms during search; get instantiated by unification. In CLF/Twelf: capital letters, declared in signatures.
- **Parameters** (eigenvariables, Skolem constants) — introduced by quantifier rules (∀R, ∃L); must remain free in the proof. In CLF: lowercase, fresh per rule application.

`fresh.js` correctly generates distinct forms: `freshEvar()` → `evar(N)` (BigInt-indexed eigenvariables), `freshMetavar()` → `freevar('_mN')` (metavariables). But `evar` has its own tag while metavariables reuse the `freevar` tag — the naming underscore convention is a runtime hack layered over a store that doesn't distinguish them.

**Recommendation**: Introduce a `metavar` tag in the store, eliminating the `isMetavar` name-prefix check. This makes the proof-theoretic distinction structural rather than nominal. The `freevar` tag then exclusively represents parameters/eigenvariables (rule-level bound variables opened during compilation).

### TH-2: "Ephemeral Expansion" Is E-Unification

**Code**: `lib/kernel/unify.js` lines 680–730 perform what comments call "ephemeral expansion" — when a `binlit` (compact binary literal) meets a structural binary term (`i(o(e))`), the unifier expands the binlit into structural form and unifies structurally.

**Theory**: This is **E-unification modulo a convergent term rewriting system (TRS)**. The TRS has a single rule schema: `binlit(n) →* structural(n)` where `structural(n)` is the i/o/e-chain encoding of `n`. Because the TRS is convergent (confluent + terminating), E-unification reduces to: normalize both sides, then syntactic unification. The `_normalizeBin` function in `match.js:38` is precisely the normalization step (rewrite to canonical binlit form).

**Current naming**: "ephemeral expansion" obscures the theoretical basis and makes it sound ad-hoc.

**Recommendation**: Rename to "equational normalization" or "TRS normalization". Document the convergent TRS in a comment: `// E-unification: binlit ↔ structural binary is a convergent TRS; normalize before syntactic unification`.

### TH-3: Backward Prover = SLD Resolution on !-Fragment

**Code**: `lib/engine/prove.js:search()` (line 358) implements depth-first search with clause selection, unification, and backtracking. `getCandidates()` (line 71) performs first-argument indexing.

**Theory**: This is textbook **SLD resolution** (Selective Linear Definite clause resolution) restricted to the unrestricted (!) fragment of the linear logic context. The key theoretical properties:
1. **Soundness**: Each resolution step corresponds to a cut on a !-clause — consuming no linear resources.
2. **Completeness**: Depth-first is incomplete in general (loops on recursive clauses), but the `maxDepth` bound makes it a bounded-depth iterative search, which is fair for finite search spaces.
3. **First-argument indexing**: Standard Prolog optimization (WAM, Twelf). `getCandidates` groups clauses by first-argument head symbol — this is sound because the first argument is sufficient for discrimination (though not for full unification).

**Naming issue**: The function `search()` is generic to the point of being opaque. In Twelf/CLF literature, this would be called `solve` or `prove_unrestricted`.

**Bug note (C5)**: `getCandidates` can return duplicates when the first argument is a freevar — it concatenates the freevar-headed bucket with the specific-head bucket, but doesn't dedup. This is a performance bug (redundant proof attempts), not a soundness bug (duplicate solutions are idempotent in the !-fragment).

### TH-4: Forward Engine = CLF Monadic Forward Chaining

**Code**: `forward.js:run()` implements the main loop; `applyMatch()` (line 35) performs state transitions.

**Theory**: The forward engine implements **CLF monadic forward chaining** (Cervesato, Pfenning, Simmons). The correspondence:
- **State** `(Γ; Δ)` = `(state.persistent; state.linear)` — unrestricted and linear contexts
- **Rule firing** = monadic let-binding: `let {p} = M in N` where `M` matches antecedent and `N` produces consequent
- **`applyMatch`** = the CLF transition: `Γ; Δ → Γ'; Δ'` where consumed linear resources are removed from Δ and produced resources are added
- **Committed choice** = `strategy.findMatch` returns the *first* matching rule, implementing the CLF "don't-care nondeterminism" of forward chaining (vs. `findAllMatches` in `explore.js` which gives "don't-know nondeterminism")

**Naming**: `applyMatch` is reasonable but could be `applyTransition` or `fireRule` to emphasize the state-transition reading. The `consumed` map correctly implements multiplicative resource accounting — each linear fact is consumed exactly once.

### TH-5: `_normalizeBin` = Canonical Form Enforcement

**Code**: `match.js:38` — after every forward step that produces new terms, `_normalizeBin` rewrites structural binary terms (i/o/e chains) to compact `binlit` form.

**Theory**: In CLF, all terms are **canonical** (β-normal, η-long). The content-addressed store (hash-consing) guarantees α-equivalence by construction. `_normalizeBin` extends this to **equational canonical forms** — ensuring that the binlit/structural binary equivalence class has a unique representative. Without this, the same number could appear as both `binlit(5)` and `i(o(i(e)))`, breaking O(1) equality checks.

**Theoretical justification**: This is a normalization-by-evaluation step for the equational theory of binary representation. It preserves the invariant: `∀t. Store.put(normalize(t)) = Store.put(normalize(t'))` whenever `t =_E t'`.

### TH-6: Tabling Soundness via Monotonicity of Γ

**Code**: `match.js:94` — `_tryBackwardCache` memoizes backward proof results keyed by `(predicate, input_args)`.

**Theory**: Tabling (memoization of proof search results) is sound for the !-fragment because:
1. Persistent context Γ is **monotonically growing** during forward chaining — facts are added, never removed
2. A successful proof at time t remains valid at time t' > t (monotonicity)
3. A failed proof at time t may become provable at time t' > t if new facts are added

**Soundness concern**: The current implementation caches both successes and failures (`null` = no solution). Caching failures is **unsound in general** for a monotonically growing context — a goal unprovable now may become provable after new persistent facts are produced. The cache is only sound if:
- (a) It is cleared between forward steps, OR
- (b) Negative cache entries are invalidated when relevant persistent facts are added

Current code clears `_backwardCache` between forward steps (verified via `resetBackwardCache()` calls), so (a) holds. But this should be documented as a critical invariant.

**Naming**: `_backwardCache` → `_tabling` or `_memo` would connect to the tabling literature (XSB Prolog, tabled resolution).

### TH-7: `resolveExistentials` = ∃R with Most General Witness

**Code**: `match.js:546` — when a rule fires and its consequent contains existentially quantified variables, `resolveExistentials` attempts to find witnesses.

**Theory**: In focused proof search, ∃R (existential right) requires providing a witness term. The implementation has a three-level fallback:
1. **State lookup**: witness already exists as a persistent fact (analogous to looking up a definition)
2. **Backward proof**: compute witness via SLD resolution on !-fragment
3. **Fresh eigenvariable**: `freshEvar()` generates a Skolem constant as a "most general witness" — the existential is left open as a constraint

Level 3 is theoretically interesting: it corresponds to the proof-theoretic technique of **delaying witness selection** (used in uniform proofs, Miller et al.). The `freshEvar` is essentially a placeholder saying "∃x. P(x) is satisfied by some x to be determined later." This is sound in a forward-chaining context because the existential variable will be constrained by subsequent rule firings.

**Naming**: `resolveExistentials` is clear. The `freshEvar` fallback could use a comment explaining the delayed-witness interpretation.

### TH-8: `deepApply` = Explicit Substitution Composition

**Code**: `prove.js:347` — `deepApply(term, theta)` applies a substitution to a term, walking the term structure and replacing bound variables.

**Theory**: This is **hereditary substitution** in the CLF sense — applying a substitution to a canonical form produces a canonical form (because the store normalizes on `put()`). The Map-based theta representation is an **explicit substitution** in the sense of Abadi et al., though without the full explicit substitution calculus.

The current implementation rebuilds the Map on every theta extension (creating a new Map from the pair-list theta). This is O(n) per extension. The theoretical alternative is a **union-find** structure (as in `_chaseFreevar`), which gives amortized O(α(n)) lookup.

**Note**: `_chaseFreevar` (prove.js:227) already implements iterative path compression — this IS a union-find chase. The duality between `_chaseFreevar` (union-find) and `deepApply` (Map walk) reflects two competing substitution representations coexisting in the same module.

### TH-9: "types" vs "clauses" — Naming Mismatch

**Code**: Throughout the engine, `calc.types` refers to backward clause definitions indexed by predicate name, and `calc.clauses` refers to the raw clause list. In `prove.js:getCandidates()`, we see `const typeDef = types[head]` where `typeDef` is actually a clause definition.

**Theory**: In Twelf/CLF, **types** and **clauses** have precise meanings:
- A **type** is a classifier: `nat : type`, `plus : nat → nat → nat → type`
- A **clause** is a definition: `plus_z : plus z N N` (a term inhabiting a type)
- The "type" of a predicate is its kind signature; the "clauses" are its defining terms

Using `types` to mean "clause definitions grouped by predicate" conflates two levels of the logical framework. This would confuse any LF/Twelf reader.

**Recommendation**: Rename `calc.types` → `calc.definitions` or `calc.clauseIndex` (an index from predicate names to their defining clauses).

### TH-10: `matchAllLinear` = Focusing Protocol

**Code**: `match.js:752` implements a two-phase loop: Phase 1 matches linear patterns (consuming resources), Phase 2 proves persistent goals.

**Theory**: This directly implements the **Andreoli focusing discipline**:
- **Phase 1 (synchronous/focusing)**: Decompose the linear antecedent — matching patterns against the linear context Δ. Each match is deterministic (no backtracking within a pattern match). Patterns with unresolved dependencies are **deferred** — this corresponds to the focusing discipline's requirement that synchronous decomposition only proceeds when all inputs are determined.
- **Phase 2 (asynchronous/inversion)**: Prove persistent goals via backward chaining on Γ. This is the "blur" rule — switching from the focused (linear matching) phase to the unfocused (persistent proving) phase.
- **Iteration**: The loop re-enters Phase 1 after Phase 2 makes progress, because persistent proving may bind metavariables needed by deferred linear patterns. This interleaving is the **focus-blur-focus** cycle.

The `deferredLen` mechanism (lines 771–798) is the key insight: it's not just optimization, it's **the focusing protocol's requirement** that synchronous rules only fire when their inputs are ground. The dependency tracking via `meta.persistentDeps` is the mode-checking equivalent — ensuring input arguments are determined before matching proceeds.

**Naming**: `matchAllLinear` undersells this function. It could be `focusedMatch` or `focusingProtocol` to reflect its theoretical role.

### TH-11: `consumed` Map = Multiplicative Accounting

**Code**: The `consumed` object tracks which linear facts have been matched, preventing double-consumption.

**Theory**: This is the **multiplicative resource accounting** that distinguishes linear logic from classical logic. Each linear proposition can be used exactly once. The `consumed` map is the runtime implementation of the proof-theoretic constraint that in a sequent `Γ; Δ ⊢ C`, each formula in Δ appears in exactly one premise of a multiplicative rule.

The `reserved` mechanism (for preserved facts that should not be consumed) implements the **principality** condition: when a rule preserves a linear fact (produces the same fact it consumes), the matching should not consume the preserved copy.

### TH-12: `applyMatch` = CLF Monadic Let-Binding

**Code**: `forward.js:35` — `applyMatch(state, { rule, theta, slots, consumed })`:
```
consumeLinear(newState.linear, consumed, null);
produceLinear(newState.linear, rule.consequent.linear, theta, slots, rule, ...);
producePersistent(newState.persistent, rule.consequent.persistent, theta, slots, rule, ...);
```

**Theory**: In CLF, a forward step is a monadic let-binding:
```
let {Δ'} = [σ]R in ...
```
where `σ` is the substitution (theta), `R` is the rule, `Δ'` is the produced linear context. The three operations correspond exactly to the CLF transition judgment:

1. `consumeLinear` = remove matched resources from Δ (antecedent consumption)
2. `produceLinear` = add [σ]C_lin to Δ (linear consequent production)
3. `producePersistent` = add [σ]C_pers to Γ (persistent consequent production)

The fact that persistent facts are only added (never removed) is the proof-theoretic guarantee of **weakening** in the !-fragment.

### TH-13: Comprehensive Naming Recommendations

Based on the analysis above, the following renamings would align the codebase with established proof-theoretic terminology:

| Current | Proposed | Justification |
|---|---|---|
| `freevar` (for metavars) | `metavar` | Distinct store tag; proof-theoretic clarity (TH-1) |
| `_normalizeBin` | `normalizeTRS` or `canonicalize` | Reflects equational theory (TH-2, TH-5) |
| `search()` in prove.js | `sldResolve()` | Standard name for the algorithm (TH-3) |
| `calc.types` | `calc.definitions` or `calc.clauseIndex` | Avoid type/clause conflation (TH-9) |
| `_backwardCache` | `_persistentMemo` or `_tabling` | Tabling literature (TH-6) |
| `matchAllLinear` | `focusedMatch` | Andreoli focusing protocol (TH-10) |
| "ephemeral expansion" | "equational normalization" | E-unification literature (TH-2) |
| `deepApply` | `hereditarySub` or `applySubst` | CLF hereditary substitution (TH-8) |
| `provePersistentNaive` | `proveUnrestricted` | CLF terminology: persistent = unrestricted (TH-3) |
| `resolveExistentials` | keep (already clear) | — |
| `applyMatch` | `fireTransition` or keep | CLF monadic let (TH-12) |

### TH-14: Mode Declarations and First-Argument Indexing

**Code**: `ffi/index.js:94` defines `defaultMeta` with mode strings like `'+ + -'`. `prove.js:getCandidates()` uses first-argument head-symbol indexing.

**Theory**: Mode declarations originate from **Twelf** (Pfenning, Schürmann). A mode `+ + -` means "input, input, output" — the first two arguments must be ground (determined) before the predicate is called, and the third is computed. This is a **moding discipline** that ensures:
1. **Termination**: if all input positions are ground, and the clause definitions are well-moded, then resolution terminates
2. **Determinism**: in many cases, well-moded predicates are functional (unique output for given inputs)

First-argument indexing is the WAM/Twelf standard for clause selection. The code's `getCandidates` groups clauses by first-argument tag — this is the same as Twelf's `%mode` + indexing.

**Gap**: The mode declarations in `defaultMeta` are only used for FFI dispatch and caching, not for mode-checking the backward prover. Adding a mode-checking pass (as Twelf does) would catch bugs where predicates are called with insufficient inputs.

### Execution Roadmap (Proof-Theoretic)

| Priority | Item | Risk | Size |
|---|---|---|---|
| P0 | TH-1: Introduce `metavar` store tag | Medium (store-wide) | Medium |
| P0 | TH-9: Rename `calc.types` → `calc.definitions` | None | Small |
| P1 | TH-6: Document tabling soundness invariant (cache clearing) | None | Tiny |
| P1 | TH-2: Rename ephemeral expansion → equational normalization | None | Small |
| P1 | TH-13: Naming pass (batch rename per table above) | None | Medium |
| P2 | TH-14: Mode-checking pass for backward prover | Low | Medium |
| P2 | TH-8: Unify substitution representation (Map vs union-find) | Medium | Large |

---

## Systems & Performance Engineering Audit

Audit of the kernel and engine code from the perspective of low-level systems engineering, compiler construction, and performance engineering. Informed by V8 internals, WAM (Warren Abstract Machine) optimization techniques, modern theorem prover implementations (Lean 4, Coq, E-prover), arena allocation patterns, and the upcoming Zig port.

### SYS-1: `Store.put()` Children Array — Dominant GC Pressure Source

**Code**: Every `Store.put(tag, children)` call site (match.js, substitute.js, compile.js, unify.js) allocates a fresh JS array for `children`. In `subCompiled` (substitute.js:274), the arity-1 and arity-2 fast paths allocate `[v0]` and `[v0, v1]` array literals per call.

**Impact**: In a typical EVM forward execution with 2000 steps, each step produces ~3 consequent facts via `subCompiled` → `Store.put`. That's ~6000 short-lived array allocations per run. V8's generational GC handles these reasonably (nursery collection), but this is the single largest source of GC pressure in the forward engine hot path.

**V8-specific**: Array literals `[v0, v1]` in a monomorphic call site are optimized by V8's TurboFan — they use a "fast elements" backing store with known length. But the array is still heap-allocated and must be GC'd.

**Fix (JS)**: Introduce `Store.put2(tag, c0, c1)` and `Store.put1(tag, c0)` that take children as direct arguments, avoiding array allocation entirely. The implementation writes directly to `child0[id]`, `child1[id]` without intermediary. This is the pattern used by WAM implementations: `MK_STRUCT(tag, arg0, arg1)` with fixed-arity specializations.

**Fix (Zig port)**: `pub fn put2(tag: u8, c0: u32, c1: u32) u32` — no allocator involved. The SoA arrays are `[]u32` slices over arena memory. Zero allocation per put.

**Estimated impact**: 30-50% reduction in GC pressure for forward.run, ~10-15% wall-clock speedup on arithmetic-heavy workloads.

### SYS-2: `hashCombine` Variadic Allocation

**Code**: `lib/hash.js:56` — `function hashCombine(...hashes)` uses rest parameters. Every call allocates an arguments array. Called from `computeHash` on every `Store.put`.

**V8-specific**: Rest parameters (`...hashes`) force V8 to allocate an `Arguments` object even in TurboFan-compiled code. The `for...of` loop over the rest array also creates an iterator.

**Fix (JS)**: Replace with a 2-argument version `hashCombine2(h1, h2)` that returns `Math.imul((h1 ^ h2) ^ ((h1 ^ h2) >>> 16), FNV_PRIME) >>> 0`. The existing `computeHash` already loops over children — inline the hash accumulation there instead of calling `hashCombine` per child. Remove the variadic version.

**Fix (Zig port)**: `fn hashCombine(a: u32, b: u32) u32` — single instruction sequence, no allocation.

### SYS-3: Forward.run State Cloning — O(groups) Allocations Per Step

**Code**: `forward.js:35` — `applyMatch` calls `state.clone()` → `state.snapshot()` which allocates one `Int32Array` per non-empty group (30-40 allocations). The old state is then GC'd.

**Contrast with explore.js**: The explore engine uses mutation+undo via Arena — zero allocation per step. `mutateState` modifies in-place; `FactSet.undo(arena, checkpoint)` restores in O(changed-facts) time.

**Analysis**: `forward.run` uses clone-per-step because it predates the Arena abstraction. The committed-choice semantics of `forward.run` (no backtracking) mean undo is never needed — but neither is cloning. Instead, mutate in-place with no arena at all, since each step is irrevocable.

**Fix**: Replace `applyMatch` with `mutateStateInPlace` that calls `consumeLinear`, `produceLinear`, `producePersistent` directly on the current state with `arena=null`. Remove `state.clone()` entirely. The only reason to keep the old state is for trace recording — snapshot only when `trace=true`.

**Estimated impact**: Eliminates ~30-40 TypedArray allocations per forward step. On a 2000-step EVM execution, this removes ~60,000-80,000 allocations. Expected 15-25% wall-clock speedup on forward.run.

### SYS-4: `FactSet.insert/remove` — O(n) Shift Operations

**Code**: `fact-set.js:109-131` — inserting into a sorted `Int32Array` group requires shifting all elements after the insertion point right by one. For a group with k elements, this is O(k) per insert. Similarly for remove.

**Impact**: For predicates with large fact populations (e.g., `mem` facts in EVM with 256+ entries), each insert/remove pays O(256) element copies. With ~4 bytes per element, this is 1KB of memmove per operation — not terrible, but adds up.

**WAM comparison**: WAM uses unsorted linked lists for clause chains. Insertion is O(1) (prepend). But lookup is O(n). The sorted array trades O(1) lookup (binary search) for O(n) mutation.

**Alternative**: **Unrolled B-tree** with Int32Array leaf nodes of 64 elements. Insert/remove at leaf is O(64) worst case (same as now for small groups), but for groups > 64, splits amortize to O(log n) per operation. Leaf nodes are cache-line-aligned (64 * 4 = 256 bytes = 4 cache lines).

**Zig alternative**: Use `std.ArrayList(u32)` with sorted insert, or `std.ArrayHashMap(u32, u32)` for O(1) insert + O(1) lookup. Since content-addressed hashes are unique, a hash set is sufficient for has/count queries. For ordered iteration (Zobrist hash update), maintain a sorted view lazily.

**Priority**: Medium — only matters for predicates with large populations (>64 facts). Most predicates in typical ILL programs have <10 facts.

### SYS-5: BigInt Arithmetic in E-Unification Hot Path

**Code**: `unify.js:687-695` — when matching `binlit(n)` against `i(X)` or `o(X)`, computes `value / 2n` and `value % 2n`. Both are BigInt operations. `Store.put('binlit', [value / 2n])` also hashes the BigInt via `hashBigInt` (hash.js:33) which iterates byte-by-byte with `val >>= 8n` and `Number(val & 0xFFn)`.

**V8-specific**: BigInt operations in V8 are not JIT-compiled — they go through a C++ runtime call. Each `value / 2n` is ~50-100x slower than a regular integer division. The byte-iteration in `hashBigInt` creates temporary BigInts on every shift/mask.

**Impact**: In EVM execution, nearly every arithmetic result goes through binlit normalization and matching. With 256-bit values (32 bytes), `hashBigInt` iterates 32 times per hash, each iteration allocating a temporary BigInt for the shift.

**Fix (JS)**: Pre-convert BigInts to `Uint8Array` representations at `Store.put` time. Store the byte array in a side table alongside the BigInt. Hash the byte array directly (no BigInt arithmetic needed). For the i/o pattern matching, use `value >> 1n` instead of `value / 2n` (bit shift is faster than division even for BigInts) and `value & 1n` instead of `value % 2n`.

**Fix (Zig port)**: Use `u256` (Zig supports arbitrary-width integers up to 65535 bits). Bit shift is a single instruction on x86-64 (SSE or pair of 64-bit shifts). Hash via direct memory cast: `@ptrCast(*[32]u8, &value)`. Zero allocation.

**Estimated impact**: 2-5x speedup on arithmetic-heavy backward proving (inc, shl, shr predicates). Moderate impact on forward engine (binlit normalization).

### SYS-6: Backward Prover Allocation Storm

**Code**: `prove.js:search()` — per recursion level:
1. `[...theta, ...newTheta]` — array spread creates new theta (O(|theta|))
2. `freshenTerm(typeHash, ...)` — creates `renamed: Map`, walks term recursively
3. `unifyUF(head, goalInst)` — creates `new UnionFind()` with `parent: Map`
4. `getCandidates()` — `[...(ti[fa]||[]), ...(ti['_']||[])]` — two array spreads

**Impact**: For a depth-5 proof search with 10 candidate clauses per level, this is: 50 Map allocations (UnionFind) + 50 Map allocations (freshen) + 250 array spreads (theta, getCandidates). Total: ~350 allocations per successful proof.

In the forward engine, `provePersistentNaive` calls `backward.prove()` for each persistent goal that can't be resolved via state lookup or tabling. On a complex EVM rule with 5 persistent goals, this is ~1750 allocations per rule firing.

**Fix (JS, incremental)**:
1. `getCandidates`: return a view (offset+length into pre-indexed array) instead of spreading. The index is already built by `buildIndex`.
2. `freshenTerm`: use a pre-allocated `Uint32Array(maxFreshVars)` renaming table indexed by fresh counter range, instead of a Map.
3. `theta`: use indexed theta (like the forward engine) instead of pair-list. Avoid spread — append in-place and truncate on backtrack.
4. `UnionFind`: pool and reuse. Clear the parent Map between unification attempts instead of creating new instances.

**Fix (Zig port)**: Arena allocator per search depth. Each recursion level gets a bump allocator region. On backtrack, reset the arena pointer — all per-level allocations freed in O(1). This is the standard pattern in Lean 4's elaborator and Coq's tactic engine.

**Estimated impact**: 5-10x speedup on backward proving for complex predicates. Marginal impact on forward engine hot path (backward proving is already behind state-lookup and tabling caches).

### SYS-7: `for...in` Object Key Enumeration in `consumeLinear`

**Code**: `state-ops.js:21` — `for (const hStr in consumed)` iterates object keys as strings. Each key requires `Number(hStr)` conversion.

**V8-specific**: `for...in` over plain objects triggers V8's enum cache. If the object was created with `consumed[hash] = count` where `hash` is a numeric uint32, V8 stores it as a "fast elements" integer-keyed property. But `for...in` converts all keys to strings regardless. The `Number(hStr)` conversion back to a number is an additional string-to-number parse per key.

**Fix (JS)**: Use a `Map<number, number>` for `consumed` instead of a plain object. Then iterate with `consumed.forEach((count, hash) => ...)`. Map iteration is numeric-typed — no string conversion. Alternatively, since consumed facts are always a small set (typically 1-4 entries), use two parallel arrays: `consumedHashes: Uint32Array(8)`, `consumedCounts: Uint8Array(8)`, `consumedLen: number`.

**Fix (Zig port)**: `consumed: [4]struct { hash: u32, count: u8 }` — stack-allocated fixed array. Iteration is a tight `for` loop over contiguous memory.

### SYS-8: `_poolConsumed.clear()` Cost in `tryMatch`

**Code**: `match.js` — `_poolConsumed`, `_poolReserved`, `_poolPreservedCount` are module-level `Map` instances cleared on every `tryMatch` call. `Map.clear()` in V8 is O(n) where n is the number of entries — it must walk the backing store and delete entries.

**Impact**: `tryMatch` is called for every candidate rule in every forward step. With 100 rules and fingerprint narrowing to ~5 candidates, that's 5 `Map.clear()` calls per step × 3 maps = 15 clears. If previous matches filled the maps with 3-5 entries, each clear touches 3-5 hash table slots.

**Fix (JS)**: Replace Maps with generation-counted arrays. Use `_poolConsumedGen: number` that increments on each `tryMatch` call. Store `{value, gen}` pairs. Lookup checks `gen === _poolConsumedGen`. "Clearing" is just incrementing the generation counter — O(1). This is the standard "generation stamp" technique from RETE engines.

**Alternative**: Since consumed typically has ≤4 entries, use parallel `Uint32Array(8)` buffers with a length counter. Clear is setting `len = 0` — O(1).

### SYS-9: Content-Addressed Store SoA Cache Locality

**Code**: `store.js:164-176` — six parallel TypedArrays (`tags`, `arities`, `child0`, `child1`, `child2`, `child3`), each 4M entries. Accessing a single node requires reads from 6 different memory locations (potentially 6 different cache lines for random access patterns).

**Analysis**: For sequential access (building indexes, serialization), the SoA layout is excellent — each array is a contiguous block, and iterating one array at a time maximizes spatial locality. But for random access (unification, matching, substitution), each `Store.tag(id)` + `Store.child(id, 0)` + `Store.child(id, 1)` hits 3 different arrays at the same offset, which are at least `4M * 1byte + 4M * 1byte + 4M * 4bytes = 20MB` apart in memory. These are almost certainly in different cache lines and possibly different pages.

**Impact**: On a modern CPU with 64-byte cache lines and 32KB L1d, the 6 arrays for 4M entries consume: `4M * (1+1+4+4+4+4) = 72MB` total. Random access patterns during unification trigger cache misses proportional to the number of distinct term IDs accessed per match.

**Lean 4 comparison**: Lean stores terms as tagged pointers with inline children — AoS (Array of Structures) layout. Each term access touches one contiguous cache line containing tag + all children. For terms with arity ≤ 3, one cache line (64 bytes) covers everything.

**Fix (Zig port)**: Use an AoS layout with packed structs:
```zig
const Term = packed struct {
    tag: u8,
    arity: u8,
    _pad: u16,
    children: [4]u32,
};
// sizeof(Term) = 20 bytes → 3.2 terms per cache line
```
This keeps tag + children contiguous. For sequential iteration, use SIMD to process 4 terms at a time.

**Alternative (hybrid)**: Keep SoA for `tags` and `arities` (used for filtering: "find all terms with tag X") but use AoS for children (used for structural access: "read all children of term X"). This gives best of both worlds.

**Priority for JS**: Not actionable (V8 TypedArrays don't support struct layouts). Important for Zig port architecture.

### SYS-10: Discrimination Tree — Allocation in `getCandidateRules`

**Code**: `disc-tree.js:199-235` — `getCandidateRules` allocates `results = []` and `seen = new Set()` on every call, plus `filtered = []`. In `explore.js`, this is called once per DFS node.

**Impact**: For an explore tree with 500 nodes, that's 500 array + 500 Set + 500 filtered-array allocations. The Set is used for deduplication — same rule can match via multiple facts.

**Fix (JS)**: Use a generation-stamped dedup. Each rule gets a `lastSeenGen: number` field. Increment `_queryGen` on each `getCandidateRules` call. Check `rule.lastSeenGen !== _queryGen` instead of `seen.has(r)`. This eliminates the Set allocation entirely. For `results` and `filtered`, use module-level pre-allocated arrays with length counters.

**E-prover comparison**: E uses timestamp-based dedup for clause selection — the exact same "generation stamp" pattern. It's standard in production theorem provers.

### SYS-11: `matchIndexed` Worklist — Array(64) vs Uint32Array

**Code**: `unify.js` — `_Gp` and `_Gt` are regular `Array(64)` holding term hashes (uint32 values). In V8, regular arrays store numbers as boxed `HeapNumber` objects in the worst case, or as 31-bit Smis in the best case. Term hashes are uint32 — they exceed the Smi range (which is -2^30 to 2^30-1 on 64-bit) when > 1,073,741,823.

**V8-specific**: V8's Smi range on 64-bit is [-2^31, 2^31-1] (implementation-dependent, typically uses pointer tagging). Values in the Smi range are stored inline (no allocation). Values outside Smi range are boxed as `HeapNumber` — each box is a heap allocation. Content-addressed store IDs are sequential starting from 1, so they stay in Smi range until ~2 billion terms. Safe for practical use.

**Fix (Zig port)**: `_Gp: [64]u32` — stack-allocated array, zero overhead.

### SYS-12: Theta Pair-List in Backward Prover vs Indexed Theta

**Code**: The forward engine uses `theta: Array(slotCount)` with `slots: { hash → index }` for O(1) lookup. The backward prover (prove.js) uses a pair-list `theta = [[var0, val0], [var1, val1], ...]` with O(n) linear scan per lookup.

**Impact**: The backward prover's `apply(term, theta)` does `for (let i = 0; i < theta.length; i += 2) if (theta[i] === hash)` — a linear scan per term node visited. With 20 bindings and a term tree of 50 nodes, that's 1000 comparisons per `apply` call. The forward engine's indexed version does 50 hash lookups — effectively O(50).

**WAM comparison**: WAM bindings are in registers or on the stack — binding lookup is a single array index (like the forward engine's indexed theta). No Prolog implementation uses linear scan for substitutions.

**Fix (JS)**: Port the backward prover to indexed theta. This requires assigning slots to clause variables at clause-compilation time (like `compileRule` does for forward rules). `buildIndex` should pre-assign slot tables per clause. The `search()` function then uses `theta[slot]` instead of pair-list scan.

**Estimated impact**: 5-20x speedup on deep backward proofs (10+ bindings, depth 5+). This is the single highest-ROI optimization for backward proving.

### SYS-13: `_resolveHash` — Iterative Post-Order with Per-Node Frame Allocation

**Code**: `prove.js:241` — `_resolveHash` uses an explicit stack `[[hash, childIndex, childResults, changed], ...]`. Each frame is a 4-element array allocated per compound node visited. For a term tree with 30 compound nodes, that's 30 array allocations.

**Fix (JS)**: Use pre-allocated frame arrays. Maintain a module-level `_resolveStack: Array(128)` where each slot is a pre-allocated `[0, 0, null, false]` frame. Reset frames on use instead of allocating. The stack depth is bounded by term depth (typically <20).

**Alternative**: Convert to a recursive implementation with depth guard. Term depth is typically 3-8 for ILL predicates. Stack overflow occurs at depth ~10,000 (V8 default). Recursion avoids all frame allocation.

**Note**: The iterative version was introduced specifically to fix stack overflow on deep theta chains (conversation context mentions `RangeError: Maximum call stack size exceeded`). The solution should keep the iterative structure but pre-allocate frames.

### SYS-14: DEDUP Map — JS Map vs Open-Addressing Hash Table

**Code**: `store.js:182` — `DEDUP = new Map()` maps content hash (uint32) to term index (uint32). V8's `Map` implementation uses a hash table with chaining. Each entry stores key, value, and a link pointer — ~24 bytes per entry on 64-bit.

**Impact**: With 10K terms, DEDUP uses ~240KB. This is fine. But V8's Map has overhead: hash computation for the Map key (redundant — our content hash IS the key), bucket lookup, chain traversal.

**Fix (JS)**: Use a TypedArray-based open-addressing hash table:
```javascript
const DEDUP_KEYS = new Uint32Array(capacity);   // content hash
const DEDUP_VALS = new Uint32Array(capacity);   // term index
const DEDUP_USED = new Uint8Array(capacity);     // occupancy flag
```
Lookup: linear probe on `DEDUP_KEYS[(hash + probe) & mask]`. Cache-friendly (keys are contiguous). No chaining overhead. Load factor 0.7 gives ~1.5 probes average.

**Zig port**: `std.AutoHashMap(u32, u32)` — open addressing with Robin Hood hashing. Or a custom hash table with the content hash as the key directly (no re-hashing needed since the key IS a hash).

**Estimated impact**: ~20-30% speedup on `Store.put()` hot path. Store.put is only hot during term construction (not during matching), so overall impact is moderate.

### SYS-15: `snapshot()/snapshotBulk()` — Copy-on-Write Opportunity

**Code**: `fact-set.js:232-275` — `snapshot()` copies each group's backing array. `snapshotBulk()` copies all groups into one buffer.

**Alternative**: **Copy-on-write (CoW)** groups. Each group is a `{ data: Int32Array, owned: bool }`. On `snapshot()`, create a new FactSet sharing the same data references with `owned = false`. On first mutation (`insert`/`remove`), if `!owned`, copy the backing array and set `owned = true`.

**Impact**: For explore.js where most groups are unchanged between parent and child states, CoW avoids copying unmodified groups entirely. Only the 1-3 groups that actually change get copied.

**Lean 4 comparison**: Lean 4's RC-based FBIP (Functional But In-Place) does exactly this — if the reference count is 1, mutate in place; otherwise copy. CoW is the manual equivalent.

**Priority**: Medium — explore.js already uses mutation+undo (better than CoW). This mainly benefits forward.run, which should switch to in-place mutation (SYS-3) anyway.

### SYS-16: `Store.child()` — Reconstructs String/BigInt on Every Call

**Code**: `store.js:407-411` — `child(id, i)` calls `reconstructChild(id, i)` which dispatches on tag type. For string-child tags (atom, freevar, strlit), it calls `stringTable.get(raw)` — a Map lookup returning a string. For BigInt-child tags (binlit, evar, bound), it calls `getBigInt(raw)` — an array index returning a BigInt.

**Hot-path concern**: In `matchIndexed` (unify.js:662), `Store.child(p, i)` is called for every child of every compound node in the worklist. If the child is a string (e.g., atom name), this triggers a Map lookup per call. In the worklist loop, the same atom children may be accessed multiple times (once during pattern flattening, once during structural comparison).

**V8 note**: `stringTable.get(raw)` returns a reference to an interned string — the string itself is not reallocated. The Map lookup is O(1) with integer key. This is acceptable.

**Fix (Zig port)**: Store a union directly in the child slots:
```zig
const Child = union(enum) { term: u32, string: u32, bigint: u32 };
```
No dispatch needed — the union tag is checked once. Or use the current approach (tag determines child interpretation) with `@intToEnum` at the call site.

### SYS-17: Tabling Key — String Concatenation

**Code**: `match.js:106` — backward cache key is built via `key = head` then `key += ':' + args[i]` per input argument. This creates intermediate strings on every cache lookup.

**Fix (JS)**: For predicates with ≤4 arguments (all current FFI predicates), use a numeric composite key:
```javascript
key = head_hash ^ (args[0] * 2654435761) ^ (args[1] * 2246822519);
```
Use the same Zobrist-style mixing as `hashFactEntry`. Collisions are acceptable for a cache (false miss → reprove, not unsound).

**Fix (Zig port)**: `key: u64 = @as(u64, head_hash) << 32 | hash_combine(input_args)`. Single comparison, no allocation.

### SYS-18: `explore.go()` Tree Node Allocation

**Code**: `explore.js:234` — each DFS step allocates `{ rule: m.rule.name, child }` and pushes to `children = []`. For multi-alt rules, additional `{ rule, choice, child }` objects. The final return is `{ type: 'branch', state: null, children }`.

**Impact**: An explore tree with 1000 nodes allocates ~1000 tree node objects + ~1000 children arrays + ~3000 `{rule, child}` edge objects = ~5000 allocations for tree construction alone.

**Fix (JS, if tree size is a problem)**: Encode the tree in flat arrays:
```javascript
const nodeTypes = new Uint8Array(maxNodes);    // 0=leaf, 1=branch, ...
const nodeStates = new Array(maxNodes);         // state snapshots (only for leaves)
const childStart = new Uint32Array(maxNodes);   // index into edges array
const childCount = new Uint16Array(maxNodes);   // number of children
const edgeRule = new Array(totalEdges);          // rule name per edge
const edgeTarget = new Uint32Array(totalEdges); // child node index
```
This replaces ~5000 objects with 6 pre-allocated arrays. Iteration is contiguous and cache-friendly.

**Priority**: Low for JS (tree construction is not the bottleneck — matching is). High for Zig port where flat arrays are natural and GC pressure doesn't exist.

### SYS-19: `Store.put()` — Linear Probing Collision vs Robin Hood

**Code**: `store.js:301-306` — on hash collision, linear probes up to 64 slots. The `matchesEntry` verification at each probe allocates a `[child0, child1, child2, child3]` array (line 256) per probe.

**Fix (JS)**: Inline the matching check without array allocation:
```javascript
function matchesEntry(id, tagName, c0, c1, c2, c3, arity) {
  if (tags[id] !== TAG[tagName] || arities[id] !== arity) return false;
  if (arity > 0 && child0[id] !== c0) return false;
  if (arity > 1 && child1[id] !== c1) return false;
  // ...
}
```
Pass children as individual arguments, matching the `put1`/`put2` specializations from SYS-1.

**Zig port**: Robin Hood hashing (used by `std.HashMap`) gives better worst-case probe lengths than linear probing. For the content-addressed store, the key IS the hash — so use identity-hash with open addressing. Expected probe length: 1.0 at load factor 0.5, 2.0 at 0.7.

### SYS-20: Forward Engine Architecture — Zig Port Blueprint

Summary of architectural decisions for the Zig port, drawing from all findings:

**Memory layout**:
- AoS term storage: `Term = packed struct { tag: u8, arity: u8, pad: u16, children: [4]u32 }` (20 bytes, fits in L1 with 3.2 terms/cache-line)
- Open-addressing hash table for DEDUP (identity-hash on content hash)
- Arena allocator for backward prover (per-search-depth regions, O(1) bulk free on backtrack)
- Stack-allocated theta arrays (comptime-known max slot count per rule)
- FactSet as `std.ArrayList(u32)` per tag, sorted

**Term operations**:
- `put2(tag, c0, c1) u32` — zero-allocation term construction
- Child access: `terms[id].children[i]` — single cache line
- Tag comparison: `terms[id].tag == TAG.binlit` — single byte compare

**Matching**:
- Worklist: `[64]struct { p: u32, t: u32 }` on stack (no heap allocation)
- Undo: `[32]u8` on stack for slot indices
- Theta: `[max_slots]?u32` on stack — null-initialized, O(1) slot access

**Forward engine**:
- In-place mutation with no undo (committed choice)
- `comptime` rule specialization: each compiled rule generates a specialized match function at compile time via Zig's comptime
- SIMD for binary search in FactSet groups: `@Vector(8, i32)` comparison against search key

**Backward prover**:
- Region-based allocation per recursion depth
- Indexed theta (pre-assigned slot tables per clause at compile time)
- `comptime` clause indexing: first-argument dispatch tables generated at compile time

**Explore**:
- Arena + undo log (same as current JS, but with zero-allocation Arena backed by `FixedBufferAllocator`)
- Generation-stamped cycle/memo detection (avoid Set allocations)
- Flat tree encoding (SYS-18)

### Execution Roadmap (Systems Engineering)

| Priority | Item | Speedup Est. | Risk | Size |
|---|---|---|---|---|
| P0 | SYS-3: In-place mutation for forward.run | 15-25% | Low | Small |
| P0 | SYS-1: `Store.put1/put2` arity specialization | 10-15% | Low | Small |
| P0 | SYS-2: Inline `hashCombine`, remove variadic | 5% | None | Tiny |
| P1 | SYS-12: Indexed theta for backward prover | 5-20x (backward) | Medium | Medium |
| P1 | SYS-5: Byte-array BigInt hashing | 2-5x (arith) | Low | Small |
| P1 | SYS-6: Pre-allocated frames in prove.js | 2-5x (backward) | Low | Medium |
| P1 | SYS-8: Generation-stamped pools in tryMatch | 5-10% | Low | Small |
| P1 | SYS-10: Generation-stamped dedup in disc-tree | 5% (explore) | Low | Small |
| P1 | SYS-7: Consumed as typed buffer, not string-keyed object | 3-5% | Low | Small |
| P2 | SYS-14: TypedArray DEDUP table | 20-30% (put) | Medium | Medium |
| P2 | SYS-17: Numeric tabling key | 5% | Low | Tiny |
| P2 | SYS-19: Inline matchesEntry, remove array alloc | 3% | None | Tiny |
| P3 | SYS-4: Unrolled B-tree for large FactSet groups | Marginal | High | Large |
| P3 | SYS-15: CoW FactSet groups | Marginal | Medium | Medium |
| P3 | SYS-18: Flat tree encoding for explore | Marginal (JS) | Medium | Large |

**Recommended execution order** (JS, before Zig port):
1. SYS-3 + SYS-1 + SYS-2 (three small changes, cumulative 25-40% on forward.run)
2. SYS-8 + SYS-10 + SYS-7 (generation stamps + typed buffers, reduce per-step allocation overhead)
3. SYS-12 + SYS-6 (backward prover modernization — indexed theta + pooled frames)
4. SYS-5 (BigInt optimization — important for arithmetic-heavy workloads)

**Zig port priorities**: SYS-9 (AoS layout), SYS-20 (architecture blueprint), then backport learnings to JS where applicable.
