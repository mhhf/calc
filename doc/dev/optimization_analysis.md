# Prover Optimization Analysis

## Executive Summary

Similar to the content-addressed hash bug (where we computed hashes redundantly instead of using hashes as pointers), we have another architectural issue: **we maintain two parallel representations of linear resources and constantly convert between them**.

## The Core Problem: Dual Representation

We maintain TWO representations of the same data:

| Representation | Format | Purpose |
|----------------|--------|---------|
| `seq.contexts.linear` | Array of hashes | "What formulas are available" |
| `delta` | Multiset `{hash: count}` | "What resources remain" |

**They contain the same information!**

### The Conversion Dance (called on EVERY recursive search call)

```
search(seq, delta)
    │
    ├─► applyRule creates premise (new sequent with partial linear)
    │
    ├─► addDeltaToSequent merges delta INTO premise.linear
    │       ├─► Context.toArray(delta)         // multiset → array
    │       ├─► Seq.copy(premise)              // Object.entries/fromEntries
    │       └─► loop: Seq.addToContext         // N new sequent objects
    │
    ├─► Context.fromArray(Seq.getContext(...)) // array → multiset (BACK!)
    │
    └─► search(mergedSeq, extractedDelta)      // same info, two formats
```

**This is ~25% of total runtime!**

## Optimization #1: Eliminate Dual Representation (~25% savings)

### Current Flow
```javascript
const search = (seq, state, depth, delta) => {
  // seq.linear and delta contain same resources!
  for (const premise of result.premises) {
    const premiseWithDelta = addDeltaToSequent(premise, currentDelta);
    const childDelta = Context.fromArray(Seq.getContext(premiseWithDelta, 'linear'));
    search(premiseWithDelta, ..., childDelta);
  }
}
```

### Optimized Flow
```javascript
const search = (goal, delta, cartesian, state, depth) => {
  // delta IS the linear resources (single source of truth)
  // No conversion needed!
  for (const premise of result.premises) {
    const childDelta = computeChildDelta(delta, premise);  // Direct multiset ops
    search(premise.goal, childDelta, cartesian, ...);
  }
}
```

### What Changes
- Remove `addDeltaToSequent` entirely
- Remove most `Context.fromArray` calls
- Rules work directly with multiset delta
- Only create Sequent for ProofTree output at the end
- Identify formulas by hash, not array index

### Why This Works
With content-addressed hashes:
- **Hash IS the identity** - don't need array index
- **Removal by hash is O(1)** - `Context.remove(delta, hash)`
- **Multiset is the natural representation** for linear logic resources

## Optimization #2: Cache Store.get in unify (~2-3% savings)

### Current (6 Store.get calls per pair)
```javascript
if (isMetavar(t0)) {           // Store.get(t0) #1
if (isMetavar(t1)) {           // Store.get(t1) #1
if (isFreevar(t0) && ...       // Store.get(t0) #2
    ... && isFreevar(t1)) {    // Store.get(t1) #2
const n0 = Store.get(t0);      // Store.get(t0) #3
const n1 = Store.get(t1);      // Store.get(t1) #3
```

### Optimized (2 Store.get calls per pair)
```javascript
const n0 = Store.get(t0);
const n1 = Store.get(t1);

// Inline checks using cached nodes
const isMeta0 = n0?.tag === 'freevar' && n0.children[0]?.startsWith?.('_');
const isMeta1 = n1?.tag === 'freevar' && n1.children[0]?.startsWith?.('_');
// Use n0, n1, isMeta0, isMeta1 for rest of logic
```

## Optimization #3: Fix Context.isEmpty (~1-2% savings)

### Current (allocates array)
```javascript
const isEmpty = (ms) => Object.keys(ms).length === 0;
```
- Called 1,882 times per proof
- Each call allocates array of all keys

### Optimized (no allocation)
```javascript
const isEmpty = (ms) => {
  for (const _ in ms) return false;
  return true;
};
```

## Optimization #4: Use Hash as Identity (enables #1)

### Current (array index)
```javascript
findInvertible returns { position: 'L', index: i, formula: h }
applyRule uses: Seq.getContext(seq, 'linear')[index]
```

### Optimized (hash identity)
```javascript
findInvertible returns { position: 'L', formula: h }  // h IS the ID
applyRule uses: formula directly
Context.remove(delta, h)  // O(1) removal by hash
```

## Expected Impact

| Optimization | Current Cost | Expected Savings |
|--------------|--------------|------------------|
| Eliminate dual representation | ~25% | ~20-25% |
| Cache Store.get in unify | ~7% | ~2-3% |
| Fix Context.isEmpty | ~3% | ~1-2% |
| **Total** | | **~25-30%** |

## Implementation Priority

1. **Fix Context.isEmpty** - One-line change, immediate benefit
2. **Cache Store.get in unify** - Small refactor, clear benefit
3. **Eliminate dual representation** - Larger refactor, biggest benefit

## Philosophical Note

This is the same class of bug as the content-addressed hashing issue:

| Bug | What we designed | What we implemented |
|-----|------------------|---------------------|
| Hashing | Hash = identity, O(1) compare | Recompute hash every time |
| Resources | Multiset = truth, O(1) ops | Convert array↔multiset constantly |

The fix is the same: **use the efficient representation as the source of truth, don't convert back and forth**.
