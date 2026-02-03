# Prover Profiling Report

Sequent: `A & B, C & D, E & F |- (A*C*E) & (B*D*F)`

## Complete Time Breakdown

### Directly Measured (33.2% JavaScript)

| Function | % | Description |
|----------|---|-------------|
| FindOrderedHashMapEntry (Map.get) | 7.2% | Store lookups |
| unify | 4.3% | Unification |
| search | 3.9% | Main proof search |
| KeyedLoadIC_Megamorphic | 3.6% | Object property access |
| addDeltaToSequent | 2.0% | Context→Sequent conversion |
| findInvertible | 1.9% | Inversion phase |
| ArrayIteratorPrototypeNext | 1.2% | for-of loops |
| chooseFocus | 0.9% | Focus selection |
| applyRule | 0.8% | Rule application |
| Other JS builtins | 7.4% | Clone, toString, etc. |

### C++ / System (3.5%)

| Function | % | Description |
|----------|---|-------------|
| pthread locks, memcpy, malloc | 3.5% | System calls |

### GC (2.3%)

| Function | % | Description |
|----------|---|-------------|
| Garbage collection | 2.3% | Memory management |

### "Unaccounted" (63.3%) - Breakdown

This is time spent IN the JS functions but not sampled at a specific instruction. The bottom-up profile shows it's distributed as:

| Category | % of Unaccounted | Description |
|----------|------------------|-------------|
| Object operations in addDeltaToSequent | ~19% | ObjectEntries/FromEntries |
| Rule application overhead | ~14% | applyRule internals |
| Recursive search overhead | ~11% | call stack management |
| Context operations | ~7% | remove, fromArray |
| Object.keys (isEmpty checks) | ~3% | frequent empty checks |
| Other distributed work | ~9% | various |

## Operation Counts (per proof)

| Operation | Calls |
|-----------|-------|
| Store.get() | 55,185 |
| Store.tag() | 25,517 |
| Seq.getContext() | 17,620 |
| Context.fromArray() | 3,868 |
| Seq.addToContext() | 3,583 |
| Context.remove() | 1,167 |

## Key Findings

### Content-Addressed Fix Results
- ✓ No more redundant hashing (was 82K hashAST calls, now 0)
- ✓ eq() is O(1) now (just number comparison)

### Current Bottlenecks

1. **addDeltaToSequent (~21% total)** - The hidden bottleneck
   - ObjectEntries: 15.8% of unaccounted
   - ObjectFromEntries: 8.4% of unaccounted
   - ObjectKeys: 5.4% of unaccounted

2. **Store.get() (~7%)** - 55K calls/proof, but each is O(1)

3. **unify (~4-7%)** - Calls Store.get multiple times per pair

## The Hidden Bottleneck: addDeltaToSequent

This function (prover.js:419) accounts for ~21% of total time:

```javascript
const addDeltaToSequent = (seq, delta, copy = false) => {
  if (Context.isEmpty(delta)) return seq;

  const arr = Context.toArray(delta);      // Creates array
  let newSeq = Seq.copy(seq);              // Object.entries + fromEntries

  for (const h of arr) {
    newSeq = Seq.addToContext(newSeq, 'linear', h);  // N new objects
  }

  return newSeq;
};
```

**Problem:** Converts Context ↔ Sequent for EVERY rule application
- Calls Context.toArray (creates new array)
- Calls Seq.copy (Object.entries + Object.fromEntries)
- Calls Seq.addToContext in a loop (creates N new sequent objects)

## Top Optimization Targets

1. **addDeltaToSequent (~21% total)**
   - Fix: Work with multiset context directly, avoid Sequent rebuilding

2. **Context.isEmpty using Object.keys (~3-5%)**
   - Problem: `Object.keys(ms).length === 0` allocates an array
   - Fix: Track size separately or use for-in with early return

3. **unify calling Store.get repeatedly (~4-7% total)**
   - Problem: isMetavar, isFreevar each call Store.get
   - Fix: Cache node lookup, combine checks
