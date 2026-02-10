# Persistent Data Structures for Proof Search

Deep dive into immutable data structures with structural sharing for efficient backtracking.

> **See also:** [[content-addressed-formulas]] for Merkle-DAG hash consing, [[backward-prover-optimization]] for overall optimization strategy, [[explicit-substitutions]] for lazy evaluation.

---

## Table of Contents

1. [The Problem: Copying is Expensive](#1-the-problem-copying-is-expensive)
2. [Persistent Data Structures: Core Concept](#2-persistent-data-structures-core-concept)
3. [HAMT: Hash Array Mapped Trie](#3-hamt-hash-array-mapped-trie)
4. [Application to Proof Search](#4-application-to-proof-search)
5. [Complexity Comparison](#5-complexity-comparison)
6. [Integration with Merkle-DAG](#6-integration-with-merkle-dag)
7. [Implementation Options](#7-implementation-options)
8. [Recommendation](#8-recommendation)
9. [References](#9-references)

---

## 1. The Problem: Copying is Expensive

### Current Copying Pattern

In proof search, we frequently copy entire data structures:

```javascript
// sequent.js:209-229
Sequent.copy = function (seq) {
  let linear_ctx = {};
  Object.keys(seq.linear_ctx)
  .forEach(id => {
    let r = seq.linear_ctx[id];
    linear_ctx[id] = {num: r.num, val: r.val.copy()};  // Deep copy every formula!
  });
  let persistent_ctx = {};
  Object.keys(seq.persistent_ctx)
  .forEach(id => {
    persistent_ctx[id] = seq.persistent_ctx[id].copy()  // Deep copy here too!
  });
  let succedent = seq.succedent.copy();  // And here!
  return new Sequent({ persistent_ctx, linear_ctx, succedent });
}
```

### Where Copying Happens

1. **Focus operation**: `Sequent.copy(pt.conclusion)` (proofstate.js:507)
2. **Rule application**: Each premise gets copied context
3. **Backtracking**: JavaScript GC cleans up, but we already paid the cost
4. **Substitution**: Creates new sequent with modified formulas

### The Cost

For a sequent with m formulas, each of size n:
- **Sequent.copy**: O(m·n) - copies every formula
- **Rule application**: O(m·n) per premise
- **Proof tree of depth d**: O(d·m·n) total copying

### The Waste

Most copied formulas are **never modified**:
- Copying 20 formulas, modifying 2 → 90% waste
- Backtracking discards everything anyway
- Formulas in persistent context are literally never modified!

**Observation:** We do O(m) work when O(1) would suffice.

---

## 2. Persistent Data Structures: Core Concept

### Immutable with Structural Sharing

A **persistent** data structure preserves all previous versions after modification.

```
Original:    [A, B, C, D, E]
                    │
Update C→C':        │
                    ▼
             [A, B, C', D, E]  ← New version

Original still exists and is unchanged!
```

But we don't copy everything - we **share** unchanged parts:

```
Original:  root ─┬─ A
                 ├─ B
                 ├─ C
                 ├─ D
                 └─ E

Update C→C':

New root ──┬─ A  ← (shared)
           ├─ B  ← (shared)
           ├─ C' ← (new)
           ├─ D  ← (shared)
           └─ E  ← (shared)
```

### Path Copying

Only nodes on the path from root to modification point are copied:

```
HAMT with 32-way branching, depth 7:
- Total capacity: 32^7 = 34 billion entries
- Update cost: log₃₂(n) ≈ 7 node copies max
- Each node: ~32 pointers + bitmap = ~256 bytes

Update in map of 1 million entries:
- Naive copy: 1,000,000 entries × 8 bytes = 8 MB
- HAMT path copy: ~4 nodes × 256 bytes = 1 KB
- Speedup: 8000×!
```

---

## 3. HAMT: Hash Array Mapped Trie

### Structure

A **HAMT** (Hash Array Mapped Trie) is the standard persistent map implementation:

```javascript
class HAMTNode {
  constructor() {
    this.bitmap = 0;        // 32-bit: which children exist
    this.children = [];     // Dense array of actual children
  }
}

// Key lookup uses hash bits as path
function get(root, key) {
  let hash = hashOf(key);
  let node = root;
  let depth = 0;

  while (node) {
    let frag = (hash >>> (depth * 5)) & 0x1F;  // 5 bits = 0-31
    let bit = 1 << frag;

    if ((node.bitmap & bit) === 0) {
      return undefined;  // Path doesn't exist
    }

    let index = popcount(node.bitmap & (bit - 1));  // Dense index
    let child = node.children[index];

    if (isLeaf(child)) {
      return child.key === key ? child.value : undefined;
    }

    node = child;
    depth++;
  }
  return undefined;
}
```

### Bitmap Magic

The bitmap enables O(1) child lookup with dense storage:

```
Conceptual array (32 slots):
[null, A, null, null, B, null, ..., C, ...]
   0   1    2     3   4   ...    16

Bitmap: 0b00000000_00000001_00000000_00010010
                                         ││
                                         │└─ Bit 1 = A exists
                                         └── Bit 4 = B exists
                                    ↑
                                    Bit 16 = C exists

Dense array: [A, B, C]

To find index of B (bit 4):
  popcount(bitmap & (0b10000 - 1))
= popcount(bitmap & 0b01111)
= popcount(0b00010)  // Only bit 1 is set below bit 4
= 1                  // So B is at dense index 1 ✓
```

### Persistent Update

Updates create new nodes along the path:

```javascript
function set(root, key, value) {
  let hash = hashOf(key);
  return setRecursive(root, hash, 0, key, value);
}

function setRecursive(node, hash, depth, key, value) {
  let frag = (hash >>> (depth * 5)) & 0x1F;
  let bit = 1 << frag;
  let index = popcount(node.bitmap & (bit - 1));

  if ((node.bitmap & bit) === 0) {
    // Insert new child
    let newChildren = [...node.children];
    newChildren.splice(index, 0, { key, value });
    return new HAMTNode(node.bitmap | bit, newChildren);
  }

  let child = node.children[index];

  if (isLeaf(child)) {
    if (child.key === key) {
      // Replace value
      let newChildren = [...node.children];
      newChildren[index] = { key, value };
      return new HAMTNode(node.bitmap, newChildren);
    } else {
      // Collision: create subtrie
      let subtrie = createSubtrie(child, { key, value }, depth + 1);
      let newChildren = [...node.children];
      newChildren[index] = subtrie;
      return new HAMTNode(node.bitmap, newChildren);
    }
  }

  // Recurse into subtrie
  let newChild = setRecursive(child, hash, depth + 1, key, value);
  let newChildren = [...node.children];
  newChildren[index] = newChild;
  return new HAMTNode(node.bitmap, newChildren);
}
```

---

## 4. Application to Proof Search

### Persistent Sequent

```javascript
class PersistentSequent {
  constructor(linearCtx, persistentCtx, succedent) {
    this.linearCtx = linearCtx;         // HAMT: hash → {num, formulaHash}
    this.persistentCtx = persistentCtx; // HAMT: hash → formulaHash
    this.succedent = succedent;         // Formula hash
    this._hash = null;                  // Cached sequent hash
  }

  // Add to linear context - O(log m)
  addLinear(formulaHash, num = 1) {
    const existing = this.linearCtx.get(formulaHash);
    const newEntry = existing
      ? { num: existing.num + num, formulaHash }
      : { num, formulaHash };

    return new PersistentSequent(
      this.linearCtx.set(formulaHash, newEntry),  // Path copy!
      this.persistentCtx,                          // Shared!
      this.succedent                               // Shared!
    );
  }

  // Remove from linear context - O(log m)
  removeLinear(formulaHash, num = 1) {
    const existing = this.linearCtx.get(formulaHash);
    if (!existing) return null;  // Can't remove what doesn't exist

    if (existing.num <= num) {
      return new PersistentSequent(
        this.linearCtx.delete(formulaHash),
        this.persistentCtx,
        this.succedent
      );
    }

    return new PersistentSequent(
      this.linearCtx.set(formulaHash, { num: existing.num - num, formulaHash }),
      this.persistentCtx,
      this.succedent
    );
  }

  // Set succedent - O(1)
  setSuccedent(formulaHash) {
    return new PersistentSequent(
      this.linearCtx,      // Shared!
      this.persistentCtx,  // Shared!
      formulaHash
    );
  }

  // Iterate (for display, rule matching) - O(m)
  *linearEntries() {
    for (const [hash, entry] of this.linearCtx) {
      yield [hash, entry];
    }
  }
}
```

### Backtracking = Free!

```javascript
// Proof search with automatic "undo"
function proofSearch(sequent, depth = 0) {
  if (isAxiom(sequent)) {
    return { success: true, proof: axiomProof(sequent) };
  }

  for (const rule of applicableRules(sequent)) {
    // Generate premises
    const premises = applyRule(sequent, rule);  // Returns new sequents

    let allSucceed = true;
    const subproofs = [];

    for (const premise of premises) {
      const result = proofSearch(premise, depth + 1);  // Recurse
      if (!result.success) {
        allSucceed = false;
        break;  // Backtrack! But sequent is unchanged (immutable)
      }
      subproofs.push(result.proof);
    }

    if (allSucceed) {
      return { success: true, proof: buildProof(rule, subproofs) };
    }
    // Automatic backtrack - sequent was never mutated
  }

  return { success: false };
}
```

**Key insight:** No explicit undo needed! The original sequent persists unchanged.

---

## 5. Complexity Comparison

### Current (Mutable with Copying)

| Operation | Time | Space |
|-----------|------|-------|
| Copy sequent | O(m·n) | O(m·n) |
| Add formula | O(1) | O(1) |
| Remove formula | O(1) | O(1) |
| Backtrack | O(m·n) copy cost already paid | GC reclaims |

### With HAMT (Persistent)

| Operation | Time | Space |
|-----------|------|-------|
| "Copy" sequent | O(1) | O(1) - just share reference |
| Add formula | O(log m) | O(log m) path nodes |
| Remove formula | O(log m) | O(log m) path nodes |
| Backtrack | O(1) - keep old reference | O(log m) garbage |

### Full Proof Search Analysis

Let:
- d = proof depth
- b = branching factor
- m = context size
- n = formula size

**Current approach:**
```
Copying per node: O(m·n)
Total nodes explored: O(b^d)
Total cost: O(b^d · m · n)
```

**With persistent structures:**
```
Update per node: O(log m)
Total nodes explored: O(b^d)
Total cost: O(b^d · log m)
```

**Speedup: O(m·n / log m) ≈ 100-1000× for typical values!**

---

## 6. Integration with Merkle-DAG

### Natural Fit

With content-addressed formulas, our "values" are already hashes:

```javascript
class PersistentSequent {
  constructor(linearCtx, persistentCtx, succedentHash) {
    // linearCtx: HAMT<FormulaHash, {num: number}>
    // All "values" are already small fixed-size hashes!
    this.linearCtx = linearCtx;
    this.persistentCtx = persistentCtx;
    this.succedentHash = succedentHash;
  }
}
```

Benefits:
1. HAMT nodes are small (just hashes)
2. Formula storage is separate (in Store)
3. Hash-based keys give uniform distribution
4. Equality is O(1) - compare hashes

### Sequent Hashing

```javascript
class PersistentSequent {
  get hash() {
    if (this._hash) return this._hash;

    // Hash is computed from sorted context hashes
    const linearHashes = [...this.linearCtx.keys()].sort();
    const persistentHashes = [...this.persistentCtx.keys()].sort();

    this._hash = hashCombine(
      hashArray(linearHashes),
      hashArray(persistentHashes),
      this.succedentHash
    );
    return this._hash;
  }
}
```

---

## 7. Implementation Options

### Option 1: Use Immutable.js

```javascript
const { Map } = require('immutable');

class PersistentSequent {
  constructor(linearCtx, persistentCtx, succedent) {
    this.linearCtx = linearCtx || Map();      // Immutable.Map
    this.persistentCtx = persistentCtx || Map();
    this.succedent = succedent;
  }

  addLinear(hash, num = 1) {
    const existing = this.linearCtx.get(hash);
    return new PersistentSequent(
      this.linearCtx.set(hash, (existing || 0) + num),
      this.persistentCtx,
      this.succedent
    );
  }
}
```

**Pros:** Battle-tested, well-optimized, no implementation effort
**Cons:** External dependency (~60KB), some overhead

### Option 2: Minimal Custom HAMT

```javascript
// Minimal HAMT for our use case (string keys, small values)
const BITS = 5;
const WIDTH = 1 << BITS;  // 32
const MASK = WIDTH - 1;

class HAMTNode {
  constructor(bitmap = 0, children = []) {
    this.bitmap = bitmap;
    this.children = children;
  }

  static EMPTY = new HAMTNode();
}

function get(node, hash, shift = 0) {
  if (!node || node === HAMTNode.EMPTY) return undefined;

  const frag = (hash >>> shift) & MASK;
  const bit = 1 << frag;

  if ((node.bitmap & bit) === 0) return undefined;

  const idx = popcount(node.bitmap & (bit - 1));
  const child = node.children[idx];

  if (child.isLeaf) {
    return child.hash === hash ? child.value : undefined;
  }

  return get(child, hash, shift + BITS);
}

function set(node, hash, value, shift = 0) {
  const frag = (hash >>> shift) & MASK;
  const bit = 1 << frag;
  const idx = popcount(node.bitmap & (bit - 1));

  if ((node.bitmap & bit) === 0) {
    // Insert
    const newChildren = [...node.children];
    newChildren.splice(idx, 0, { isLeaf: true, hash, value });
    return new HAMTNode(node.bitmap | bit, newChildren);
  }

  const child = node.children[idx];
  const newChildren = [...node.children];

  if (child.isLeaf) {
    if (child.hash === hash) {
      // Update
      newChildren[idx] = { isLeaf: true, hash, value };
    } else {
      // Collision - create subtrie
      newChildren[idx] = set(
        set(HAMTNode.EMPTY, child.hash, child.value, shift + BITS),
        hash, value, shift + BITS
      );
    }
  } else {
    // Recurse
    newChildren[idx] = set(child, hash, value, shift + BITS);
  }

  return new HAMTNode(node.bitmap, newChildren);
}

// Fast popcount for 32-bit integers
function popcount(n) {
  n = n - ((n >>> 1) & 0x55555555);
  n = (n & 0x33333333) + ((n >>> 2) & 0x33333333);
  return (((n + (n >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24;
}
```

**Pros:** Minimal code (~100 lines), no dependencies, tailored to our needs
**Cons:** Need to implement and test ourselves

### Option 3: Plain Objects with COW

Copy-on-write with plain JavaScript objects:

```javascript
class COWSequent {
  constructor(linearCtx, persistentCtx, succedent, shared = false) {
    this.linearCtx = linearCtx || {};
    this.persistentCtx = persistentCtx || {};
    this.succedent = succedent;
    this.shared = shared;  // Is this a shared reference?
  }

  // Mark as shared (enables COW)
  share() {
    return new COWSequent(
      this.linearCtx,
      this.persistentCtx,
      this.succedent,
      true
    );
  }

  // Get mutable copy if shared, otherwise return this
  _getMutable() {
    if (!this.shared) return this;
    return new COWSequent(
      { ...this.linearCtx },      // Shallow copy
      { ...this.persistentCtx },
      this.succedent,
      false
    );
  }

  addLinear(hash, num = 1) {
    const seq = this._getMutable();
    const existing = seq.linearCtx[hash];
    seq.linearCtx[hash] = (existing || 0) + num;
    return seq;
  }
}
```

**Pros:** Simple, uses native objects, fast for small contexts
**Cons:** Degrades to O(m) for large contexts, not truly persistent

---

## 8. Recommendation

### Verdict: **IMPLEMENT** (after content-addressing)

**Priority:** MEDIUM

**Effort:** LOW (Immutable.js) or MEDIUM (custom HAMT)

### Rationale

**Pros:**
1. Eliminates O(m·n) copying → O(1) sharing
2. Backtracking becomes free
3. Natural fit with content-addressed formulas
4. Enables cheap memoization (sequent identity by hash)
5. Memory-efficient for deep proof trees

**Cons:**
1. Adds dependency (Immutable.js) or implementation effort (custom)
2. O(log m) updates instead of O(1) - but copying was O(m)!
3. Slight constant-factor overhead
4. Debugging shows references, not copies

### When It's Worth It

- **Proof trees with depth > 10** - copying compounds
- **Large contexts (m > 20)** - copying is expensive
- **High backtracking** - many failed branches
- **Memory-constrained** - sharing reduces footprint

### When It's NOT Worth It

- **Tiny proofs** - overhead dominates
- **Linear proofs** - no backtracking benefit
- **Small contexts** - O(log m) ≈ O(m) for small m

### Recommended Implementation Order

1. **Phase 1 (Content-Addressing):** Implement Merkle-DAG store
2. **Phase 2 (Persistent Sequent):** Use Immutable.js for contexts
3. **Phase 3 (Optimization):** If Immutable.js is slow, implement minimal HAMT

### Starter Code

```javascript
const { Map } = require('immutable');

class PersistentSequent {
  constructor({ linearCtx, persistentCtx, succedentHash, store }) {
    this.linearCtx = linearCtx || Map();
    this.persistentCtx = persistentCtx || Map();
    this.succedentHash = succedentHash;
    this.store = store;
    this._hash = null;
  }

  static fromSequent(seq, store) {
    let linearCtx = Map();
    for (const [id, entry] of Object.entries(seq.linear_ctx)) {
      const hash = store.intern(entry.val);
      linearCtx = linearCtx.set(hash, entry.num);
    }

    let persistentCtx = Map();
    for (const [id, val] of Object.entries(seq.persistent_ctx)) {
      const hash = store.intern(val);
      persistentCtx = persistentCtx.set(hash, true);
    }

    const succedentHash = store.intern(seq.succedent);

    return new PersistentSequent({ linearCtx, persistentCtx, succedentHash, store });
  }

  addLinear(formulaHash, num = 1) {
    const existing = this.linearCtx.get(formulaHash) || 0;
    return new PersistentSequent({
      linearCtx: this.linearCtx.set(formulaHash, existing + num),
      persistentCtx: this.persistentCtx,
      succedentHash: this.succedentHash,
      store: this.store
    });
  }

  removeLinear(formulaHash, num = 1) {
    const existing = this.linearCtx.get(formulaHash);
    if (!existing || existing < num) return null;

    const newCtx = existing === num
      ? this.linearCtx.delete(formulaHash)
      : this.linearCtx.set(formulaHash, existing - num);

    return new PersistentSequent({
      linearCtx: newCtx,
      persistentCtx: this.persistentCtx,
      succedentHash: this.succedentHash,
      store: this.store
    });
  }

  get hash() {
    if (this._hash) return this._hash;
    this._hash = this.store.hashSequent(this);
    return this._hash;
  }
}

module.exports = { PersistentSequent };
```

---

## 9. References

- [HAMT in JavaScript](https://blog.mattbierner.com/hash-array-mapped-tries-in-javascript/)
- [Immutable.js](https://immutable-js.com/)
- [Clojure Persistent Data Structures](https://hypirion.com/musings/understanding-persistent-vector-pt-1)
- [Phil Bagwell: Ideal Hash Trees](https://infoscience.epfl.ch/record/64398)
- [Optimizing HAMTs for Fast and Lean Immutable Collections](https://michael.steindorfer.name/publications/oopsla15.pdf)
