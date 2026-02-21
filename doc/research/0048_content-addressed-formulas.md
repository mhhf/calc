---
title: "Content-Addressed Formulas, Terms, and Sequents"
created: 2026-02-10
modified: 2026-02-10
summary: "Research on Merkle-DAG hash consing techniques, design space for content-addressed AST storage, and hash function selection. CALC's current implementation is documented in doc/documentation/content-addressed-store.md."
tags: [hash-consing, Merkle-DAG, optimization, content-addressing, equality]
category: "Performance"
---

# Content-Addressed Formulas, Terms, and Sequents

Research document for CALC project: designing efficient identity and equality checking for logical objects.

> **See also:** [[dev/constructor-indexing]] for O(1) identity lookup using hash indexes, [[benchmarking]] for complexity analysis of current implementation.

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Current Implementation Analysis](#current-implementation-analysis)
3. [Chosen Approach: Merkle-DAG Hash Consing](#chosen-approach-merkle-dag-hash-consing)
4. [Hash Function Selection](#hash-function-selection)
5. [Merkle-DAG Hash Consing Implementation](#merkle-dag-hash-consing-implementation)
6. [Memory Management Strategies](#memory-management-strategies)
7. [Substitution in Merkle-DAG Store](#substitution-in-merkle-dag-store)
8. [Integration with Proof Search](#integration-with-proof-search)
9. [Complexity Analysis](#complexity-analysis)
10. [Implementation Roadmap](#implementation-roadmap)
11. [References](#references)

---

## Problem Statement

During proof search, CALC constantly:
- Compares formulas and sequents for equality
- Creates copies of ASTs during rule application
- Tracks which formulas appear in contexts (multisets)
- Memoizes proof states to avoid redundant search

The current implementation uses **O(n) string serialization** for equality and **O(n) deep copying** throughout. This is a significant performance bottleneck that will become critical for:
- Complex proofs with large formulas
- Exhaustive proof search
- Future Zig export for high-performance proving

**Goal:** O(1) equality checking, O(1) structural identity, efficient memory use through sharing.

---

## Current Implementation Analysis

### node.js — AST Nodes

```javascript
class Node {
  constructor (id, vals) {
    this.id = id;      // Integer rule ID from Calc.db.rules
    this.vals = vals;  // Array of child nodes or strings
  }
  copy() {
    return new Node(this.id,
      this.vals.map(v => (typeof v === "object") ? v.copy() : v))
  }
}
```

**Issues:**
- `id` is rule type, NOT content identifier
- `copy()` is O(n) deep copy — called frequently
- No structural sharing between identical subtrees
- Equality requires full structural comparison

### sequent.js — Sequent Representation

```javascript
// Uses SHA3 hash of toString() for context keys
let id = sha3(ast.toString())
if(id in seq.linear_ctx) {
  seq.linear_ctx[id].num += num;
} else {
  seq.linear_ctx[id] = {num: num, val: ast}
}
```

**Issues:**
- `sha3(ast.toString())` is O(n) per formula
- Called on every context operation
- Browser fallback uses weak djb2 hash (collision risk)
- Hash computed repeatedly, not cached

### mgu.js — Unification

```javascript
let isEq = t0.toString() === t1.toString();  // O(n) equality
// ...
theta = propagate(theta, [[t0, t1]])
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))  // O(n) substitutions
```

**Issues:**
- Equality via string comparison: O(n)
- Substitutions create copies: O(n) each
- Overall unification: O(n²) or worse

### Complexity Summary (Current)

| Operation | Current | Target |
|-----------|---------|--------|
| Equality | O(n) | O(1) |
| Copy | O(n) | O(1)* |
| Hash for context | O(n) | O(1) |
| Substitution | O(n) | O(log n)** |
| Unification | O(n²) | O(n) |

\* With structural sharing, "copy" becomes reference copy
\** With path copying in persistent structures

---

## Chosen Approach: Merkle-DAG Hash Consing

After evaluating options, we adopt **Merkle-DAG Hash Consing** — a hybrid combining:
1. **Merkle-style content hashing:** Node identity = hash(constructor, child_hashes)
2. **Hash consing interning:** Deduplicate via lookup table
3. **64-bit fast hashing:** rapidhash for speed, near-zero collision risk

This is the same principle used in Git, IPFS, and theorem provers like ACL2.

### Why "Merkle-DAG"?

From [IPFS documentation](https://docs.ipfs.tech/concepts/merkle-dag/):
> A Merkle DAG is a DAG where each node has an identifier that is the result of hashing the node's contents — any payload carried by the node and the list of identifiers of its children.

Key properties:
- **Self-verified:** The hash univocally identifies the entire subtree
- **Immutable:** Any change alters the hash, creating a different DAG
- **Bottom-up construction:** Children must exist before parents (natural for ASTs)
- **Structural sharing:** Identical subtrees have identical hashes → shared

### Why This Fits CALC Perfectly

**Display calculi have the subformula property:** Every formula in a proof appears as a subformula of the goal. This means:
1. We build formulas bottom-up (atoms first, then compounds)
2. Subformulas are reused across the proof
3. Natural fit for Merkle-style hashing

**Proof search explores a DAG, not a tree:**
- Many proof branches share subgoals
- Memoization requires fast equality
- Content addressing enables proof caching

---

## Hash Function Selection

### Requirements
- **64-bit output:** Collision probability < 1 in 4 billion (birthday paradox)
- **Fast on small inputs:** Formulas are small (< 100 bytes typically)
- **Deterministic:** Same input → same hash (unlike cryptographic salts)
- **Quality:** Pass SMHasher tests

### Candidates Evaluated

| Hash | Speed | Quality | JS Support | Notes |
|------|-------|---------|------------|-------|
| **rapidhash** | Fastest | Excellent | [rapidhash-js](https://github.com/komiya-atsushi/rapidhash-js) | Official wyhash successor |
| xxHash3 | Very fast | Excellent | [xxhash-wasm](https://github.com/jungomi/xxhash-wasm) | Widely used |
| wyhash | Very fast | Excellent | Manual port | Default in Zig, Go, Nim |
| FNV-1a | Fast | Good | Native | Simple, good for small inputs |
| MurmurHash3 | Fast | Good | Multiple | Older, well-tested |

### Recommendation: rapidhash

From [SMHasher benchmarks](https://github.com/rurban/smhasher):
> The fastest hash functions without quality problems are: **rapidhash** (an improved wyhash), xxh3low, wyhash.

From [rapidhash repository](https://github.com/Nicoshev/rapidhash):
> Rapidhash is the fastest recommended hash function by SMHasher and SMHasher3. Collision probability lower than wyhash and close to ideal.

**JavaScript implementation:** [rapidhash-js](https://github.com/komiya-atsushi/rapidhash-js)
- Returns 64-bit BigInt
- Supports seed values
- Multiple variants (micro, nano, protected)

### Implementation

```javascript
import { rapidhash } from 'rapidhash-js';

// For leaf nodes: hash the string representation
function leafHash(ruleId, stringVals) {
  return rapidhash(`${ruleId}:${stringVals.join(',')}`);
}

// For internal nodes: combine child hashes
function nodeHash(ruleId, childHashes) {
  // Convert to bytes: ruleId (4 bytes) + each childHash (8 bytes)
  const buffer = new ArrayBuffer(4 + childHashes.length * 8);
  const view = new DataView(buffer);
  view.setUint32(0, ruleId, true);
  childHashes.forEach((h, i) => view.setBigUint64(4 + i * 8, h, true));
  return rapidhash(new Uint8Array(buffer));
}
```

### Collision Analysis

64-bit hash space: 2^64 ≈ 1.8 × 10^19 unique values

| Formulas | Collision Probability |
|----------|----------------------|
| 1,000 | ~0.00000003% |
| 1,000,000 | ~0.003% |
| 1,000,000,000 | ~2.7% |

For proof search with thousands to millions of formulas: **effectively collision-free**.

If paranoid: store full structure, verify on hash collision (like Git does).

---

## Merkle-DAG Hash Consing Implementation

### Core Data Structure

```javascript
class MerkleInterner {
  constructor() {
    this.store = new Map();  // hash (bigint) → NodeData
  }

  // Intern a parsed Node tree, returns content hash
  intern(node) {
    // Leaf node: strings/numbers only
    if (node.vals.every(v => typeof v !== 'object')) {
      const hash = this.leafHash(node.id, node.vals);
      if (!this.store.has(hash)) {
        this.store.set(hash, {
          ruleId: node.id,
          children: node.vals,  // Original string values
          isLeaf: true
        });
      }
      return hash;
    }

    // Internal node: intern children first (bottom-up)
    const childHashes = node.vals.map(v =>
      typeof v === 'object' ? this.intern(v) : this.internString(v)
    );

    const hash = this.nodeHash(node.id, childHashes);
    if (!this.store.has(hash)) {
      this.store.set(hash, {
        ruleId: node.id,
        children: childHashes,  // Hashes of children
        isLeaf: false
      });
    }
    return hash;
  }

  // O(1) equality
  equal(hashA, hashB) {
    return hashA === hashB;
  }

  // Reconstruct Node from hash (for rendering)
  toNode(hash) {
    const data = this.store.get(hash);
    if (data.isLeaf) {
      return new Node(data.ruleId, data.children);
    }
    return new Node(data.ruleId,
      data.children.map(h => typeof h === 'bigint' ? this.toNode(h) : h)
    );
  }
}
```

### Handling Strings and Numbers

Strings and numbers (variable names, term values) are also interned:

```javascript
class MerkleInterner {
  constructor() {
    this.store = new Map();
    this.stringStore = new Map();  // string → hash
  }

  internString(str) {
    if (this.stringStore.has(str)) {
      return this.stringStore.get(str);
    }
    const hash = rapidhash(str);
    this.stringStore.set(str, hash);
    this.store.set(hash, { type: 'string', value: str });
    return hash;
  }

  internNumber(num) {
    const str = `#${num}`;  // Prefix to distinguish from strings
    return this.internString(str);
  }
}
```

### Example Trace

```
Input: parse("(A * B) -o C")

Step 1: intern(Atom_A)
  leafHash("Atom", ["A"]) → 0x1a2b3c4d5e6f7a8bn
  store[0x1a2b...] = { ruleId: "Atom", children: ["A"], isLeaf: true }

Step 2: intern(Atom_B)
  leafHash("Atom", ["B"]) → 0x2b3c4d5e6f7a8b9cn
  store[0x2b3c...] = { ruleId: "Atom", children: ["B"], isLeaf: true }

Step 3: intern(A * B)
  childHashes = [0x1a2b..., 0x2b3c...]
  nodeHash("Formula_Tensor", childHashes) → 0x3c4d5e6f7a8b9c0dn
  store[0x3c4d...] = { ruleId: "Formula_Tensor", children: [0x1a2b..., 0x2b3c...], isLeaf: false }

Step 4: intern(Atom_C)
  leafHash("Atom", ["C"]) → 0x4d5e6f7a8b9c0d1en
  store[0x4d5e...] = { ruleId: "Atom", children: ["C"], isLeaf: true }

Step 5: intern((A * B) -o C)
  childHashes = [0x3c4d..., 0x4d5e...]
  nodeHash("Formula_Loli", childHashes) → 0x5e6f7a8b9c0d1e2fn
  store[0x5e6f...] = { ruleId: "Formula_Loli", children: [0x3c4d..., 0x4d5e...], isLeaf: false }

Result: 0x5e6f7a8b9c0d1e2fn (8 bytes, regardless of formula complexity)

Store size: 5 entries (~150 bytes total)
```

### Structural Sharing in Action

```
Formula 1: (A * B) -o C    → hash: 0x5e6f...
Formula 2: (A * B) -o D    → hash: 0x6f7a... (different)

But both share:
  - Atom_A: 0x1a2b...
  - Atom_B: 0x2b3c...
  - (A * B): 0x3c4d...  ← SHARED!

Only 1 copy of (A * B) in memory.
```

---

## Memory Management Strategies

### The Problem

Hash consing stores create a growing table of interned nodes. During proof search:
- Many nodes created during failed branches
- Backtracking abandons these nodes
- Without cleanup, memory grows unbounded

### Strategy 1: Generational Interning (Appel's Approach)

From [Hash-Consing Garbage Collection](https://www.semanticscholar.org/paper/Hash-consing-Garbage-Collection-Appel-alves/ce7cfa0613bb52bcc35b8ad4c4af65482c33c18f):
> Only records that survive a garbage collection are "hash-consed," thus avoiding the cost of a table lookup for short-lived records.

**Idea:** Don't intern immediately. Let V8's young generation GC clean up short-lived nodes. Only intern nodes that survive to old generation.

**Implementation:**
```javascript
class GenerationalInterner {
  constructor() {
    this.youngGen = new Map();   // Temporary, not deduplicated
    this.oldGen = new Map();     // Permanent, deduplicated
    this.promotionThreshold = 2; // Survive 2 accesses → promote
  }

  intern(node) {
    const hash = this.computeHash(node);

    // Check old generation first
    if (this.oldGen.has(hash)) {
      return hash;
    }

    // Check young generation
    if (this.youngGen.has(hash)) {
      const entry = this.youngGen.get(hash);
      entry.accessCount++;
      if (entry.accessCount >= this.promotionThreshold) {
        // Promote to old generation
        this.oldGen.set(hash, entry.data);
        this.youngGen.delete(hash);
      }
      return hash;
    }

    // New entry in young generation
    this.youngGen.set(hash, { data: nodeData, accessCount: 1 });
    return hash;
  }

  // Call periodically to clean young generation
  minorGC() {
    this.youngGen.clear();  // Discard all young nodes
  }
}
```

**Pros:**
- Short-lived nodes never enter permanent store
- Matches proof search pattern (failed branches → discard)
- Low overhead

**Cons:**
- May re-intern same formula if not promoted
- Tuning required for promotion threshold

### Strategy 2: Arena-Scoped Interning

**Idea:** Each proof branch gets its own "arena". On backtrack, discard the arena.

```javascript
class ArenaInterner {
  constructor(parent = null) {
    this.parent = parent;
    this.local = new Map();
  }

  intern(node) {
    const hash = this.computeHash(node);

    // Check parent chain first
    let current = this;
    while (current) {
      if (current.local.has(hash)) return hash;
      current = current.parent;
    }

    // Add to local arena
    this.local.set(hash, nodeData);
    return hash;
  }

  // Create child arena for new branch
  fork() {
    return new ArenaInterner(this);
  }

  // Merge successful branch into parent
  commit() {
    if (this.parent) {
      for (const [hash, data] of this.local) {
        this.parent.local.set(hash, data);
      }
    }
  }

  // Discard failed branch (just drop reference)
  discard() {
    // GC will clean up this.local
  }
}
```

**Usage in proof search:**
```javascript
function prove(goal, interner) {
  const arena = interner.fork();

  for (const action of getActions(goal)) {
    const result = action(arena);
    if (result.success) {
      arena.commit();  // Keep successful nodes
      return result;
    }
    // Failed: arena.discard() implicit (just don't commit)
  }

  return null;
}
```

**Pros:**
- Perfect match for backtracking
- O(1) bulk discard
- Maps to Zig ArenaAllocator

**Cons:**
- Some duplication across arenas
- Parent lookup adds overhead

### Strategy 3: Weak References (JS-Specific)

From [Hash consing - Wikipedia](https://en.wikipedia.org/wiki/Hash_consing):
> Hash consing is most commonly implemented with hash tables storing weak references that may be garbage-collected when the data stored therein contains no references from outside the table.

```javascript
class WeakInterner {
  constructor() {
    this.table = new Map();  // hash → WeakRef<NodeData>
    this.registry = new FinalizationRegistry(hash => {
      this.table.delete(hash);
    });
  }

  intern(node) {
    const hash = this.computeHash(node);

    const ref = this.table.get(hash);
    if (ref) {
      const data = ref.deref();
      if (data) return { hash, data };
    }

    const data = { ruleId: node.id, children: ... };
    this.table.set(hash, new WeakRef(data));
    this.registry.register(data, hash);
    return { hash, data };
  }
}
```

**Pros:**
- Automatic GC of unused nodes
- No manual memory management

**Cons:**
- WeakRef behavior non-deterministic
- **Not portable to Zig**
- Performance overhead

### Recommendation: Arena for Proof Search, Persistent for Results

```
Proof Search:
  ┌─────────────────────────────────────────┐
  │  Root Interner (persistent, shared)     │
  │  - Contains base formulas from goal     │
  │  - Never garbage collected              │
  └─────────────────────────────────────────┘
              │
              ├── Branch A arena
              │   └── (discarded on fail)
              │
              ├── Branch B arena
              │   └── (committed on success)
              │
              └── Branch C arena
                  └── (discarded on fail)

Result:
  - Root + Branch B nodes → final proof
  - Branch A, C nodes → garbage collected
```

**Implementation:**
```javascript
function proveWithArenas(goal) {
  const root = new MerkleInterner();
  const goalHash = root.intern(parse(goal));

  return search(goalHash, root);
}

function search(goal, interner) {
  const arena = interner.fork();

  for (const action of getActions(goal, arena)) {
    const result = tryAction(action, arena);
    if (result.success) {
      arena.commit();
      return result;
    }
    // arena discarded implicitly
  }

  return null;
}
```

---

## Opaque Primitive Storage (Lazy Expansion)

### The Problem: Deep Trees for Large Numbers

A 256-bit word (common in EVM) represented structurally:

```
0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

In bin representation:
i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(
i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(i(
...256 levels...
e))))...))))
```

**Problems with deep structural representation:**

| Issue | Impact |
|-------|--------|
| **256 nodes per number** | Memory explosion |
| **256 hash computations** | Slow interning |
| **256 hops for traversal** | Slow pattern matching |
| **256 entries in DAG store** | Storage overhead |
| **O(256) for equality** | Even with Merkle-DAG, must traverse to hash |

For EVM simulation with thousands of 256-bit words, this is **catastrophic**.

### Solution: Opaque Leaf Nodes

Store primitive values as **opaque leaves** with their raw binary representation:

```javascript
// Instead of 256-level tree:
{
  type: 'structural',
  id: 'bin_i',
  children: [{ id: 'bin_i', children: [{ id: 'bin_i', ... }] }]
}

// Store as single opaque leaf:
{
  type: 'opaque',
  dataType: 'bin',
  value: 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffn,
  hash: rapidhash('bin:' + value.toString(16))
}
```

**Benefits:**

| Aspect | Structural (256-bit) | Opaque |
|--------|----------------------|--------|
| Nodes | 256 | 1 |
| Hashes | 256 | 1 |
| Memory | ~6KB | ~40 bytes |
| Intern time | O(256) | O(1) |
| Equality | O(1) after interning | O(1) |

### Lazy Expansion

Only expand to structural form when **pattern matching requires it**:

```javascript
class OpaqueNode {
  constructor(dataType, value) {
    this.dataType = dataType;  // 'bin', 'nat', 'string', etc.
    this.value = value;        // JS BigInt, string, etc.
    this._hash = null;         // Computed lazily
    this._expanded = null;     // Structural form, computed lazily
  }

  get hash() {
    if (this._hash === null) {
      // Single hash of type + raw value
      this._hash = rapidhash(`${this.dataType}:${this.value.toString()}`);
    }
    return this._hash;
  }

  // Expand to structural form (only when needed)
  expand(interner) {
    if (this._expanded === null) {
      this._expanded = this.buildStructural(interner);
    }
    return this._expanded;
  }

  buildStructural(interner) {
    if (this.dataType === 'bin') {
      return this.binToStructural(this.value, interner);
    }
    // ... other types
  }

  binToStructural(n, interner) {
    if (n === 0n) {
      return interner.intern('bin_e', []);
    }
    const bit = n % 2n;
    const rest = n / 2n;
    const restHash = this.binToStructural(rest, interner);
    const constructor = bit === 1n ? 'bin_i' : 'bin_o';
    return interner.intern(constructor, [restHash]);
  }
}
```

### When Expansion is Needed

| Operation | Needs Expansion? | Reason |
|-----------|------------------|--------|
| FFI call with ground args | **NO** | FFI uses raw values |
| Hash comparison | **NO** | Compare opaque hashes |
| Store in context | **NO** | Just store hash |
| Pattern match `i(X)` | **YES** | Must decompose structure |
| Unification with structural | **YES** | Must compare structures |
| Export/display | **MAYBE** | Depends on format |

### Smart Pattern Matching

For common patterns, we can match **without full expansion**:

```javascript
class OpaqueNode {
  // Match pattern without full expansion
  matchPattern(pattern, interner) {
    // Variable pattern: bind directly
    if (pattern.isVariable) {
      return { success: true, bindings: { [pattern.name]: this } };
    }

    // Exact structural match needed
    if (pattern.isStructural) {
      // Expand and delegate
      return this.expand(interner).matchPattern(pattern);
    }

    // Optimized: match head constructor without full expansion
    if (this.dataType === 'bin' && pattern.constructor === 'bin_i') {
      // i(X) matches if LSB is 1
      if (this.value % 2n === 1n) {
        const rest = new OpaqueNode('bin', this.value / 2n);
        return {
          success: true,
          bindings: { [pattern.child.name]: rest }
        };
      }
      return { success: false };
    }

    if (this.dataType === 'bin' && pattern.constructor === 'bin_o') {
      // o(X) matches if LSB is 0 and value > 0
      if (this.value > 0n && this.value % 2n === 0n) {
        const rest = new OpaqueNode('bin', this.value / 2n);
        return {
          success: true,
          bindings: { [pattern.child.name]: rest }
        };
      }
      return { success: false };
    }

    if (this.dataType === 'bin' && pattern.constructor === 'bin_e') {
      // e matches only 0
      return { success: this.value === 0n, bindings: {} };
    }

    // Unknown pattern: fall back to full expansion
    return this.expand(interner).matchPattern(pattern);
  }
}
```

### Hash Consistency Design Decision

**Critical question:** Should `hash(opaque(5))` equal `hash(i(o(i(e))))`?

#### Option A: Hash Equivalence (Same hash for same logical value)

```
opaque(5).hash === structural_hash(i(o(i(e))))
```

**Problem:** To compute the opaque hash, we'd need to compute the structural hash anyway — defeating the purpose!

**Only works if:** We define a canonical numeric hash independent of structure.

#### Option B: Separate Representations (Different hashes)

```
opaque(5).hash = rapidhash("bin:5")           // Fast
i(o(i(e))).hash = merkle_hash(i, merkle_hash(o, ...))  // Slow

opaque(5).hash ≠ structural(5).hash  // Different!
```

**Implication:** Opaque and structural are different representations. We need explicit boundaries where conversion happens.

#### Option C: Canonical Numeric Hash (Recommended)

Define the hash of a `bin` value as a function of the **numeric value**, not the structure:

```javascript
function binHash(value) {
  // Hash the number directly, not the structure
  const buffer = new ArrayBuffer(8 + 32);  // type tag + 256-bit value
  const view = new DataView(buffer);
  view.setUint32(0, TYPE_BIN, true);
  // Store value as big-endian bytes
  let v = value;
  for (let i = 31; i >= 0; i--) {
    view.setUint8(8 + i, Number(v & 0xffn));
    v >>= 8n;
  }
  return rapidhash(new Uint8Array(buffer));
}
```

**Now:**
```
opaque(5).hash === binHash(5) === hash_of_structural(i(o(i(e))))
```

**The structural hash is defined to equal the numeric hash:**
```javascript
function structuralBinHash(node, interner) {
  // Convert structure to number, then hash the number
  const value = structureToValue(node);
  return binHash(value);
}
```

**Benefit:** Hash equality works correctly, but we only compute the expensive structural traversal when we **need** the structure, not for hashing.

### Implementation: Hybrid Interner

```javascript
class HybridInterner {
  constructor() {
    this.opaqueStore = new Map();      // hash → OpaqueNode
    this.structuralStore = new Map();  // hash → StructuralNode
    this.expansionCache = new Map();   // opaqueHash → structuralHash
  }

  // Intern an opaque value (O(1))
  internOpaque(dataType, value) {
    const hash = this.computeCanonicalHash(dataType, value);
    if (!this.opaqueStore.has(hash)) {
      this.opaqueStore.set(hash, new OpaqueNode(dataType, value));
    }
    return hash;
  }

  // Intern a structural node (O(k) where k = arity)
  internStructural(ruleId, childHashes) {
    const hash = this.computeStructuralHash(ruleId, childHashes);
    if (!this.structuralStore.has(hash)) {
      this.structuralStore.set(hash, { ruleId, children: childHashes });
    }
    return hash;
  }

  // Get structural form, expanding opaque if needed
  getStructural(hash) {
    if (this.structuralStore.has(hash)) {
      return this.structuralStore.get(hash);
    }
    if (this.opaqueStore.has(hash)) {
      // Expand opaque to structural
      const opaque = this.opaqueStore.get(hash);
      const structuralHash = opaque.expand(this);
      this.expansionCache.set(hash, structuralHash);
      return this.structuralStore.get(structuralHash);
    }
    throw new Error(`Unknown hash: ${hash}`);
  }

  // Canonical hash for primitive types
  computeCanonicalHash(dataType, value) {
    switch (dataType) {
      case 'bin':
        return this.binCanonicalHash(value);
      case 'nat':
        return this.natCanonicalHash(value);
      case 'string':
        return rapidhash(`string:${value}`);
      default:
        throw new Error(`Unknown data type: ${dataType}`);
    }
  }

  binCanonicalHash(value) {
    // Fixed-size hash regardless of value magnitude
    const buffer = new ArrayBuffer(36);  // 4 byte type + 32 byte value
    const view = new DataView(buffer);
    view.setUint32(0, 0x42494E00, true);  // "BIN\0"
    let v = value;
    for (let i = 31; i >= 0; i--) {
      view.setUint8(4 + i, Number(v & 0xffn));
      v >>= 8n;
    }
    return rapidhash(new Uint8Array(buffer));
  }
}
```

### Integration with FFI

FFI naturally works with opaque values:

```javascript
// In FFI handler
const ffi = {
  plus: {
    handlers: {
      '+ + -': {
        canApply: (a, b, c) => isOpaque(a) && isOpaque(b),
        compute: (a, b, c) => {
          // Work directly with opaque values — no expansion needed!
          const aVal = a.value;  // BigInt
          const bVal = b.value;  // BigInt
          const result = aVal + bVal;

          // Return new opaque node
          return {
            success: true,
            bindings: { 2: new OpaqueNode('bin', result) }
          };
        }
      }
    }
  }
};
```

**The FFI never expands!** It works entirely with opaque values.

### Integration with Pattern Matching

Only expand when proof search needs structural decomposition:

```javascript
// In proof search
function matchPremise(premise, ctx, interner) {
  // Find formula in context that matches premise pattern
  for (const [hash, entry] of ctx) {
    const node = interner.get(hash);

    // Try opaque smart-match first
    if (node.type === 'opaque') {
      const result = node.matchPattern(premise, interner);
      if (result.success) return result;
    } else {
      // Structural node: normal unification
      const theta = mgu(premise, node);
      if (theta) return { success: true, bindings: theta };
    }
  }
  return { success: false };
}
```

### When to Use Opaque vs Structural

| Source | Representation | Reason |
|--------|---------------|--------|
| Parsed literal `42` | **Opaque** | User input, likely used in FFI |
| Parsed literal `0xff` | **Opaque** | Hex literals are always large |
| FFI output | **Opaque** | FFI produces raw values |
| Pattern match result | **Opaque** | Smart match keeps opaque |
| Axiom clause `plus/z1: plus e e e` | **Structural** | Needs pattern matching |
| Rule conclusion | **Structural** | Part of calculus definition |

### Garbage Collection Considerations

Opaque nodes are much cheaper to GC:

```javascript
// Arena for proof search
class Arena {
  constructor(parent) {
    this.parent = parent;
    this.opaqueNodes = [];    // Just BigInts, cheap
    this.structuralNodes = []; // More complex, but fewer
  }

  discard() {
    // Opaque nodes: just drop references
    this.opaqueNodes = null;
    // Structural nodes: same
    this.structuralNodes = null;
    // GC handles the rest
  }
}
```

### String Storage

Same principle applies to strings:

```javascript
// Instead of:
cons('h', cons('e', cons('l', cons('l', cons('o', nil)))))  // 6 nodes

// Store as:
{
  type: 'opaque',
  dataType: 'string',
  value: "hello",
  hash: rapidhash("string:hello")
}
```

Expand to cons-list only if pattern matching against list structure.

### Complexity Summary

| Operation | Structural (256-bit) | Opaque |
|-----------|----------------------|--------|
| Create | O(256) | O(1) |
| Hash | O(256) | O(1) |
| Equality | O(1)* | O(1) |
| FFI use | O(256) convert | O(1) |
| Store | O(256) nodes | O(1) node |
| Pattern `i(X)` | O(1) | O(1) smart-match |
| Full expansion | — | O(256) when needed |

\* After interning, but interning itself is O(256)

### Implementation Recommendations

1. **Default to opaque** for all literals and FFI outputs
2. **Structural only** for axiom patterns and rule conclusions
3. **Smart matching** to avoid expansion when possible
4. **Canonical hashing** so opaque and structural hash to same value
5. **Lazy expansion** with caching
6. **Arena-scoped** opaque nodes for efficient GC

**See also:** `typed-dsl-logical-framework.md` § "End-to-End Example: Opaque Values in DSL, FFI, and DAG" for a complete trace of `plus 42 8 X` through parsing, DAG interning, FFI execution, and pattern matching.

### Zig Considerations

Opaque nodes map well to Zig:

```zig
const OpaqueNode = struct {
    data_type: DataType,
    value: Value,
    hash: u64,

    const Value = union(enum) {
        bin: u256,           // Zig has arbitrary-width integers!
        nat: u64,
        string: []const u8,
    };

    const DataType = enum { bin, nat, string };

    pub fn computeHash(self: *const OpaqueNode) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(&[_]u8{@intFromEnum(self.data_type)});
        switch (self.value) {
            .bin => |v| hasher.update(std.mem.asBytes(&v)),
            .nat => |v| hasher.update(std.mem.asBytes(&v)),
            .string => |s| hasher.update(s),
        }
        return hasher.final();
    }
};
```

Zig's `u256` type makes 256-bit words first-class!

---

## Low-Level Memory Model

This section defines the precise memory layout, addressing the questions:
1. Why NOT store hash inside the node?
2. How is type information stored?
3. What's the storage model for variable-size data?
4. How is data added, accessed, removed?
5. What's the computational complexity?

---

### Design Principle: Separate Index from Data

**Key insight from [Git's pack files](https://git-scm.com/book/en/v2/Git-Internals-Packfiles):** Separate the lookup structure (index) from the data storage. The index maps hash → location, the data store holds the actual content.

**Key insight from [BDD implementations](https://en.wikipedia.org/wiki/Hash_consing):** Storing hash inside the node causes "indirection inefficiency" — every access requires a hash table lookup. Instead, use integer indices for internal references.

---

### Why NOT Store Hash Inside the Node

**Wrong design:**
```javascript
const dagNode = {
  hash: 0xabcd...,        // REDUNDANT!
  nodeType: 'opaque',
  value: 50n,
};
store.set(hash, dagNode);  // hash stored twice!
```

**Problems:**
1. **Memory waste:** Hash stored in both key AND value
2. **Inconsistency risk:** What if `node.hash ≠ key`?
3. **No benefit:** If you have the node, you got it via the key (which IS the hash)

**Correct design:**
```javascript
// Index: hash → location
// Data: just the payload, no hash

store.set(hash, {
  nodeType: 'opaque',
  value: 50n,
  // NO hash field!
});
```

**When you need the hash:** You already have it — it's how you looked up the node.

---

### Two-Level Architecture: Index + Data Pools

```
┌─────────────────────────────────────────────────────────────────────┐
│                         INDEX (Hash Table)                          │
│                                                                     │
│    hash (u64) ──────────────────────────► NodeRef                   │
│    0xa1b2c3d4... ───────────────────────► { pool: BIN, idx: 42 }    │
│    0xe5f6a7b8... ───────────────────────► { pool: STRUCT, idx: 17 } │
│    0xc9d0e1f2... ───────────────────────► { pool: VAR, idx: 3 }     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        DATA POOLS (Type-Specific)                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  BIN_POOL (fixed 32 bytes each):                                    │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │ [0]:  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00          │ │
│  │       00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 2a  (= 42)  │ │
│  ├────────────────────────────────────────────────────────────────┤ │
│  │ [1]:  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00          │ │
│  │       00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 08  (= 8)   │ │
│  ├────────────────────────────────────────────────────────────────┤ │
│  │ [2]:  ... (= 50)                                               │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  STRUCT_POOL (variable size, packed):                               │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │ [0]: { constructor_id: 7, arity: 2,                            │ │
│  │        children: [0xa1b2..., 0xe5f6...] }                      │ │
│  ├────────────────────────────────────────────────────────────────┤ │
│  │ [1]: { constructor_id: 3, arity: 1,                            │ │
│  │        children: [0xc9d0...] }                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  VAR_POOL (variable names, interned strings):                       │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │ [0]: "X"                                                       │ │
│  │ [1]: "Y"                                                       │ │
│  │ [2]: "Result"                                                  │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

### NodeRef: The Indirection Structure

```javascript
// JavaScript
const NodeRef = {
  pool: 'bin' | 'nat' | 'string' | 'struct' | 'var',
  idx: number  // Index into the appropriate pool
};
```

```zig
// Zig: Pack into 8 bytes
const NodeRef = packed struct {
    pool: Pool,      // 3 bits (8 pool types max)
    idx: u29,        // 29 bits (500M entries max)
};

const Pool = enum(u3) {
    bin = 0,         // 256-bit opaque numbers
    nat = 1,         // 64-bit opaque naturals
    string = 2,      // Variable-length strings
    structural = 3,  // Compound nodes
    variable = 4,    // Logic variables
    // room for 3 more types
};
```

**Size:** 4 bytes per reference (or 8 bytes with padding for alignment).

---

### Type-Specific Pool Layouts

#### Pool 0: BIN (256-bit numbers)

```
┌─────────────────────────────────────────────────────────────────┐
│  BIN_POOL: Array of [32]u8, fixed size                          │
├─────────────────────────────────────────────────────────────────┤
│  Memory layout: contiguous array, no headers                    │
│                                                                 │
│  offset = idx * 32                                              │
│  data   = pool[offset .. offset + 32]                           │
│                                                                 │
│  Example: idx=42 → bytes at offset 1344 (42 * 32)               │
│                                                                 │
│  idx  offset   value (big-endian 256-bit)                       │
│  ───  ──────   ─────────────────────────────                    │
│   0      0     0x000...00000000000000000000000000000000002a     │
│   1     32     0x000...000000000000000000000000000000000008     │
│   2     64     0x000...000000000000000000000000000000000032     │
│  ...                                                            │
└─────────────────────────────────────────────────────────────────┘

Access: O(1) — direct array indexing
Memory: 32 bytes per entry, zero overhead
```

#### Pool 1: NAT (64-bit naturals)

```
┌─────────────────────────────────────────────────────────────────┐
│  NAT_POOL: Array of u64, fixed size                             │
├─────────────────────────────────────────────────────────────────┤
│  offset = idx * 8                                               │
│  data   = pool[offset .. offset + 8]                            │
│                                                                 │
│  idx   value                                                    │
│  ───   ─────                                                    │
│   0    42                                                       │
│   1    1000000                                                  │
│  ...                                                            │
└─────────────────────────────────────────────────────────────────┘

Access: O(1)
Memory: 8 bytes per entry
```

#### Pool 2: STRING (variable-length)

```
┌─────────────────────────────────────────────────────────────────┐
│  STRING_POOL: Length-prefixed strings in contiguous buffer      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  string_offsets: [u32]  — offset into string_data               │
│  string_data: [u8]      — raw string bytes                      │
│                                                                 │
│  idx  offset  length  data                                      │
│  ───  ──────  ──────  ────                                      │
│   0      0       5    "hello"                                   │
│   1      5       3    "foo"                                     │
│   2      8      11    "transaction"                             │
│                                                                 │
│  string_offsets = [0, 5, 8, ...]                                │
│  string_data    = "hellofootransaction..."                      │
│                                                                 │
│  Access: offset = string_offsets[idx]                           │
│          length = string_offsets[idx+1] - offset (or sentinel)  │
│          data   = string_data[offset .. offset + length]        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

Access: O(1) — two array lookups
Memory: 4 bytes overhead per string (offset entry)
```

#### Pool 3: STRUCTURAL (compound nodes)

```
┌─────────────────────────────────────────────────────────────────┐
│  STRUCT_POOL: Variable-size entries with header                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Entry layout:                                                  │
│  ┌──────────────────┬────────────────────────────────────────┐  │
│  │  Header (4 bytes)│  Children (arity × 8 bytes)            │  │
│  │  ┌────────┬─────┐│                                        │  │
│  │  │ctor_id │arity││  [child_hash_0, child_hash_1, ...]     │  │
│  │  │ (u16)  │(u16)││  (each child is u64 hash)              │  │
│  │  └────────┴─────┘│                                        │  │
│  └──────────────────┴────────────────────────────────────────┘  │
│                                                                 │
│  struct_offsets: [u32]  — offset into struct_data               │
│  struct_data: [u8]      — packed entries                        │
│                                                                 │
│  Example entry for "tensor(A, B)":                              │
│    ctor_id = 7 (tensor)                                         │
│    arity   = 2                                                  │
│    children = [hash_of_A, hash_of_B]                            │
│    total size = 4 + 2*8 = 20 bytes                              │
│                                                                 │
│  Access:                                                        │
│    offset = struct_offsets[idx]                                 │
│    header = struct_data[offset .. offset + 4]                   │
│    ctor_id = header[0..2] as u16                                │
│    arity   = header[2..4] as u16                                │
│    children = struct_data[offset+4 .. offset+4+arity*8]         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

Access: O(1) + O(arity) to read children
Memory: 4 bytes header + 8 bytes per child
```

#### Pool 4: VARIABLE (logic variables)

```
┌─────────────────────────────────────────────────────────────────┐
│  VAR_POOL: Similar to STRING_POOL                               │
├─────────────────────────────────────────────────────────────────┤
│  Stores variable names: "X", "Y", "Result", etc.                │
│  Same layout as STRING_POOL.                                    │
└─────────────────────────────────────────────────────────────────┘
```

---

### Complete Memory Layout

```
┌─────────────────────────────────────────────────────────────────────┐
│                           STORE                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  INDEX: std.AutoHashMap(u64, NodeRef)                               │
│  ├─ capacity: u32                                                   │
│  ├─ entries: [](struct { key: u64, value: NodeRef, ... })           │
│  └─ (standard open-addressing hash table)                           │
│                                                                     │
│  POOLS:                                                             │
│  ├─ bin_pool:      ArrayList([32]u8)    — fixed 32 bytes each       │
│  ├─ nat_pool:      ArrayList(u64)       — fixed 8 bytes each        │
│  ├─ string_offsets: ArrayList(u32)      — offsets into string_data  │
│  ├─ string_data:   ArrayList(u8)        — raw string bytes          │
│  ├─ struct_offsets: ArrayList(u32)      — offsets into struct_data  │
│  ├─ struct_data:   ArrayList(u8)        — packed struct entries     │
│  ├─ var_offsets:   ArrayList(u32)       — offsets into var_data     │
│  └─ var_data:      ArrayList(u8)        — variable name bytes       │
│                                                                     │
│  ALLOCATOR:                                                         │
│  └─ arena: ArenaAllocator                                           │
│     └─ (for bulk deallocation on proof branch discard)              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

### Operations and Complexity

#### INSERT (intern)

```
intern(node) → hash:
  1. Compute canonical hash              O(1) opaque, O(arity) structural
  2. Check index for existing            O(1) hash table lookup
  3. If exists, return existing hash     O(1)
  4. Append to appropriate pool          O(1) amortized (ArrayList)
  5. Insert into index                   O(1) amortized
  6. Return hash                         O(1)

Total: O(1) for opaque, O(arity) for structural
```

```javascript
// JavaScript implementation
function intern(node) {
  // 1. Compute hash
  const hash = computeCanonicalHash(node);

  // 2. Check existence
  if (index.has(hash)) {
    return hash;  // Already interned
  }

  // 3. Append to pool
  let ref;
  switch (node.type) {
    case 'bin':
      const idx = bin_pool.length;
      bin_pool.push(node.value);  // BigInt → 32 bytes
      ref = { pool: 'bin', idx };
      break;

    case 'struct':
      const offset = struct_data.length;
      // Write header
      struct_data.push(...encodeU16(node.constructorId));
      struct_data.push(...encodeU16(node.children.length));
      // Write children hashes
      for (const childHash of node.children) {
        struct_data.push(...encodeU64(childHash));
      }
      struct_offsets.push(offset);
      ref = { pool: 'struct', idx: struct_offsets.length - 1 };
      break;

    // ... other types
  }

  // 4. Insert into index
  index.set(hash, ref);

  return hash;
}
```

#### LOOKUP (get)

```
get(hash) → NodeData:
  1. Look up hash in index               O(1)
  2. Get NodeRef { pool, idx }           O(1)
  3. Access pool[idx]                    O(1) fixed-size, O(1) variable (with offset table)
  4. Decode data                         O(1) fixed-size, O(size) variable

Total: O(1) for fixed-size, O(size) for variable-size data
```

```javascript
// JavaScript implementation
function get(hash) {
  const ref = index.get(hash);
  if (!ref) return null;

  switch (ref.pool) {
    case 'bin':
      return {
        type: 'bin',
        value: bin_pool[ref.idx]  // Already a BigInt
      };

    case 'struct':
      const offset = struct_offsets[ref.idx];
      const constructorId = decodeU16(struct_data, offset);
      const arity = decodeU16(struct_data, offset + 2);
      const children = [];
      for (let i = 0; i < arity; i++) {
        children.push(decodeU64(struct_data, offset + 4 + i * 8));
      }
      return {
        type: 'struct',
        constructorId,
        children  // Array of hashes, NOT NodeData
      };

    // ... other types
  }
}
```

#### EQUALITY

```
equal(hashA, hashB) → bool:
  return hashA === hashB;               O(1)
```

That's it. Hash comparison is O(1) integer/bigint comparison.

#### REMOVE (individual)

**Not supported in arena-scoped design.** This is intentional:

- During proof search, we create many speculative nodes
- Most get discarded when branches fail
- Individual removal would require:
  - Tombstones (waste space, need compaction)
  - Reference counting (complex, not Zig-idiomatic)
  - GC (overhead, non-deterministic)

**Instead:** Use arena-scoped allocation.

#### BULK REMOVE (discard arena)

```
discardArena(arena):
  arena.deinit();                       O(1)
```

All memory allocated from the arena is freed in one operation.
This is how Zig [ArenaAllocator](https://zig.guide/standard-library/allocators/) works — you can't free individual allocations, but `deinit()` frees everything at once.

---

### Arena-Scoped Allocation for Proof Search

```
Proof search structure:

  ROOT_ARENA (never freed):
  ├─ Goal sequent
  ├─ Known formulas
  └─ Base calculus rules

  BRANCH_ARENA_1 (discarded on failure):
  ├─ Speculative substitutions
  ├─ Intermediate formulas
  └─ (freed when branch fails)

  BRANCH_ARENA_2 (committed on success):
  ├─ Successful substitutions
  ├─ Proof steps
  └─ (merged into root on success)
```

```javascript
// JavaScript implementation
class ScopedStore {
  constructor(parent = null) {
    this.parent = parent;

    // Local pools (arena-scoped)
    this.index = new Map();
    this.bin_pool = [];
    this.struct_offsets = [];
    this.struct_data = [];
    // ... other pools
  }

  intern(node) {
    const hash = computeCanonicalHash(node);

    // Check local first
    if (this.index.has(hash)) return hash;

    // Check parent chain
    let current = this.parent;
    while (current) {
      if (current.index.has(hash)) return hash;
      current = current.parent;
    }

    // Not found, add to local
    // ... (same as before)
    return hash;
  }

  get(hash) {
    // Check local first
    if (this.index.has(hash)) {
      return this.getLocal(hash);
    }

    // Check parent chain
    let current = this.parent;
    while (current) {
      if (current.index.has(hash)) {
        return current.getLocal(hash);
      }
      current = current.parent;
    }

    return null;
  }

  // Create child arena for speculative branch
  fork() {
    return new ScopedStore(this);
  }

  // Merge successful branch into parent
  commit() {
    if (!this.parent) return;

    // Merge local into parent
    for (const [hash, ref] of this.index) {
      // Copy data from local pool to parent pool
      // Update ref to point to parent pool
      this.parent.index.set(hash, this.copyToParent(ref));
    }
  }

  // Discard failed branch (just drop reference)
  discard() {
    // In JS: GC handles it
    // In Zig: arena.deinit()
  }
}
```

---

### Zig Implementation

```zig
const std = @import("std");

pub const Pool = enum(u3) {
    bin = 0,
    nat = 1,
    string = 2,
    structural = 3,
    variable = 4,
};

pub const NodeRef = packed struct {
    pool: Pool,
    idx: u29,
};

pub const Store = struct {
    allocator: std.mem.Allocator,

    // Index: hash → NodeRef
    index: std.AutoHashMap(u64, NodeRef),

    // Type-specific pools
    bin_pool: std.ArrayList([32]u8),
    nat_pool: std.ArrayList(u64),

    // Variable-length pools
    string_offsets: std.ArrayList(u32),
    string_data: std.ArrayList(u8),
    struct_offsets: std.ArrayList(u32),
    struct_data: std.ArrayList(u8),
    var_offsets: std.ArrayList(u32),
    var_data: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{
            .allocator = allocator,
            .index = std.AutoHashMap(u64, NodeRef).init(allocator),
            .bin_pool = std.ArrayList([32]u8).init(allocator),
            .nat_pool = std.ArrayList(u64).init(allocator),
            .string_offsets = std.ArrayList(u32).init(allocator),
            .string_data = std.ArrayList(u8).init(allocator),
            .struct_offsets = std.ArrayList(u32).init(allocator),
            .struct_data = std.ArrayList(u8).init(allocator),
            .var_offsets = std.ArrayList(u32).init(allocator),
            .var_data = std.ArrayList(u8).init(allocator),
        };
    }

    pub fn deinit(self: *Store) void {
        self.index.deinit();
        self.bin_pool.deinit();
        self.nat_pool.deinit();
        self.string_offsets.deinit();
        self.string_data.deinit();
        self.struct_offsets.deinit();
        self.struct_data.deinit();
        self.var_offsets.deinit();
        self.var_data.deinit();
    }

    pub fn internBin(self: *Store, value: u256) !u64 {
        // Compute canonical hash
        const hash = binCanonicalHash(value);

        // Check existence
        if (self.index.contains(hash)) {
            return hash;
        }

        // Append to pool
        var bytes: [32]u8 = undefined;
        std.mem.writeInt(u256, &bytes, value, .big);
        try self.bin_pool.append(bytes);

        // Insert into index
        try self.index.put(hash, .{
            .pool = .bin,
            .idx = @intCast(self.bin_pool.items.len - 1),
        });

        return hash;
    }

    pub fn internStructural(
        self: *Store,
        constructor_id: u16,
        children: []const u64,
    ) !u64 {
        // Compute hash
        const hash = structuralHash(constructor_id, children);

        if (self.index.contains(hash)) {
            return hash;
        }

        // Record offset
        const offset: u32 = @intCast(self.struct_data.items.len);
        try self.struct_offsets.append(offset);

        // Write header
        try self.struct_data.appendSlice(std.mem.asBytes(&constructor_id));
        const arity: u16 = @intCast(children.len);
        try self.struct_data.appendSlice(std.mem.asBytes(&arity));

        // Write children
        for (children) |child_hash| {
            try self.struct_data.appendSlice(std.mem.asBytes(&child_hash));
        }

        // Insert into index
        try self.index.put(hash, .{
            .pool = .structural,
            .idx = @intCast(self.struct_offsets.items.len - 1),
        });

        return hash;
    }

    pub fn getBin(self: *const Store, hash: u64) ?u256 {
        const ref = self.index.get(hash) orelse return null;
        if (ref.pool != .bin) return null;
        const bytes = self.bin_pool.items[ref.idx];
        return std.mem.readInt(u256, &bytes, .big);
    }

    pub fn getStructural(self: *const Store, hash: u64) ?StructuralView {
        const ref = self.index.get(hash) orelse return null;
        if (ref.pool != .structural) return null;

        const offset = self.struct_offsets.items[ref.idx];
        const data = self.struct_data.items[offset..];

        const constructor_id = std.mem.readInt(u16, data[0..2], .little);
        const arity = std.mem.readInt(u16, data[2..4], .little);

        return .{
            .constructor_id = constructor_id,
            .children_data = data[4 .. 4 + arity * 8],
        };
    }

    fn binCanonicalHash(value: u256) u64 {
        var bytes: [36]u8 = undefined;
        std.mem.writeInt(u32, bytes[0..4], 0x42494E00, .little); // "BIN\0"
        std.mem.writeInt(u256, bytes[4..36], value, .big);
        return std.hash.Wyhash.hash(0, &bytes);
    }

    fn structuralHash(constructor_id: u16, children: []const u64) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&constructor_id));
        hasher.update(std.mem.sliceAsBytes(children));
        return hasher.final();
    }
};

pub const StructuralView = struct {
    constructor_id: u16,
    children_data: []const u8,

    pub fn getChild(self: StructuralView, i: usize) u64 {
        const offset = i * 8;
        return std.mem.readInt(u64, self.children_data[offset..][0..8], .little);
    }

    pub fn arity(self: StructuralView) usize {
        return self.children_data.len / 8;
    }
};

// Arena-scoped store for proof branches
pub const ScopedStore = struct {
    parent: ?*const Store,
    local: Store,

    pub fn init(allocator: std.mem.Allocator, parent: ?*const Store) ScopedStore {
        return .{
            .parent = parent,
            .local = Store.init(allocator),
        };
    }

    pub fn deinit(self: *ScopedStore) void {
        self.local.deinit();
    }

    pub fn getBin(self: *const ScopedStore, hash: u64) ?u256 {
        // Check local first
        if (self.local.getBin(hash)) |v| return v;
        // Check parent
        if (self.parent) |p| return p.getBin(hash);
        return null;
    }

    // commit() would copy local entries to parent
    // discard() is just deinit()
};
```

---

### Complexity Summary

| Operation | Time | Space |
|-----------|------|-------|
| `intern(opaque_bin)` | O(1) | 32 bytes + index entry |
| `intern(opaque_nat)` | O(1) | 8 bytes + index entry |
| `intern(structural)` | O(arity) | 4 + 8*arity bytes + index entry |
| `get(hash)` | O(1) | — |
| `equal(h1, h2)` | O(1) | — |
| `fork()` | O(1) | New arena |
| `commit()` | O(n) | Merge n entries |
| `discard()` | O(1) | Free arena |

---

### Memory Overhead Analysis

For a 256-bit number (e.g., EVM word):

| Storage | Bytes |
|---------|-------|
| Value | 32 |
| Index entry (hash + NodeRef) | 8 + 4 = 12 |
| **Total** | **44 bytes** |

Compare to structural `i(o(i(...)))` with 256 levels:
- 256 nodes × (4 bytes constructor + 8 bytes child hash + 12 bytes index) = **6,144 bytes**

**Savings: 139× smaller**

---

## High-Performance JavaScript Implementation

This section provides an efficient JS implementation using TypedArrays where possible, addressing V8 optimization considerations.

### Why TypedArrays?

From [MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Typed_arrays) and [V8 performance research](https://v8.dev/blog/hash-code):

1. **Contiguous memory** — TypedArrays allocate memory in bulk, optimal for CPU caches
2. **Type consistency** — Fixed types mean lower CPU overhead
3. **No object overhead** — Raw memory, no hidden classes or property lookups
4. **64-bit support** — `BigUint64Array` provides native 64-bit integers

### Why Map over Object?

From [V8 Map internals](https://itnext.io/v8-deep-dives-understanding-map-internals-45eb94a183df):

- `Map` is **~4-5× faster** for frequent insertions
- `Map` uses a proper hash table (deterministic hash tables algorithm)
- `Object` falls into slow "dictionary mode" with dynamic keys
- `Map.delete()` is optimized; `delete obj.key` is notoriously slow

### The `n` Suffix: BigInt Syntax

```javascript
const a = 42;     // Number (64-bit float, ~53-bit integer precision)
const b = 42n;    // BigInt (arbitrary precision)

42 + 42n;         // TypeError! Can't mix
42n + 42n;        // 84n ✓
```

For **64-bit hashes**, we use `BigInt` because:
- JavaScript `Number` only has ~53 bits of integer precision
- `BigUint64Array` elements are `BigInt` values
- Hash comparison must be exact (no floating point errors)

---

### Complete TypedArray-Based Implementation

```javascript
// lib/store.js — High-performance store using TypedArrays

/**
 * Pool types enum (matches Zig)
 */
const Pool = {
  BIN: 0,        // 256-bit opaque (4 × u64 = 32 bytes)
  NAT: 1,        // 64-bit opaque (1 × u64 = 8 bytes)
  HASH: 2,       // 64-bit hash values (for structural children)
  STRING: 3,     // Variable-length UTF-8
  STRUCT: 4,     // Variable-length structural nodes
  VAR: 5,        // Variable names
};

/**
 * High-performance store using TypedArrays for fixed-size data
 */
class Store {
  constructor(initialCapacity = 1024) {
    // Index: hash (BigInt) → NodeRef
    // Map is faster than Object for dynamic keys (V8 optimized)
    this.index = new Map();

    // === FIXED-SIZE POOLS (TypedArrays) ===

    // BIN pool: 256-bit numbers stored as 4 × 64-bit chunks
    // Each entry is 4 consecutive u64 values
    this._binCapacity = initialCapacity;
    this._binLength = 0;
    this._binData = new BigUint64Array(initialCapacity * 4);

    // NAT pool: 64-bit numbers
    this._natCapacity = initialCapacity;
    this._natLength = 0;
    this._natData = new BigUint64Array(initialCapacity);

    // HASH pool: for storing child hash arrays (structural nodes)
    this._hashCapacity = initialCapacity * 4;
    this._hashLength = 0;
    this._hashData = new BigUint64Array(initialCapacity * 4);

    // === VARIABLE-SIZE POOLS ===

    // STRING pool: offset table + data buffer
    this._stringOffsets = new Uint32Array(initialCapacity);
    this._stringOffsetsLength = 0;
    this._stringData = new Uint8Array(initialCapacity * 16);  // ~16 bytes avg
    this._stringDataLength = 0;

    // STRUCT pool: constructorId (u16) + arity (u16) + hashOffset (u32)
    // Each entry: 8 bytes header pointing to _hashData
    this._structCapacity = initialCapacity;
    this._structLength = 0;
    this._structHeaders = new Uint32Array(initialCapacity * 2);  // [ctorId<<16|arity, hashOffset]

    // VAR pool: same as STRING
    this._varOffsets = new Uint32Array(initialCapacity);
    this._varOffsetsLength = 0;
    this._varData = new Uint8Array(initialCapacity * 8);  // ~8 bytes avg
    this._varDataLength = 0;
  }

  // === HASH FUNCTIONS ===

  /**
   * FNV-1a hash (64-bit) — fast, good distribution
   * For production, use wyhash via WebAssembly
   */
  _hash64(data) {
    let hash = 0xcbf29ce484222325n;  // FNV offset basis
    const prime = 0x100000001b3n;     // FNV prime

    if (typeof data === 'bigint') {
      // Hash BigInt by its bytes
      for (let i = 0; i < 8; i++) {
        hash ^= (data >> BigInt(i * 8)) & 0xffn;
        hash = (hash * prime) & 0xffffffffffffffffn;
      }
    } else if (data instanceof Uint8Array) {
      for (let i = 0; i < data.length; i++) {
        hash ^= BigInt(data[i]);
        hash = (hash * prime) & 0xffffffffffffffffn;
      }
    } else if (typeof data === 'string') {
      for (let i = 0; i < data.length; i++) {
        hash ^= BigInt(data.charCodeAt(i));
        hash = (hash * prime) & 0xffffffffffffffffn;
      }
    }
    return hash;
  }

  /**
   * Canonical hash for 256-bit bin value
   */
  _binHash(value) {
    // value is BigInt (up to 256 bits)
    // Hash: type tag + 4 × 64-bit chunks
    let hash = 0xcbf29ce484222325n;
    const prime = 0x100000001b3n;

    // Type tag
    hash ^= BigInt(Pool.BIN);
    hash = (hash * prime) & 0xffffffffffffffffn;

    // 4 chunks (little-endian)
    for (let i = 0; i < 4; i++) {
      const chunk = (value >> BigInt(i * 64)) & 0xffffffffffffffffn;
      for (let j = 0; j < 8; j++) {
        hash ^= (chunk >> BigInt(j * 8)) & 0xffn;
        hash = (hash * prime) & 0xffffffffffffffffn;
      }
    }
    return hash;
  }

  /**
   * Canonical hash for structural node
   */
  _structHash(constructorId, childHashes) {
    let hash = 0xcbf29ce484222325n;
    const prime = 0x100000001b3n;

    // Type tag
    hash ^= BigInt(Pool.STRUCT);
    hash = (hash * prime) & 0xffffffffffffffffn;

    // Constructor ID
    hash ^= BigInt(constructorId);
    hash = (hash * prime) & 0xffffffffffffffffn;

    // Children hashes
    for (const childHash of childHashes) {
      for (let j = 0; j < 8; j++) {
        hash ^= (childHash >> BigInt(j * 8)) & 0xffn;
        hash = (hash * prime) & 0xffffffffffffffffn;
      }
    }
    return hash;
  }

  // === POOL GROWTH ===

  _growBinPool() {
    const newCapacity = this._binCapacity * 2;
    const newData = new BigUint64Array(newCapacity * 4);
    newData.set(this._binData);
    this._binData = newData;
    this._binCapacity = newCapacity;
  }

  _growNatPool() {
    const newCapacity = this._natCapacity * 2;
    const newData = new BigUint64Array(newCapacity);
    newData.set(this._natData);
    this._natData = newData;
    this._natCapacity = newCapacity;
  }

  _growHashPool() {
    const newCapacity = this._hashCapacity * 2;
    const newData = new BigUint64Array(newCapacity);
    newData.set(this._hashData);
    this._hashData = newData;
    this._hashCapacity = newCapacity;
  }

  _growStringData() {
    const newCapacity = this._stringData.length * 2;
    const newData = new Uint8Array(newCapacity);
    newData.set(this._stringData);
    this._stringData = newData;
  }

  _growStringOffsets() {
    const newCapacity = this._stringOffsets.length * 2;
    const newData = new Uint32Array(newCapacity);
    newData.set(this._stringOffsets);
    this._stringOffsets = newData;
  }

  // === INTERN FUNCTIONS ===

  /**
   * Intern a 256-bit number (e.g., EVM word)
   * @param {BigInt} value — up to 256 bits
   * @returns {BigInt} — 64-bit hash
   */
  internBin(value) {
    const hash = this._binHash(value);

    if (this.index.has(hash)) {
      return hash;
    }

    // Grow if needed
    if (this._binLength >= this._binCapacity) {
      this._growBinPool();
    }

    // Store as 4 × 64-bit chunks
    const idx = this._binLength;
    const offset = idx * 4;
    this._binData[offset + 0] = value & 0xffffffffffffffffn;
    this._binData[offset + 1] = (value >> 64n) & 0xffffffffffffffffn;
    this._binData[offset + 2] = (value >> 128n) & 0xffffffffffffffffn;
    this._binData[offset + 3] = (value >> 192n) & 0xffffffffffffffffn;
    this._binLength++;

    // Index entry: pool type + index
    this.index.set(hash, { pool: Pool.BIN, idx });

    return hash;
  }

  /**
   * Intern a 64-bit natural number
   * @param {BigInt} value — up to 64 bits
   * @returns {BigInt} — 64-bit hash
   */
  internNat(value) {
    // For nat, hash is just type tag + value (simple and fast)
    let hash = 0xcbf29ce484222325n;
    const prime = 0x100000001b3n;
    hash ^= BigInt(Pool.NAT);
    hash = (hash * prime) & 0xffffffffffffffffn;
    for (let j = 0; j < 8; j++) {
      hash ^= (value >> BigInt(j * 8)) & 0xffn;
      hash = (hash * prime) & 0xffffffffffffffffn;
    }

    if (this.index.has(hash)) {
      return hash;
    }

    if (this._natLength >= this._natCapacity) {
      this._growNatPool();
    }

    const idx = this._natLength;
    this._natData[idx] = value;
    this._natLength++;

    this.index.set(hash, { pool: Pool.NAT, idx });

    return hash;
  }

  /**
   * Intern a string
   * @param {string} value
   * @returns {BigInt} — 64-bit hash
   */
  internString(value) {
    const hash = this._hash64('s:' + value);

    if (this.index.has(hash)) {
      return hash;
    }

    // Encode to UTF-8
    const encoder = new TextEncoder();
    const bytes = encoder.encode(value);

    // Grow if needed
    while (this._stringDataLength + bytes.length > this._stringData.length) {
      this._growStringData();
    }
    if (this._stringOffsetsLength >= this._stringOffsets.length) {
      this._growStringOffsets();
    }

    // Store offset
    const idx = this._stringOffsetsLength;
    this._stringOffsets[idx] = this._stringDataLength;
    this._stringOffsetsLength++;

    // Store data
    this._stringData.set(bytes, this._stringDataLength);
    this._stringDataLength += bytes.length;

    this.index.set(hash, { pool: Pool.STRING, idx });

    return hash;
  }

  /**
   * Intern a structural node
   * @param {number} constructorId
   * @param {BigInt[]} childHashes — array of 64-bit hashes
   * @returns {BigInt} — 64-bit hash
   */
  internStructural(constructorId, childHashes) {
    const hash = this._structHash(constructorId, childHashes);

    if (this.index.has(hash)) {
      return hash;
    }

    // Store children in hash pool
    while (this._hashLength + childHashes.length > this._hashCapacity) {
      this._growHashPool();
    }

    const hashOffset = this._hashLength;
    for (let i = 0; i < childHashes.length; i++) {
      this._hashData[this._hashLength + i] = childHashes[i];
    }
    this._hashLength += childHashes.length;

    // Store header: [constructorId << 16 | arity, hashOffset]
    if (this._structLength >= this._structCapacity) {
      // Grow struct headers
      const newCapacity = this._structCapacity * 2;
      const newHeaders = new Uint32Array(newCapacity * 2);
      newHeaders.set(this._structHeaders);
      this._structHeaders = newHeaders;
      this._structCapacity = newCapacity;
    }

    const idx = this._structLength;
    this._structHeaders[idx * 2] = (constructorId << 16) | childHashes.length;
    this._structHeaders[idx * 2 + 1] = hashOffset;
    this._structLength++;

    this.index.set(hash, { pool: Pool.STRUCT, idx });

    return hash;
  }

  /**
   * Intern a logic variable
   * @param {string} name
   * @returns {BigInt} — 64-bit hash
   */
  internVar(name) {
    const hash = this._hash64('v:' + name);

    if (this.index.has(hash)) {
      return hash;
    }

    // Same as string, but separate pool
    const encoder = new TextEncoder();
    const bytes = encoder.encode(name);

    while (this._varDataLength + bytes.length > this._varData.length) {
      const newData = new Uint8Array(this._varData.length * 2);
      newData.set(this._varData);
      this._varData = newData;
    }
    if (this._varOffsetsLength >= this._varOffsets.length) {
      const newOffsets = new Uint32Array(this._varOffsets.length * 2);
      newOffsets.set(this._varOffsets);
      this._varOffsets = newOffsets;
    }

    const idx = this._varOffsetsLength;
    this._varOffsets[idx] = this._varDataLength;
    this._varOffsetsLength++;

    this._varData.set(bytes, this._varDataLength);
    this._varDataLength += bytes.length;

    this.index.set(hash, { pool: Pool.VAR, idx });

    return hash;
  }

  // === GET FUNCTIONS ===

  /**
   * Get pool type for a hash
   * @param {BigInt} hash
   * @returns {number|null} — Pool enum value or null
   */
  getPool(hash) {
    const ref = this.index.get(hash);
    return ref ? ref.pool : null;
  }

  /**
   * Get a 256-bit bin value
   * @param {BigInt} hash
   * @returns {BigInt|null}
   */
  getBin(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.BIN) return null;

    const offset = ref.idx * 4;
    return (
      this._binData[offset + 0] |
      (this._binData[offset + 1] << 64n) |
      (this._binData[offset + 2] << 128n) |
      (this._binData[offset + 3] << 192n)
    );
  }

  /**
   * Get a 64-bit nat value
   * @param {BigInt} hash
   * @returns {BigInt|null}
   */
  getNat(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.NAT) return null;
    return this._natData[ref.idx];
  }

  /**
   * Get a string value
   * @param {BigInt} hash
   * @returns {string|null}
   */
  getString(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.STRING) return null;

    const start = this._stringOffsets[ref.idx];
    const end = ref.idx + 1 < this._stringOffsetsLength
      ? this._stringOffsets[ref.idx + 1]
      : this._stringDataLength;

    const decoder = new TextDecoder();
    return decoder.decode(this._stringData.subarray(start, end));
  }

  /**
   * Get a structural node
   * @param {BigInt} hash
   * @returns {{ constructorId: number, children: BigInt[] }|null}
   */
  getStructural(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.STRUCT) return null;

    const header = this._structHeaders[ref.idx * 2];
    const hashOffset = this._structHeaders[ref.idx * 2 + 1];

    const constructorId = header >>> 16;
    const arity = header & 0xffff;

    const children = [];
    for (let i = 0; i < arity; i++) {
      children.push(this._hashData[hashOffset + i]);
    }

    return { constructorId, children };
  }

  /**
   * Get a variable name
   * @param {BigInt} hash
   * @returns {string|null}
   */
  getVar(hash) {
    const ref = this.index.get(hash);
    if (!ref || ref.pool !== Pool.VAR) return null;

    const start = this._varOffsets[ref.idx];
    const end = ref.idx + 1 < this._varOffsetsLength
      ? this._varOffsets[ref.idx + 1]
      : this._varDataLength;

    const decoder = new TextDecoder();
    return decoder.decode(this._varData.subarray(start, end));
  }

  /**
   * Generic get — returns typed result
   * @param {BigInt} hash
   * @returns {{ type: string, value: any }|null}
   */
  get(hash) {
    const ref = this.index.get(hash);
    if (!ref) return null;

    switch (ref.pool) {
      case Pool.BIN:
        return { type: 'bin', value: this.getBin(hash) };
      case Pool.NAT:
        return { type: 'nat', value: this.getNat(hash) };
      case Pool.STRING:
        return { type: 'string', value: this.getString(hash) };
      case Pool.STRUCT:
        return { type: 'struct', ...this.getStructural(hash) };
      case Pool.VAR:
        return { type: 'var', name: this.getVar(hash) };
      default:
        return null;
    }
  }

  // === EQUALITY ===

  /**
   * O(1) equality check
   */
  equal(hashA, hashB) {
    return hashA === hashB;
  }

  // === STATS ===

  stats() {
    return {
      entries: this.index.size,
      binPool: { length: this._binLength, capacity: this._binCapacity },
      natPool: { length: this._natLength, capacity: this._natCapacity },
      stringPool: { length: this._stringOffsetsLength, dataBytes: this._stringDataLength },
      structPool: { length: this._structLength, hashesUsed: this._hashLength },
      varPool: { length: this._varOffsetsLength, dataBytes: this._varDataLength },
    };
  }
}

// === SCOPED STORE (for proof search branches) ===

class ScopedStore {
  constructor(parent = null) {
    this.parent = parent;
    this.local = new Store(256);  // Smaller initial size for branches
  }

  // Intern checks parent first, stores in local
  internBin(value) {
    const hash = this.local._binHash(value);
    if (this._hasInChain(hash)) return hash;
    return this.local.internBin(value);
  }

  internNat(value) {
    let hash = 0xcbf29ce484222325n;
    const prime = 0x100000001b3n;
    hash ^= BigInt(Pool.NAT);
    hash = (hash * prime) & 0xffffffffffffffffn;
    for (let j = 0; j < 8; j++) {
      hash ^= (value >> BigInt(j * 8)) & 0xffn;
      hash = (hash * prime) & 0xffffffffffffffffn;
    }
    if (this._hasInChain(hash)) return hash;
    return this.local.internNat(value);
  }

  internString(value) {
    const hash = this.local._hash64('s:' + value);
    if (this._hasInChain(hash)) return hash;
    return this.local.internString(value);
  }

  internStructural(constructorId, childHashes) {
    const hash = this.local._structHash(constructorId, childHashes);
    if (this._hasInChain(hash)) return hash;
    return this.local.internStructural(constructorId, childHashes);
  }

  internVar(name) {
    const hash = this.local._hash64('v:' + name);
    if (this._hasInChain(hash)) return hash;
    return this.local.internVar(name);
  }

  // Check if hash exists in this store or any parent
  _hasInChain(hash) {
    let current = this;
    while (current) {
      if (current.local.index.has(hash)) return true;
      current = current.parent;
    }
    return false;
  }

  // Get from local or parent chain
  get(hash) {
    let current = this;
    while (current) {
      const result = current.local.get(hash);
      if (result) return result;
      current = current.parent;
    }
    return null;
  }

  getBin(hash) {
    let current = this;
    while (current) {
      const result = current.local.getBin(hash);
      if (result !== null) return result;
      current = current.parent;
    }
    return null;
  }

  // ... similar for other getters

  // Create child scope for speculative branch
  fork() {
    return new ScopedStore(this);
  }

  // Discard this scope (just drop reference, GC handles it)
  discard() {
    // In JS, just let GC collect it
    // The local Store's TypedArrays will be garbage collected
  }

  // Commit local entries to parent (for successful branch)
  commit() {
    if (!this.parent) return;

    // Copy all local entries to parent
    for (const [hash, ref] of this.local.index) {
      if (!this.parent.local.index.has(hash)) {
        // Re-intern in parent (copies data)
        const data = this.local.get(hash);
        switch (data.type) {
          case 'bin':
            this.parent.local.internBin(data.value);
            break;
          case 'nat':
            this.parent.local.internNat(data.value);
            break;
          case 'string':
            this.parent.local.internString(data.value);
            break;
          case 'struct':
            this.parent.local.internStructural(data.constructorId, data.children);
            break;
          case 'var':
            this.parent.local.internVar(data.name);
            break;
        }
      }
    }
  }
}

module.exports = { Store, ScopedStore, Pool };
```

---

### Performance Characteristics

| Operation | Time | Memory |
|-----------|------|--------|
| `internBin(value)` | O(1) | 32 bytes in TypedArray |
| `internNat(value)` | O(1) | 8 bytes in TypedArray |
| `internString(s)` | O(len) | len bytes + 4 byte offset |
| `internStructural(id, children)` | O(arity) | 8 bytes header + 8×arity bytes |
| `getBin(hash)` | O(1) | — |
| `getStructural(hash)` | O(arity) | Creates children array |
| `equal(h1, h2)` | O(1) | — |
| `fork()` | O(1) | New Store instance |
| `commit()` | O(n) | Copies n local entries |
| `discard()` | O(1) | GC handles cleanup |

### Memory Layout Comparison

| Approach | 256-bit number | String "hello" | Struct(2 children) |
|----------|----------------|----------------|---------------------|
| **TypedArray pools** | 32 bytes | 5 + 4 = 9 bytes | 8 + 16 = 24 bytes |
| **Plain JS objects** | ~80 bytes (BigInt + obj overhead) | ~48 bytes | ~96 bytes |
| **Savings** | **2.5×** | **5×** | **4×** |

### Why This Is Fast

1. **[BigUint64Array](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigUint64Array)** — Native 64-bit integers, contiguous memory
2. **[Map for index](https://itnext.io/v8-deep-dives-understanding-map-internals-45eb94a183df)** — V8-optimized hash table, ~4× faster than Object for dynamic keys
3. **No object allocation** in hot paths — Data goes directly into TypedArrays
4. **Pool-per-type** — No type tags in data, no branching in tight loops
5. **Offset tables** for variable-size — O(1) access, no linked lists

---

## Integration with Proof Search

### Sequent Context Keys

**Before:** `sha3(formula.toString())` — O(n)
**After:** Formula's content hash — O(1) lookup

```javascript
// Before
let id = sha3(ast.toString());
seq.linear_ctx[id] = { num, val: ast };

// After
let hash = interner.intern(ast);
seq.linear_ctx[hash] = { num, hash };  // Store hash, not node
```

### Unification Equality

**Before:** `t0.toString() === t1.toString()` — O(n)
**After:** `hashA === hashB` — O(1)

```javascript
// Before
let isEq = t0.toString() === t1.toString();

// After
let isEq = interner.intern(t0) === interner.intern(t1);
```

### Memoization

Content hashes enable proof memoization:

```javascript
class ProofMemo {
  constructor() {
    this.cache = new Map();  // sequentHash → proofResult
  }

  memoize(sequent, proveFunc) {
    const hash = this.hashSequent(sequent);
    if (this.cache.has(hash)) {
      return this.cache.get(hash);
    }
    const result = proveFunc(sequent);
    this.cache.set(hash, result);
    return result;
  }

  hashSequent(seq) {
    // Hash combines: persistent_ctx hashes + linear_ctx hashes + succedent hash
    return rapidhash([
      ...Object.keys(seq.persistent_ctx).sort(),
      ...Object.keys(seq.linear_ctx).sort(),
      seq.succedent
    ].join(':'));
  }
}
```

---

## Advanced Optimizations Enabled by Merkle-DAG

### Eliminating Sequent.copy()

**What it does** (lib/sequent.js:209-229):
```javascript
Sequent.copy = function (seq) {
  // Deep copy every formula in linear_ctx
  linear_ctx[id] = {num: r.num, val: r.val.copy()};  // O(n) per formula!
  // Deep copy every formula in persistent_ctx
  persistent_ctx[id] = seq.persistent_ctx[id].copy()  // O(n) per formula!
  // Deep copy succedent
  let succedent = seq.succedent.copy();  // O(n)
}
```

**Current complexity:** O(m·n) where m = formulas in context, n = average formula size.

**Where it's used:**

| Location | Purpose | Needed with Merkle-DAG? |
|----------|---------|-------------------------|
| `proofstate.js:327` | `debug.result = Sequent.copy(...)` | **NO** — debug only |
| `proofstate.js:507` | `Proofstate.focus()` — create focused sequent | **NO** — use hash refs |
| `sequent.js:146` | `renameUniqueArray()` — before substitution | **NO** — immutable |
| `sequent.js:166` | `renameUnique()` — before substitution | **NO** — immutable |

**Why copy exists:** Current implementation mutates sequents. Substitution modifies nodes in-place, so we copy first to preserve the original.

**Why Merkle-DAG eliminates it:** With content-addressed immutable data:
- Substitution returns a **new hash**, doesn't mutate
- "Copying" a sequent means copying hash references (8 bytes each)
- Original data is never modified

```javascript
// Current: mutates, so we copy first
let seq_ = Sequent.copy(seq);        // O(m·n)
seq_.substitute(theta);              // Mutates seq_

// Merkle-DAG: immutable, no copy needed
let newSeqHash = substituteSequent(seqHash, theta);  // Returns new hash, O(m·k)
// Original seqHash unchanged, still valid
```

**New complexity:** O(0) — operation eliminated entirely.

---

### Near-Linear Unification Algorithms

The current mgu() implementation uses naive Robinson unification with O(k²·n) complexity. Better algorithms exist:

#### Paterson-Wegman (1976): True O(n) Linear

From [Linear Unification](https://www.sciencedirect.com/science/article/pii/0022000078900430):
> A unification algorithm is described which tests a set of expressions for unifiability and which requires time and space which are only linear in the size of the input.

**Key insight:** Use unbounded pointer lists instead of union-find to represent equivalence classes, avoiding the inverse Ackermann factor.

**Trade-off:** Complex implementation, rarely needed for small terms.

#### Martelli-Montanari: Almost Linear O(n·α(n))

From [An Efficient Unification Algorithm](https://dl.acm.org/doi/10.1145/357162.357169):
> Almost linear time where α(n) is the inverse Ackermann function.

The α(n) factor is effectively constant for all practical inputs (α(n) ≤ 4 for n < 10^80).

**Uses union-find** for equivalence class maintenance, which is simpler to implement than Paterson-Wegman.

#### Comparison

| Algorithm | Complexity | Implementation | Best For |
|-----------|------------|----------------|----------|
| Robinson (current) | O(n²) | Simple | Tiny terms |
| Martelli-Montanari | O(n·α(n)) ≈ O(n) | Medium | General use |
| Paterson-Wegman | O(n) | Complex | Very large terms |

#### With Merkle-DAG: Even Better

Hash consing provides additional speedups on top of better algorithms:

1. **Equality is O(1)** — compare hashes, not structures
2. **Occurs check is O(1)** — if hashes match, same term (no traversal)
3. **Substitution shares structure** — only changed paths are new

From [Efficient Symbolic Computation via Hash Consing](https://arxiv.org/html/2509.20534v2):
> Hash-consing can eliminate the extra linear factor of time complexity commonly seen when dealing with sequences.

**Revised mgu() complexity:**

| Implementation | Complexity | Notes |
|----------------|------------|-------|
| Current | O(k²·n) | k iterations, O(k·n) propagation each |
| Merkle-DAG + Robinson | O(k²) | O(1) equality eliminates n factor |
| Merkle-DAG + Martelli-Montanari | O(k·α(k)) ≈ O(k) | Near-linear in variables |

Where k = number of variables (typically 5-10 in practice).

---

### O(1) Identity Rule via Hash Lookup

**Current identity rule** (`tryIdPos` in proofstate.js:433-462):
```javascript
// For EACH formula in context, try to unify with succedent
Object.keys(ctx).find(id => {
  theta = mgu([[ctxFormula, formula]]);  // O(n²) per attempt!
  return !!theta;
});
```

**Current complexity:** O(m·n²) — m context formulas, O(n²) mgu each.

**Key insight:** For ground formulas (no variables), identity is just hash lookup:

```javascript
// Merkle-DAG identity for ground formulas: O(1)
function tryIdPos(pt, succedentHash) {
  // Direct lookup — does this exact hash exist in context?
  if (ctx.has(succedentHash)) {
    return { theta: [], delta_out: ... };  // Instant match!
  }
  return false;
}
```

**For formulas with variables:**

The constructor (outermost connective) must match. Use a secondary index:

```javascript
class ContextIndex {
  constructor() {
    this.byHash = new Map();        // hash → entry (O(1) ground lookup)
    this.byConstructor = new Map(); // ruleId → [entries] (filter by head)
  }

  // For identity with variables:
  findUnifiable(formulaHash) {
    const data = interner.get(formulaHash);

    // Get candidates with same constructor
    const candidates = this.byConstructor.get(data.ruleId) || [];

    // Only unify with candidates (much smaller than full context)
    for (const candidate of candidates) {
      const theta = mgu([[candidate.hash, formulaHash]]);
      if (theta) return { match: candidate, theta };
    }
    return null;
  }
}
```

**Revised complexity:**

| Case | Current | Merkle-DAG |
|------|---------|------------|
| Ground formula (no vars) | O(m·n²) | **O(1)** hash lookup |
| With variables | O(m·n²) | **O(c·k)** where c = candidates with same constructor |

In practice, c << m (few formulas share the same outermost connective).

---

### Revised Speedup Estimates

The n× speedup I initially stated was **conservative**. Here's the full picture:

#### Per-Operation Speedups

| Operation | Current | Merkle-DAG | Merkle-DAG + Optimized | Speedup |
|-----------|---------|------------|------------------------|---------|
| Node.copy() | O(n) | O(1) | O(1) | **n×** |
| Node equality | O(n) | O(1) | O(1) | **n×** |
| Sequent.copy() | O(m·n) | O(m) | **O(0)** eliminated | **∞** |
| mgu() | O(k²·n) | O(k²) | O(k) | **k·n×** |
| Identity (ground) | O(m·n²) | O(m) | **O(1)** | **m·n²×** |
| Identity (with vars) | O(m·n²) | O(m+k²) | O(c·k) | **(m/c)·n²×** |

#### Full Proof Speedup

For a proof with:
- d = depth
- b = branching factor
- m = context size (~10)
- n = formula size (~20)
- k = variables (~5)

**Current:**
```
O(b^d × (m·n + m·n² + k²·n))
= O(b^d × m·n²)  (identity dominates)
= O(b^d × 10 × 400)
= O(b^d × 4000)
```

**Merkle-DAG + All Optimizations:**
```
O(b^d × (0 + 1 + k))  (no copy, O(1) identity, O(k) mgu)
= O(b^d × k)
= O(b^d × 5)
```

**Actual speedup: ~800× for typical proofs** (not just n×).

#### Speedup by Formula Structure

| Proof Type | Current | Optimized | Speedup |
|------------|---------|-----------|---------|
| Small ground (n=5, k=0) | O(b^d × 250) | O(b^d × 1) | **250×** |
| Medium with vars (n=20, k=5) | O(b^d × 4000) | O(b^d × 5) | **800×** |
| Large complex (n=50, k=10) | O(b^d × 25000) | O(b^d × 10) | **2500×** |

The speedup grows with formula size because we eliminate O(n²) operations entirely.

---

### Summary: Optimization Stack

| Layer | Technique | Improvement |
|-------|-----------|-------------|
| 1. Hash equality | Compare 64-bit hashes | O(n) → O(1) |
| 2. Immutability | No defensive copies | O(m·n) → O(0) |
| 3. Structural sharing | Subtrees shared | Memory ÷ sharing factor |
| 4. Near-linear unification | Martelli-Montanari | O(k²) → O(k) |
| 5. Indexed identity | Hash + constructor index | O(m·n²) → O(1) or O(c·k) |
| 6. Arena GC | Bulk discard on backtrack | GC pauses → O(1) |

**Combined effect:** 100-2500× speedup depending on formula complexity.

---

## Background: Content-Addressing Techniques

### 1. Hash Consing (Filliâtre & Conchon, 2006)

**Core idea:** Every structurally unique term gets a unique integer ID. Equality becomes integer comparison.

```
hashcons_table: (constructor, child_ids...) → unique_id
```

**Key properties:**
- **Maximal sharing:** Identical subtrees share memory
- **O(1) equality:** Compare unique IDs (integers)
- **Memoization-friendly:** IDs can index into memo tables
- **Weak references:** Allow GC of unused nodes

**OCaml signature:**
```ocaml
type 'a hash_consed = {
  node : 'a;        (* The actual value *)
  tag  : int;       (* Unique integer ID *)
  hkey : int;       (* Hash key for table *)
}
```

**Reference:** [Type-Safe Modular Hash-Consing](https://dl.acm.org/doi/10.1145/1159876.1159880)

### 2. De Bruijn Indices

**Problem:** Alpha-equivalent terms should be equal.
- `λx. x` and `λy. y` are alpha-equivalent but syntactically different

**Solution:** Replace bound variable names with indices (depth to binder).

```
λx. λy. x   →   λ. λ. 1      (index 1 = skip 1 binder)
λx. λy. y   →   λ. λ. 0      (index 0 = nearest binder)
```

**Operations needed:**
- **Shift:** Increment indices when going under binder
- **Substitution:** Replace index with term, adjust other indices

**Benefit:** Alpha-equivalent terms become syntactically identical → can apply hash consing.

**Reference:** [De Bruijn index - Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index)

### 3. Locally Nameless Representation

**Hybrid approach:**
- Bound variables: de Bruijn indices
- Free variables: names

```
λx. x y   →   λ. 0 y      (0 is bound, y is free name)
```

**Benefits:**
- Alpha-equivalence for bound variables
- Readable names for free variables
- Simpler than pure de Bruijn for many operations

**Operations:**
- **Opening:** Replace outermost bound var with a name
- **Closing:** Replace a name with bound var (index 0)

**Reference:** [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf)

### 4. E-graphs (Equality Graphs)

**Used in:** SMT solvers, equality saturation (egg)

**Structure:**
- E-class: Set of equivalent e-nodes
- E-node: Operator with children that are e-classes (not nodes)
- Union-find: Tracks equivalence classes

**Key insight:** Represent equivalence relation, not individual terms.

```
      +---------+
      | E-class |
      | {a+b,   |
      |  b+a}   |
      +---------+
         / \
    e-class  e-class
      {a}      {b}
```

**Benefits:**
- Efficient congruence closure
- Represent many equivalent terms compactly
- Good for rewriting/optimization

**Reference:** [egg: E-Graphs Good](https://egraphs-good.github.io/)

### 5. BDD Unique Tables

**Binary Decision Diagrams** use:
- **Unique table:** Hash table ensuring canonical nodes
- **Computed table:** Cache for operation results

```javascript
// Pseudo-code for BDD node creation
function makeNode(var, low, high) {
  if (low.id === high.id) return low;  // Reduction rule
  let key = (var, low.id, high.id);
  if (uniqueTable.has(key)) return uniqueTable.get(key);
  let node = new Node(var, low, high, nextId++);
  uniqueTable.set(key, node);
  return node;
}
```

**Benefits:**
- Canonical representation
- O(1) equivalence check
- Efficient boolean operations via memoization

**Reference:** [Binary Decision Diagrams](https://course.khoury.northeastern.edu/csu690/notes/bdd.html)

### 6. Unison Language

**Approach:** SHA3-512 hash of normalized AST.

```
hash(definition) = SHA3-512(normalize(AST))
```

**Normalization:**
- Replace names with positional references
- Replace dependencies with their hashes

**Benefits:**
- Content-addressed code storage
- Rename-proof identity
- Distributed caching

**Tradeoff:** Hash computation is O(n), not suitable for O(1) runtime equality.

**Reference:** [Unison: The Big Idea](https://www.unison-lang.org/docs/the-big-idea/)

### 7. Structural Sharing (Immutable.js, Clojure)

**Technique:** Persistent data structures with path copying.

```
Original trie:        After update (tea: 3 → 14):
    root                    root'
   /    \                  /    \
  t      ...              t'     ...  (shared)
  |                       |
  e                       e'
  |                       |
  a → 3                   a → 14
```

Only nodes on the path to change are copied; rest is shared.

**Benefits:**
- Immutable updates without full copy
- Memory efficient
- Enables undo/versioning

**Reference:** [Immutable.js: Structural Sharing](https://medium.com/@dtinth/immutable-js-persistent-data-structures-and-structural-sharing-6d163fbd73d2)

---

## Design Options for CALC

### Option 1: Integer ID Interning (Recommended)

**Approach:** Every unique (constructor, child_ids) tuple gets a unique integer ID.

```typescript
interface InternedNode {
  id: number;           // Unique identifier
  ruleId: number;       // Constructor/rule type
  children: number[];   // IDs of children (not nodes)
}

class NodeInterner {
  private nextId = 0;
  private table: Map<string, number> = new Map();  // key → id
  private nodes: InternedNode[] = [];              // id → node

  intern(ruleId: number, children: number[]): number {
    const key = `${ruleId}:${children.join(',')}`;
    if (this.table.has(key)) return this.table.get(key)!;
    const id = this.nextId++;
    this.table.set(key, id);
    this.nodes[id] = { id, ruleId, children };
    return id;
  }

  equal(a: number, b: number): boolean {
    return a === b;  // O(1)!
  }
}
```

**Complexity:**
| Operation | Complexity |
|-----------|------------|
| Create node | O(k) where k = arity |
| Equality | O(1) |
| Get children | O(1) |
| Memory | Shared subtrees |

**Pros:**
- O(1) equality (integer comparison)
- Maximal structural sharing
- Simple implementation
- Easy to port to Zig (array indexing)
- Good cache locality

**Cons:**
- Nodes never garbage collected (without weak refs)
- Need to handle binding (quantifiers) separately
- Interning table grows monotonically

**Zig compatibility:** Excellent — just array indices.

### Option 2: Hash Consing with WeakRef

**Approach:** Like Option 1, but use WeakRef for GC of unused nodes.

```typescript
class WeakNodeInterner {
  private table: Map<string, WeakRef<InternedNode>> = new Map();
  private registry = new FinalizationRegistry((key: string) => {
    this.table.delete(key);
  });

  intern(ruleId: number, children: number[]): InternedNode {
    const key = `${ruleId}:${children.join(',')}`;
    const ref = this.table.get(key);
    if (ref) {
      const node = ref.deref();
      if (node) return node;
    }
    const node = { id: this.nextId++, ruleId, children };
    this.table.set(key, new WeakRef(node));
    this.registry.register(node, key);
    return node;
  }
}
```

**Pros:**
- Allows garbage collection of unused nodes
- Same O(1) equality benefits

**Cons:**
- WeakRef behavior is non-deterministic
- More complex implementation
- Not portable to Zig (no WeakRef equivalent)
- Performance overhead from weak references

**Zig compatibility:** Poor — WeakRef is JS-specific.

### Option 3: De Bruijn + Interning (For Binding)

**Approach:** Convert to de Bruijn indices, then intern.

```typescript
// Original: ∀x. P(x) ⊗ Q(x)
// De Bruijn: ∀. P(0) ⊗ Q(0)

function toDeBruijn(node: Node, env: Map<string, number>): DeBruijnNode {
  if (isForall(node)) {
    const varName = node.boundVar;
    const newEnv = new Map(env);
    newEnv.set(varName, 0);
    // Shift all other indices
    for (const [k, v] of newEnv) {
      if (k !== varName) newEnv.set(k, v + 1);
    }
    return { type: 'forall', body: toDeBruijn(node.body, newEnv) };
  }
  if (isFreeVar(node)) {
    const idx = env.get(node.name);
    if (idx !== undefined) {
      return { type: 'bound', index: idx };
    }
    return { type: 'free', name: node.name };
  }
  // ... recursive cases
}
```

**Then intern the de Bruijn form:**
```typescript
const dbNode = toDeBruijn(originalNode, new Map());
const internedId = interner.intern(dbNode);
```

**Pros:**
- Alpha-equivalent terms get same ID
- Combines benefits of de Bruijn and interning

**Cons:**
- Two-pass: convert then intern
- De Bruijn terms harder to read/debug
- Shift operations needed for substitution

**Zig compatibility:** Good — de Bruijn indices are just integers.

### Option 4: Locally Nameless + Interning (Hybrid)

**Approach:** Bound vars as indices, free vars as interned names.

```typescript
type LNTerm =
  | { type: 'bound', index: number }
  | { type: 'free', nameId: number }      // Interned name
  | { type: 'app', ruleId: number, args: number[] }  // Interned term IDs
```

**Pros:**
- Readable free variables
- Alpha-equivalence for bound vars
- Interning benefits

**Cons:**
- Slightly more complex than pure de Bruijn
- Need opening/closing operations

**Zig compatibility:** Good.

### Option 5: E-graph Style (For Proof Search)

**Approach:** Use e-graphs to represent equivalent sequents.

```typescript
interface EClass {
  id: number;
  nodes: Set<ENode>;  // Equivalent representations
}

interface ENode {
  ruleId: number;
  children: number[];  // E-class IDs, not node IDs
}

class EGraph {
  private classes: Map<number, EClass> = new Map();
  private unionFind: UnionFind = new UnionFind();

  merge(a: number, b: number): number {
    // Merge equivalence classes, propagate congruence
    const rootA = this.unionFind.find(a);
    const rootB = this.unionFind.find(b);
    if (rootA === rootB) return rootA;
    // ... merge and rebuild
  }
}
```

**Pros:**
- Track equivalences during proof search
- Congruence closure for free
- Good for bidirectional search

**Cons:**
- More complex than simple interning
- Overkill if we just need equality, not equivalence tracking
- Significant implementation effort

**Zig compatibility:** Moderate — union-find is straightforward.

### Option 6: Content Hash (Unison-style) for Serialization Only

**Approach:** Use interning for runtime, hashes only for serialization/dedup.

```typescript
class HybridAddressing {
  private interner = new NodeInterner();  // For runtime

  // Runtime: use integer IDs
  equal(a: number, b: number): boolean {
    return a === b;
  }

  // Serialization: compute hash lazily
  hash(id: number): string {
    const node = this.interner.get(id);
    const childHashes = node.children.map(c => this.hash(c));
    return sha256(`${node.ruleId}:${childHashes.join(',')}`);
  }
}
```

**Pros:**
- Fast runtime (O(1) equality)
- Content hashes for distributed/persistent storage
- Best of both worlds

**Cons:**
- Two identity systems to maintain
- Hash computation still O(n) when needed

**Zig compatibility:** Excellent.

---

## Complexity Comparison

| Operation | Current | Opt 1 | Opt 2 | Opt 3 | Opt 4 | Opt 5 | Opt 6 |
|-----------|---------|-------|-------|-------|-------|-------|-------|
| Create | O(n) | O(k) | O(k) | O(n) | O(n) | O(k) | O(k) |
| Equality | O(n) | O(1) | O(1) | O(1) | O(1) | O(1) | O(1) |
| Copy | O(n) | O(1) | O(1) | O(1) | O(1) | O(1) | O(1) |
| Hash | O(n) | - | - | - | - | - | O(n)* |
| Substitute | O(n) | O(n)† | O(n)† | O(n) | O(n) | - | O(n)† |
| Memory | O(n) | shared | shared+GC | shared | shared | compact | shared |

k = arity of node
* = computed lazily, cached
† = creates new interned nodes, but shares subtrees

---

## Recommendations

### Primary Recommendation: Merkle-DAG Hash Consing

**64-bit content hashes** (rapidhash) with **arena-scoped interning** for proof search.

**Decision Summary:**
| Aspect | Choice | Rationale |
|--------|--------|-----------|
| Hash function | rapidhash (64-bit) | Fastest, excellent quality, JS+Zig support |
| Identity | Content hash | Deterministic, portable, persistent |
| Memory management | Arena per branch | Matches backtracking, Zig-portable |
| Lookup | Map<bigint, NodeData> | O(1) dedup, O(1) equality |

**Why not integer IDs?**
- Integer IDs require session state (ID counter)
- IDs change on restart
- Content hashes are deterministic and portable
- With 64-bit hashes, collision risk is negligible

**Why not cryptographic hashes (SHA3)?**
- Too slow for proof search hot path
- We don't need cryptographic properties
- rapidhash is 10-100× faster

### Implementation Priority

1. **Phase 1: Core Interner**
   - Implement `MerkleInterner` with rapidhash
   - Support leaf nodes (atoms, variables)
   - Support internal nodes (compounds)
   - Benchmark vs current toString() approach

2. **Phase 2: Integrate with Sequent**
   - Replace `sha3(ast.toString())` with content hash
   - Store hashes in linear_ctx instead of string keys
   - Update mgu.js equality to use hash comparison

3. **Phase 3: Arena-Scoped Interning**
   - Implement fork/commit/discard for proof branches
   - Integrate with Proofstate backtracking
   - Benchmark GC reduction

4. **Phase 4: Proof Memoization**
   - Hash entire sequents
   - Cache proven/disproven sequents
   - Share proofs across similar goals

5. **Phase 5: Alpha-Equivalence (if needed)**
   - De Bruijn conversion before hashing
   - For quantified formulas only

### For Zig Export

```zig
const std = @import("std");

const NodeData = struct {
    rule_id: u32,
    children: []const u64,
    is_leaf: bool,
};

const MerkleInterner = struct {
    store: std.AutoHashMap(u64, NodeData),
    arena: std.heap.ArenaAllocator,

    pub fn init(allocator: std.mem.Allocator) MerkleInterner {
        return .{
            .store = std.AutoHashMap(u64, NodeData).init(allocator),
            .arena = std.heap.ArenaAllocator.init(allocator),
        };
    }

    pub fn intern(self: *MerkleInterner, rule_id: u32, children: []const u64) !u64 {
        const hash = nodeHash(rule_id, children);
        if (self.store.contains(hash)) return hash;

        const alloc = self.arena.allocator();
        const children_copy = try alloc.dupe(u64, children);
        try self.store.put(hash, .{
            .rule_id = rule_id,
            .children = children_copy,
            .is_leaf = children.len == 0,
        });
        return hash;
    }

    fn nodeHash(rule_id: u32, children: []const u64) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&rule_id));
        hasher.update(std.mem.sliceAsBytes(children));
        return hasher.final();
    }
};
```

**Zig advantages:**
- `std.hash.Wyhash` built-in (same family as rapidhash)
- `ArenaAllocator` for bulk deallocation
- Zero-cost hash comparison (u64 == u64)
- No GC overhead

---

## References

### Hash Consing & Merkle Structures
1. Filliâtre & Conchon, [Type-Safe Modular Hash-Consing](https://dl.acm.org/doi/10.1145/1159876.1159880), ML Workshop 2006
2. Appel & Goncalves, [Hash-Consing Garbage Collection](https://www.cs.princeton.edu/research/techreps/TR-412-93), Princeton TR-412-93, 1993
3. [Hash consing - Wikipedia](https://en.wikipedia.org/wiki/Hash_consing)
4. [Merkle DAG - IPFS Documentation](https://docs.ipfs.tech/concepts/merkle-dag/)
5. [ACL2 HONS and Memoization](https://www.cs.utexas.edu/~moore/acl2/v6-3/HONS-AND-MEMOIZATION.html)
6. [Efficient Symbolic Computation via Hash Consing](https://arxiv.org/html/2509.20534v2), arXiv 2025

### Hash Functions
7. [rapidhash - GitHub](https://github.com/Nicoshev/rapidhash) — Official wyhash successor
8. [rapidhash-js - TypeScript implementation](https://github.com/komiya-atsushi/rapidhash-js)
9. [SMHasher - Hash function quality tests](https://github.com/rurban/smhasher)
10. [wyhash - GitHub](https://github.com/wangyi-fudan/wyhash)
11. [Boost hash_combine](https://gist.github.com/eugene-malashkin/884e225ff57aca1b9cbe)

### Unification Algorithms
12. Paterson & Wegman, [Linear Unification](https://www.sciencedirect.com/science/article/pii/0022000078900430), J. Computer and System Sciences, 1978
13. Martelli & Montanari, [An Efficient Unification Algorithm](https://dl.acm.org/doi/10.1145/357162.357169), ACM TOPLAS, 1982
14. [Almost Linear Unification](https://link.springer.com/article/10.1007/BF00263501), Acta Informatica, 1989
15. [Comparing Unification Algorithms](http://www.cs.man.ac.uk/~hoderk/ubench/unification_full.pdf), University of Manchester

### Variable Binding
16. [De Bruijn index - Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index)
17. Charguéraud, [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf), 2009

### Related Systems
18. [egg: Fast and Extensible Equality Saturation](https://egraphs-good.github.io/)
19. [Binary Decision Diagrams](https://course.khoury.northeastern.edu/csu690/notes/bdd.html), Northeastern CS
20. [Unison: The Big Idea](https://www.unison-lang.org/docs/the-big-idea/)

### Implementation References
21. [Immutable.js: Structural Sharing](https://medium.com/@dtinth/immutable-js-persistent-data-structures-and-structural-sharing-6d163fbd73d2)
22. [Zig Arena Allocators](https://zig.guide/standard-library/allocators/)
23. [WeakRef in JavaScript](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/WeakRef)
24. [Union-Find / Disjoint Set](https://en.wikipedia.org/wiki/Disjoint-set_data_structure), Wikipedia

---

## Appendix: Current Code Hotspots

### sequent.js:255 — Context insertion
```javascript
let id = sha3(ast.toString())  // O(n) every time
```
**Fix:** Use interned node ID directly.

### mgu.js:23 — Equality check
```javascript
let isEq = t0.toString() === t1.toString();  // O(n)
```
**Fix:** Compare interned IDs.

### substitute.js — Creates copies
```javascript
return val.copy();  // O(n)
```
**Fix:** Return interned ID; subtrees already shared.

### proofstate.js — Repeated sequent operations
Many calls to `Sequent.copy()`, `add_to_linear_ctx()`, etc.
**Fix:** With interning, these become O(1) or O(k).
