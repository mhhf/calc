# Arena Allocation for Proof Search

Deep dive into region-based memory management for efficient backtracking.

---

## 1. The Problem: Allocation and GC Pressure

### Current Allocation Pattern

Proof search creates many short-lived objects:

```javascript
// proofstate.js:414-419
pt.premisses = rule.slice(1)
  .map(seq => seq.substitute(theta))    // New sequent objects
  .map(seq => new PT({                  // New proof tree nodes
    conclusion: seq,
    proverState: pt.proverState ? pt.proverState.copy() : null  // Copied state
  }));
```

Each proof step allocates:
1. **Sequent copies** (linear_ctx, persistent_ctx, succedent)
2. **Proof tree nodes** (premisses array, conclusion, metadata)
3. **Intermediate arrays** (theta substitutions, delta_in/out)
4. **Formula copies** (from substitute, copy operations)

### The GC Problem

JavaScript's garbage collector must:
1. Track all allocated objects
2. Periodically scan for unreachable objects
3. Compact memory (in some engines)

For proof search with high backtracking:
- **Allocate** 10,000 objects in failed branches
- **Mark** them unreachable when backtracking
- **GC pause** to reclaim memory
- **Repeat** for next branch

**Result:** GC pauses during proof search, unpredictable latency.

### Memory Fragmentation

Deep proof trees interleave allocations:
```
Branch 1: [A1] [B1] [C1] ...
Branch 2: [A2] [B2] [C2] ...
Backtrack 2: [A2] [B2] [C2] become garbage but A1, B1 still live
New Branch 3: [A3] ... must find space among holes
```

Fragmentation → worse cache locality → slower traversal.

---

## 2. Arena Allocation: Core Concept

### Bump Allocation

An **arena** (or **region**) is a contiguous memory block with a simple allocation strategy:

```
Arena: [--------------------------------]
        ^
        bump pointer

Allocate 8 bytes:
Arena: [XXXXXXXX------------------------]
                ^
                bump pointer (moved forward)

Allocate 16 bytes:
Arena: [XXXXXXXXYYYYYYYYYYYYYYYY--------]
                                ^
                                bump pointer
```

**Allocation = increment pointer.** No bookkeeping, no fragmentation, cache-friendly.

### Bulk Deallocation

Instead of freeing individual objects, free the entire arena:

```
// After proof branch completes or fails
arena.reset();  // Instantly reclaim ALL memory

Arena: [--------------------------------]
        ^
        bump pointer (back to start)
```

**Deallocation = reset pointer.** No GC scan, O(1) cleanup.

---

## 3. Scoped Arenas for Backtracking

### The Key Insight

Proof search has **nested lifetimes**:

```
prove(sequent)
├── try rule A
│   ├── premise 1  ← lives until A completes
│   └── premise 2  ← lives until A completes
│   (backtrack - all A's allocations die together)
├── try rule B
│   ├── premise 1  ← lives until B completes
│   └── ...
│   (success - keep B's allocations)
```

Allocations within a branch **die together** when backtracking!

### Scoped Arena Pattern

```javascript
class ScopedArena {
  constructor(parent = null) {
    this.buffer = new ArrayBuffer(ARENA_SIZE);
    this.view = new DataView(this.buffer);
    this.offset = 0;
    this.parent = parent;
    this.checkpoint = parent ? parent.offset : 0;
  }

  // Allocate n bytes, return offset
  alloc(n) {
    const aligned = (this.offset + 7) & ~7;  // 8-byte alignment
    if (aligned + n > this.buffer.byteLength) {
      throw new Error('Arena overflow');
    }
    const ptr = aligned;
    this.offset = aligned + n;
    return ptr;
  }

  // Create child scope
  fork() {
    return new ScopedArena(this);
  }

  // Discard this scope's allocations
  discard() {
    this.offset = this.checkpoint;
  }

  // Commit allocations to parent (no-op, just don't discard)
  commit() {
    if (this.parent) {
      this.parent.offset = this.offset;
    }
  }
}
```

### Usage in Proof Search

```javascript
function proofSearch(sequent, arena) {
  if (isAxiom(sequent)) {
    return { success: true };
  }

  for (const rule of applicableRules(sequent)) {
    // Fork arena for this attempt
    const branchArena = arena.fork();

    // All allocations go to branchArena
    const premises = applyRule(sequent, rule, branchArena);

    let allSucceed = true;
    for (const premise of premises) {
      const result = proofSearch(premise, branchArena);
      if (!result.success) {
        allSucceed = false;
        break;
      }
    }

    if (allSucceed) {
      branchArena.commit();  // Keep allocations
      return { success: true };
    } else {
      branchArena.discard();  // Instant cleanup!
    }
  }

  return { success: false };
}
```

---

## 4. JavaScript Implementation Challenges

### Challenge 1: No Manual Memory Control

JavaScript doesn't expose raw memory management. We can't truly "allocate" or "free."

**Workaround:** Use TypedArrays as manual memory regions:

```javascript
class TypedArena {
  constructor(capacity = 1024 * 1024) {  // 1MB default
    this.buffer = new ArrayBuffer(capacity);
    this.u8 = new Uint8Array(this.buffer);
    this.u32 = new Uint32Array(this.buffer);
    this.f64 = new Float64Array(this.buffer);
    this.offset = 0;
  }

  allocU32(count) {
    const byteOffset = (this.offset + 3) & ~3;  // 4-byte align
    const index = byteOffset / 4;
    this.offset = byteOffset + count * 4;
    return index;  // Return index into u32 view
  }

  allocF64(count) {
    const byteOffset = (this.offset + 7) & ~7;  // 8-byte align
    const index = byteOffset / 8;
    this.offset = byteOffset + count * 8;
    return index;  // Return index into f64 view
  }
}
```

### Challenge 2: Object References

JavaScript objects can't be stored in TypedArrays. We need **handles/indices**:

```javascript
class ArenaStore {
  constructor() {
    // Typed data in arena
    this.arena = new TypedArena();

    // Object pool for things that must be JS objects
    this.objects = [];
    this.freeList = [];
  }

  // Allocate JS object, return handle
  allocObject(obj) {
    let handle;
    if (this.freeList.length > 0) {
      handle = this.freeList.pop();
      this.objects[handle] = obj;
    } else {
      handle = this.objects.length;
      this.objects.push(obj);
    }
    return handle;
  }

  // Get object by handle
  getObject(handle) {
    return this.objects[handle];
  }

  // Free object (add to free list, don't actually delete)
  freeObject(handle) {
    this.objects[handle] = null;
    this.freeList.push(handle);
  }
}
```

### Challenge 3: Structure Layout

We need to manually define data layouts:

```javascript
// Term layout in arena (all as 32-bit values):
// [0]: constructor ID
// [1]: arity (n)
// [2..n+1]: child handles

class ArenaTerm {
  constructor(arena, offset) {
    this.arena = arena;
    this.offset = offset;
  }

  get constructorId() {
    return this.arena.u32[this.offset];
  }

  get arity() {
    return this.arena.u32[this.offset + 1];
  }

  getChild(i) {
    return this.arena.u32[this.offset + 2 + i];
  }

  static alloc(arena, constructorId, children) {
    const arity = children.length;
    const offset = arena.allocU32(2 + arity);
    arena.u32[offset] = constructorId;
    arena.u32[offset + 1] = arity;
    for (let i = 0; i < arity; i++) {
      arena.u32[offset + 2 + i] = children[i];
    }
    return offset;
  }
}
```

---

## 5. Hybrid Approach: Object Pool + Scopes

Given JavaScript's constraints, a **hybrid** approach works better:

```javascript
class ScopedObjectPool {
  constructor() {
    this.scopes = [];      // Stack of scope boundaries
    this.objects = [];     // All allocated objects
    this.currentScope = 0; // Current scope depth
  }

  // Enter new scope
  pushScope() {
    this.scopes.push(this.objects.length);
    this.currentScope++;
  }

  // Exit scope, discarding allocations
  popScope() {
    const boundary = this.scopes.pop();
    // Truncate - let GC handle the rest
    this.objects.length = boundary;
    this.currentScope--;
  }

  // Allocate object in current scope
  alloc(obj) {
    this.objects.push(obj);
    return obj;  // Return object directly (JS reference)
  }

  // Create new sequent in current scope
  allocSequent(linearCtx, persistentCtx, succedent) {
    return this.alloc(new Sequent({ linearCtx, persistentCtx, succedent }));
  }

  // Create new proof tree node in current scope
  allocPT(conclusion) {
    return this.alloc(new PT({ conclusion }));
  }
}
```

### Usage

```javascript
const pool = new ScopedObjectPool();

function proofSearch(sequent) {
  if (isAxiom(sequent)) return { success: true };

  for (const rule of applicableRules(sequent)) {
    pool.pushScope();  // Enter scope for this attempt

    const premises = rule.premisses.map(p =>
      pool.allocSequent(/* ... */)
    );

    let success = true;
    for (const premise of premises) {
      if (!proofSearch(premise).success) {
        success = false;
        break;
      }
    }

    if (success) {
      // Keep allocations (don't pop scope yet)
      return { success: true };
    }

    pool.popScope();  // Discard all allocations from this attempt
  }

  return { success: false };
}
```

---

## 6. Integration with Content-Addressing

### Store as Arena

With content-addressing, the Store itself can be arena-like:

```javascript
class ScopedStore {
  constructor(parent = null) {
    this.parent = parent;
    this.localTerms = new Map();    // hash → term (local to this scope)
    this.localStructs = new Map();  // hash → structural data
  }

  // Look up term (check local, then parent)
  get(hash) {
    if (this.localTerms.has(hash)) {
      return this.localTerms.get(hash);
    }
    return this.parent?.get(hash);
  }

  // Intern term (always in local scope)
  intern(term) {
    const hash = this.computeHash(term);
    if (!this.has(hash)) {
      this.localTerms.set(hash, term);
    }
    return hash;
  }

  // Check if term exists (local or parent)
  has(hash) {
    return this.localTerms.has(hash) || (this.parent?.has(hash) ?? false);
  }

  // Fork for new proof branch
  fork() {
    return new ScopedStore(this);
  }

  // Discard local terms (backtrack)
  discard() {
    this.localTerms.clear();
    this.localStructs.clear();
  }

  // Commit to parent (merge local into parent)
  commit() {
    if (this.parent) {
      for (const [hash, term] of this.localTerms) {
        this.parent.localTerms.set(hash, term);
      }
      for (const [hash, struct] of this.localStructs) {
        this.parent.localStructs.set(hash, struct);
      }
    }
  }
}
```

### Memory Model

```
Root Store (long-lived)
├── Original input terms
├── Shared subterms
│
├── Branch A Store (fork)
│   ├── Terms created during A
│   └── (discard on backtrack)
│
└── Branch B Store (fork)
    ├── Terms created during B
    └── (commit on success → merge to root)
```

---

## 7. Performance Analysis

### Without Arena/Scoping

```
Proof search with b=3 branches, d=10 depth:
- Nodes explored: 3^10 ≈ 59,049
- Objects per node: ~20 (sequent, PT, arrays, copies)
- Total allocations: ~1.2 million
- GC work: Track all 1.2M, scan for reachable
- GC pauses: Multiple, unpredictable
```

### With Scoped Object Pool

```
Same proof search:
- Total allocations: ~1.2 million (same)
- But: Organized into ~59,049 scopes
- Backtrack: Truncate array (O(1))
- GC work: Only scan live objects at end
- GC pauses: Fewer, more predictable
```

### With Scoped Store (Content-Addressing)

```
Same proof search:
- Term allocations: O(n²) due to subformula property
- Shared via hashing: Most lookups, few allocations
- Backtrack: Clear local Map (O(k) where k = new terms)
- GC work: Minimal - Maps cleared on backtrack
- GC pauses: Rare
```

---

## 8. Edge Cases

### Deep Recursion

JavaScript has limited stack depth (~10,000 calls). Deep proofs may overflow.

**Solution:** Iterative with explicit stack:

```javascript
function proofSearchIterative(rootSequent) {
  const pool = new ScopedObjectPool();
  const stack = [{
    sequent: rootSequent,
    ruleIndex: 0,
    premiseIndex: 0,
    premises: null,
    scopeDepth: pool.currentScope
  }];

  while (stack.length > 0) {
    const frame = stack[stack.length - 1];

    if (isAxiom(frame.sequent)) {
      stack.pop();
      continue;  // Success, propagate up
    }

    const rules = applicableRules(frame.sequent);

    if (frame.ruleIndex >= rules.length) {
      // All rules failed, backtrack
      while (pool.currentScope > frame.scopeDepth) {
        pool.popScope();
      }
      stack.pop();
      continue;
    }

    if (frame.premises === null) {
      // Start new rule attempt
      pool.pushScope();
      const rule = rules[frame.ruleIndex];
      frame.premises = applyRule(frame.sequent, rule, pool);
      frame.premiseIndex = 0;
    }

    if (frame.premiseIndex < frame.premises.length) {
      // Push next premise
      stack.push({
        sequent: frame.premises[frame.premiseIndex],
        ruleIndex: 0,
        premiseIndex: 0,
        premises: null,
        scopeDepth: pool.currentScope
      });
      frame.premiseIndex++;
    } else {
      // All premises succeeded
      frame.ruleIndex++;
      frame.premises = null;
    }
  }

  return { success: true };
}
```

### Sharing Across Branches

Some terms should be shared globally (e.g., input formula subterms):

```javascript
class ScopedStore {
  constructor(parent = null, global = null) {
    this.parent = parent;
    this.global = global || this;  // Root is its own global
    this.localTerms = new Map();
  }

  // Intern in global (for input terms)
  internGlobal(term) {
    const hash = this.computeHash(term);
    if (!this.global.localTerms.has(hash)) {
      this.global.localTerms.set(hash, term);
    }
    return hash;
  }

  // Intern in local (for proof-specific terms)
  internLocal(term) {
    const hash = this.computeHash(term);
    if (!this.has(hash)) {
      this.localTerms.set(hash, term);
    }
    return hash;
  }
}
```

---

## 9. Recommendation

### Verdict: **PARTIAL IMPLEMENT** (Scoped Store only)

**Priority:** LOW

**Effort:** MEDIUM

### Rationale

**Pros:**
1. Reduces GC pressure during backtracking
2. Cleaner memory semantics (scope = lifetime)
3. Natural fit with content-addressing
4. Predictable cleanup

**Cons:**
1. JavaScript doesn't support true arenas
2. Object pool adds complexity
3. Benefits are modest in JS (GC is already good)
4. Explicit scope management is error-prone

### What to Implement

1. **YES: ScopedStore** - Fork/commit/discard for term storage
   - Easy to implement
   - Works with content-addressing
   - Clear benefit for backtracking

2. **MAYBE: ScopedObjectPool** - Only if profiling shows GC bottleneck
   - More complex
   - Marginal benefit in JS
   - Consider only for very deep proofs

3. **NO: TypedArray arenas** - Too much complexity
   - Requires manual memory layout
   - Loses JS object semantics
   - Better for WASM/native

### Recommended Implementation

```javascript
class ScopedStore {
  constructor(parent = null) {
    this.parent = parent;
    this.terms = new Map();
    this.sequents = new Map();  // For memoization
  }

  fork() {
    return new ScopedStore(this);
  }

  discard() {
    this.terms.clear();
    this.sequents.clear();
  }

  commit() {
    if (this.parent) {
      for (const [k, v] of this.terms) this.parent.terms.set(k, v);
      for (const [k, v] of this.sequents) this.parent.sequents.set(k, v);
    }
  }

  getTerm(hash) {
    return this.terms.get(hash) ?? this.parent?.getTerm(hash);
  }

  internTerm(term) {
    const hash = computeHash(term);
    if (!this.hasTerm(hash)) {
      this.terms.set(hash, term);
    }
    return hash;
  }

  hasTerm(hash) {
    return this.terms.has(hash) || (this.parent?.hasTerm(hash) ?? false);
  }
}

// Usage in proof search
function prove(sequent, store) {
  for (const rule of rules) {
    const branchStore = store.fork();

    const result = tryRule(sequent, rule, branchStore);

    if (result.success) {
      branchStore.commit();
      return result;
    }

    branchStore.discard();
  }
}
```

---

## 10. References

- [Region-based Memory Management - Wikipedia](https://en.wikipedia.org/wiki/Region-based_memory_management)
- [Bumpalo: Rust Bump Allocator](https://github.com/fitzgen/bumpalo)
- [bump-scope: Scoped Bump Allocator](https://github.com/bluurryy/bump-scope)
- [Arena Allocators (Ryan Fleury)](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)
- [Tofte & Talpin: Region Inference](https://dl.acm.org/doi/10.1145/237721.237771)
