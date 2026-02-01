# Content-Addressed Refactoring Plan

Comprehensive plan to refactor CALC to use content-addressed formulas with O(1) equality, structural sharing, and efficient memory management.

---

## Goals

1. **O(1) equality checking** — Hash comparison replaces O(n) string comparison
2. **Structural sharing** — Identical subtrees share memory
3. **Efficient memory** — TypedArray pools, no deep copying
4. **Zig-portable design** — Clean data structures that map to Zig
5. **Test-driven** — Write failing tests first, then implement
6. **Profiling from day 1** — Built-in counters and benchmarks to identify bottlenecks

---

## Current Performance Problems

| Location | Problem | Impact |
|----------|---------|--------|
| `sequent.js:255` | `sha3(ast.toString())` for context keys | O(n) per formula |
| `node.js:23-26` | `node.copy()` deep copies | O(n) per copy |
| `mgu.js:23` | `t0.toString() === t1.toString()` | O(n) equality |
| `substitute.js:19` | `val.copy()` on substitution | O(n) per substitution |
| `sequent.js:209-229` | `Sequent.copy()` deep copies all | O(m·n) for m formulas |

---

## Architecture Overview

```
NEW MODULES:
┌─────────────────────────────────────────────────────────────────────────────┐
│  lib/store.js           — TypedArray-based hash-consing store              │
│    Store                — Main store with typed pools                       │
│    ScopedStore          — Branch-scoped store for proof search             │
│    Pool                 — Pool type enum                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│  lib/hash.js            — Fast 64-bit hashing (FNV-1a, wyhash optional)    │
│    hash64               — Hash arbitrary data to u64                        │
│    binHash              — Canonical hash for 256-bit values                 │
│    structHash           — Hash structural nodes                             │
├─────────────────────────────────────────────────────────────────────────────┤
│  lib/term.js            — Content-addressed term representation             │
│    Term                 — Wrapper around hash + store reference             │
│    term.equals()        — O(1) equality via hash                            │
│    term.children()      — Lazy child access                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  lib/intern.js          — Parser → Store interning                          │
│    internNode           — Convert Node AST to content-addressed Term        │
│    externNode           — Convert Term back to Node (for rendering)         │
└─────────────────────────────────────────────────────────────────────────────┘

MODIFIED MODULES:
┌─────────────────────────────────────────────────────────────────────────────┐
│  lib/sequent.js         — Use Term hashes instead of sha3(toString())      │
│  lib/mgu.js             — Use O(1) hash equality                            │
│  lib/substitute.js      — Return new Term instead of mutating              │
│  lib/proofstate.js      — Use ScopedStore for branch isolation             │
│  lib/prover.js          — Integrate with new term representation           │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Phase 0: Benchmarking Infrastructure (FIRST!)

Before any optimization, establish measurement infrastructure so we can quantify improvements.

### 0.1 Implement `lib/profiler.js`

**Test first:** `tests/profiler.js`

```javascript
// tests/profiler.js
describe('Profiler', () => {
  it('should track operation counts', () => {
    const profiler = new Profiler();
    profiler.count('mgu');
    profiler.count('mgu');
    profiler.count('substitute');
    profiler.stats().mgu.should.equal(2);
    profiler.stats().substitute.should.equal(1);
  });

  it('should time operations', () => {
    const profiler = new Profiler();
    const end = profiler.time('mgu');
    // ... do work ...
    end();
    profiler.stats().mgu_time.should.be.greaterThan(0);
  });

  it('should track nested scopes', () => {
    const profiler = new Profiler();
    profiler.push('branch1');
    profiler.count('mgu');
    profiler.pop();
    profiler.push('branch2');
    profiler.count('mgu');
    profiler.pop();
    // Should have counts per branch
  });

  it('should be disabled by default (zero overhead)', () => {
    const profiler = new Profiler({ enabled: false });
    profiler.count('mgu');
    profiler.stats().mgu.should.equal(0);
  });
});
```

**Implementation:** `lib/profiler.js`

```javascript
class Profiler {
  constructor(opts = {}) {
    this.enabled = opts.enabled ?? (process.env.CALC_PROFILE === '1');
    this.counters = {};
    this.timers = {};
    this.scope = [];
  }

  count(name) {
    if (!this.enabled) return;
    const key = this._key(name);
    this.counters[key] = (this.counters[key] || 0) + 1;
  }

  time(name) {
    if (!this.enabled) return () => {};
    const key = this._key(name);
    const start = performance.now();
    return () => {
      const elapsed = performance.now() - start;
      if (!this.timers[key]) this.timers[key] = { total: 0, count: 0, max: 0 };
      this.timers[key].total += elapsed;
      this.timers[key].count++;
      this.timers[key].max = Math.max(this.timers[key].max, elapsed);
    };
  }

  push(scope) { if (this.enabled) this.scope.push(scope); }
  pop() { if (this.enabled) this.scope.pop(); }

  _key(name) {
    return this.scope.length ? `${this.scope.join('/')}.${name}` : name;
  }

  stats() { return { counters: this.counters, timers: this.timers }; }

  report() {
    if (!this.enabled) return 'Profiling disabled. Set CALC_PROFILE=1';
    // Pretty print stats
  }

  reset() {
    this.counters = {};
    this.timers = {};
  }
}

// Global instance
const profiler = new Profiler();
module.exports = { Profiler, profiler };
```

### 0.2 Instrument Current Code

Add profiling hooks to current implementation (before refactoring):

```javascript
// lib/mgu.js - add at top
const { profiler } = require('./profiler');

function mgu(G) {
  const endTime = profiler.time('mgu');
  profiler.count('mgu_call');
  // ... existing code ...
  endTime();
  return theta;
}
```

**Locations to instrument:**
- `lib/mgu.js` — mgu calls, iterations, substitution propagations
- `lib/substitute.js` — substitute calls, node traversals
- `lib/sequent.js` — copy, add_to_ctx, hash computations
- `lib/proofstate.js` — proof steps, backtrack count, depth
- `lib/prover.js` — identity attempts, focus choices

### 0.3 Create Benchmark Suite

**Directory structure:**
```
benchmarks/
├── micro/                  # Operation-level benchmarks
│   ├── mgu.bench.js
│   ├── substitute.bench.js
│   └── hash.bench.js
├── proof/                  # Full proof benchmarks
│   ├── simple.bench.js     # Identity, modus ponens
│   ├── medium.bench.js     # Currying, distribution
│   └── stress.bench.js     # Deep nesting, high branching
├── fixtures/               # Test formulas and nodes
│   └── formulas.js
├── lib/
│   └── runner.js           # Benchmark runner (see benchmarking.md)
└── baseline.json           # Recorded baseline measurements
```

### 0.4 Collect Baseline

Before ANY code changes, run benchmarks and save baseline:

```bash
# Run full benchmark suite
CALC_PROFILE=1 npm run bench > benchmarks/baseline.json

# Example baseline output:
{
  "timestamp": "2024-XX-XX",
  "commit": "abc123",
  "results": {
    "mgu_simple": { "mean": 0.12, "p95": 0.18, "ops": 8333 },
    "mgu_complex": { "mean": 1.45, "p95": 2.10, "ops": 689 },
    "proof_identity": { "mean": 2.3, "ops": { "mgu": 2, "sub": 0 } },
    "proof_currying": { "mean": 45.2, "ops": { "mgu": 15, "sub": 87 } },
    ...
  }
}
```

### 0.5 npm Scripts

```json
{
  "scripts": {
    "bench": "node --expose-gc benchmarks/run.js",
    "bench:micro": "node --expose-gc benchmarks/run.js --category=micro",
    "bench:proof": "node --expose-gc benchmarks/run.js --category=proof",
    "bench:compare": "node benchmarks/compare.js",
    "profile": "CALC_PROFILE=1 node libexec/calc-proof"
  }
}
```

---

## Phase 1: Foundation (Store + Hash)

### 1.1 Implement `lib/hash.js`

**Test first:** `tests/hash.js`

```javascript
// tests/hash.js
describe('hash64', () => {
  it('should produce consistent hashes for same input', () => {
    hash64('hello').should.equal(hash64('hello'));
  });

  it('should produce different hashes for different inputs', () => {
    hash64('hello').should.not.equal(hash64('world'));
  });

  it('should handle BigInt values', () => {
    const h = hash64(42n);
    (typeof h).should.equal('bigint');
  });

  it('should handle Uint8Array', () => {
    const buf = new Uint8Array([1, 2, 3]);
    hash64(buf).should.be.ok;
  });
});

describe('binHash', () => {
  it('should produce canonical hash for 256-bit value', () => {
    const h = binHash(0xffn);
    (typeof h).should.equal('bigint');
  });

  it('should produce same hash for same value', () => {
    binHash(12345n).should.equal(binHash(12345n));
  });
});

describe('structHash', () => {
  it('should include constructor ID in hash', () => {
    const h1 = structHash(1, [0x123n]);
    const h2 = structHash(2, [0x123n]);
    h1.should.not.equal(h2);
  });

  it('should include children in hash', () => {
    const h1 = structHash(1, [0x123n]);
    const h2 = structHash(1, [0x456n]);
    h1.should.not.equal(h2);
  });
});
```

**Implementation:** `lib/hash.js`

- FNV-1a 64-bit hash (pure JS, fast, good distribution)
- No external dependencies
- ~50 lines of code

### 1.2 Implement `lib/store.js`

**Test first:** `tests/store.js`

```javascript
// tests/store.js
describe('Store', () => {
  describe('intern/get roundtrip', () => {
    it('should intern and retrieve 256-bit bin', () => {
      const store = new Store();
      const value = 0xdeadbeefn;
      const hash = store.internBin(value);
      store.getBin(hash).should.equal(value);
    });

    it('should intern and retrieve 64-bit nat', () => {
      const store = new Store();
      const hash = store.internNat(42n);
      store.getNat(hash).should.equal(42n);
    });

    it('should intern and retrieve string', () => {
      const store = new Store();
      const hash = store.internString('hello');
      store.getString(hash).should.equal('hello');
    });

    it('should intern and retrieve structural node', () => {
      const store = new Store();
      const childHash = store.internNat(1n);
      const hash = store.internStructural(7, [childHash]);
      const node = store.getStructural(hash);
      node.constructorId.should.equal(7);
      node.children[0].should.equal(childHash);
    });
  });

  describe('deduplication', () => {
    it('should return same hash for same bin value', () => {
      const store = new Store();
      const h1 = store.internBin(42n);
      const h2 = store.internBin(42n);
      h1.should.equal(h2);
      store.stats().binPool.length.should.equal(1);
    });

    it('should return same hash for same structural node', () => {
      const store = new Store();
      const child = store.internNat(1n);
      const h1 = store.internStructural(5, [child]);
      const h2 = store.internStructural(5, [child]);
      h1.should.equal(h2);
    });
  });

  describe('equality', () => {
    it('should be O(1) hash comparison', () => {
      const store = new Store();
      const h1 = store.internBin(42n);
      const h2 = store.internBin(42n);
      store.equal(h1, h2).should.be.true;
    });
  });

  describe('pool growth', () => {
    it('should grow pools when capacity exceeded', () => {
      const store = new Store(4); // Small initial capacity
      for (let i = 0n; i < 100n; i++) {
        store.internNat(i);
      }
      store.stats().natPool.length.should.equal(100);
    });
  });
});

describe('ScopedStore', () => {
  it('should inherit from parent', () => {
    const root = new Store();
    const rootHash = root.internNat(42n);

    const scoped = new ScopedStore(root);
    scoped.getNat(rootHash).should.equal(42n);
  });

  it('should isolate local additions', () => {
    const root = new Store();
    const scoped = new ScopedStore(root);

    scoped.internNat(99n);
    root.stats().natPool.length.should.equal(0);
    scoped.local.stats().natPool.length.should.equal(1);
  });

  it('should commit local to parent', () => {
    const root = new Store();
    const scoped = new ScopedStore(root);

    const hash = scoped.internNat(123n);
    scoped.commit();

    root.getNat(hash).should.equal(123n);
  });

  it('should fork for nested branches', () => {
    const root = new Store();
    const branch1 = new ScopedStore(root);
    const branch2 = branch1.fork();

    branch2.internNat(456n);
    branch2.commit();
    branch1.commit();

    root.stats().natPool.length.should.equal(1);
  });
});
```

**Implementation:** `lib/store.js`

- TypedArray pools (BigUint64Array for 64-bit data)
- Map for index (hash → NodeRef)
- ScopedStore for proof search branches
- ~300 lines of code

---

## Phase 2: Term Representation

### 2.1 Implement `lib/term.js`

**Test first:** `tests/term.js`

```javascript
// tests/term.js
describe('Term', () => {
  describe('equality', () => {
    it('should compare by hash (O(1))', () => {
      const store = new Store();
      const t1 = Term.fromHash(store, store.internNat(42n));
      const t2 = Term.fromHash(store, store.internNat(42n));
      t1.equals(t2).should.be.true;
    });

    it('should not equal different terms', () => {
      const store = new Store();
      const t1 = Term.fromHash(store, store.internNat(1n));
      const t2 = Term.fromHash(store, store.internNat(2n));
      t1.equals(t2).should.be.false;
    });
  });

  describe('structural access', () => {
    it('should access constructor id', () => {
      const store = new Store();
      const child = store.internNat(1n);
      const hash = store.internStructural(7, [child]);
      const term = Term.fromHash(store, hash);
      term.constructorId().should.equal(7);
    });

    it('should access children as Terms', () => {
      const store = new Store();
      const childHash = store.internNat(42n);
      const hash = store.internStructural(5, [childHash]);
      const term = Term.fromHash(store, hash);
      const children = term.children();
      children[0].hash.should.equal(childHash);
    });
  });

  describe('type checking', () => {
    it('should identify opaque bin', () => {
      const store = new Store();
      const hash = store.internBin(0xffn);
      const term = Term.fromHash(store, hash);
      term.isBin().should.be.true;
      term.isStructural().should.be.false;
    });

    it('should identify structural', () => {
      const store = new Store();
      const hash = store.internStructural(1, []);
      const term = Term.fromHash(store, hash);
      term.isStructural().should.be.true;
    });
  });
});
```

**Implementation:** `lib/term.js`

- Thin wrapper: `{ store, hash }`
- Lazy child access
- O(1) equality via hash comparison
- ~100 lines of code

### 2.2 Implement `lib/intern.js`

**Test first:** `tests/intern.js`

```javascript
// tests/intern.js
describe('internNode', () => {
  it('should intern leaf node (atom)', () => {
    const store = new Store();
    const node = parser.parse('-- : A |- -- : A').vals[0]; // Just antecedent
    const term = internNode(store, node);
    term.hash.should.be.ok;
  });

  it('should intern compound node (tensor)', () => {
    const store = new Store();
    const node = parser.parse('-- : A * B |- -- : A').vals[0];
    const term = internNode(store, node);
    term.isStructural().should.be.true;
  });

  it('should deduplicate identical subtrees', () => {
    const store = new Store();
    // A appears twice in A * A
    const node = parser.parse('-- : A * A |- -- : A').vals[0];
    internNode(store, node);
    // Should have interned 'A' only once
    // (verify via store stats or comparing subtree hashes)
  });

  it('should preserve node.id (rule type) as constructor id', () => {
    const store = new Store();
    const node = parser.parse('-- : A |- -- : A').vals[0];
    const term = internNode(store, node);
    const struct = store.getStructural(term.hash);
    struct.constructorId.should.equal(node.id);
  });
});

describe('externNode', () => {
  it('should reconstruct Node from Term', () => {
    const store = new Store();
    const original = parser.parse('-- : A * B |- -- : A').vals[0];
    const term = internNode(store, original);
    const reconstructed = externNode(store, term);
    reconstructed.toString().should.equal(original.toString());
  });

  it('should handle variables', () => {
    const store = new Store();
    const original = parser.parse('-- : F?X |- -- : F?X').vals[0];
    const term = internNode(store, original);
    const reconstructed = externNode(store, term);
    reconstructed.toString().should.equal(original.toString());
  });
});
```

**Implementation:** `lib/intern.js`

- `internNode(store, node)` — Bottom-up interning
- `externNode(store, term)` — Reconstruct Node (for rendering)
- Uses Calc.db.rules for node.id → constructor mapping
- ~150 lines of code

---

## Phase 3: Refactor Core Modules

### 3.1 Refactor `lib/sequent.js`

**Goal:** Replace `sha3(ast.toString())` with content hash.

**Test updates:** `tests/test.js`

```javascript
describe('Sequent with content-addressing', () => {
  it('should use hash as context key', () => {
    const store = new Store();
    const node = parser.parse('-- : A, -- : B |- -- : A');
    const seq = Sequent.fromTree(node, store);
    // Keys should be BigInt hashes, not sha3 hex strings
    Object.keys(seq.linear_ctx).forEach(key => {
      (typeof key === 'bigint' || /^\d+n?$/.test(key)).should.be.true;
    });
  });

  it('should identify duplicate formulas by hash', () => {
    const store = new Store();
    const node = parser.parse('-- : A, -- : A |- -- : A');
    const seq = Sequent.fromTree(node, store);
    // Should have one entry with num=2
    Object.keys(seq.linear_ctx).length.should.equal(1);
    Object.values(seq.linear_ctx)[0].num.should.equal(2);
  });
});
```

**Changes:**

1. `Sequent.fromTree(node, store)` — Accept store parameter
2. Context keys: `hash` (BigInt) instead of `sha3(toString())`
3. Context values: `{ num, hash }` instead of `{ num, val: node }`
4. Add `store` reference to Sequent instance
5. `Sequent.copy()` becomes O(1) — just copy hash references

**Before:**
```javascript
let id = sha3(ast.toString())  // O(n)
seq.linear_ctx[id] = {num, val: ast}
```

**After:**
```javascript
const hash = store.intern(ast)  // O(n) first time, O(1) after
seq.linear_ctx[hash] = {num, hash}  // Just store hash
```

### 3.2 Refactor `lib/mgu.js`

**Goal:** Replace `t0.toString() === t1.toString()` with hash equality.

**Test updates:** `tests/mgu.js` (new file)

```javascript
describe('MGU with content-addressing', () => {
  it('should use O(1) hash equality', () => {
    const store = new Store();
    const t1 = internNode(store, parser.parse('-- : A |- -- : A').vals[0]);
    const t2 = internNode(store, parser.parse('-- : A |- -- : A').vals[0]);

    // Should recognize equal without toString
    t1.hash.should.equal(t2.hash);
  });

  it('should unify variables', () => {
    const store = new Store();
    const f1 = 'I |- -- : F?X';
    const f2 = 'I |- -- : A';
    // ... test unification produces correct theta
  });
});
```

**Changes:**

1. Accept `store` parameter
2. Replace `t0.toString() === t1.toString()` with `t0.hash === t1.hash`
3. Work with Term objects instead of Node

**Before:**
```javascript
let isEq = t0.toString() === t1.toString();  // O(n)
```

**After:**
```javascript
let isEq = t0.hash === t1.hash;  // O(1)
```

### 3.3 Refactor `lib/substitute.js`

**Goal:** Return new Term instead of mutating.

**Changes:**

1. Accept `store` parameter
2. Return new Term (interned in store) instead of modifying in place
3. Substitution creates new structural nodes only where needed

**Before:**
```javascript
// Mutates node.vals in place
node.vals = node.vals.map(v => sub(v, key, val))
return node;
```

**After:**
```javascript
// Returns new Term with substituted children
const newChildren = children.map(c =>
  c.hash === key.hash ? val.hash : substitute(store, c, key, val).hash
);
return Term.fromHash(store, store.internStructural(term.constructorId(), newChildren));
```

### 3.4 Refactor `lib/proofstate.js`

**Goal:** Integrate ScopedStore for branch isolation.

**Changes:**

1. Create root store at proof start
2. Fork ScopedStore for each branch
3. Commit on success, discard on failure
4. Pass store through proof search

```javascript
Proofstate.auto = function(pt, o) {
  // Get or create scoped store for this branch
  const store = o.store || new Store();
  const scopedStore = store instanceof ScopedStore ? store : new ScopedStore(store);

  // ... proof search ...

  for (const action of actions) {
    const branchStore = scopedStore.fork();
    const result = action(branchStore);
    if (result.success) {
      branchStore.commit();
      return result;
    }
    // branchStore discarded (GC handles it)
  }
};
```

---

## Phase 4: Integration and Optimization

### 4.1 Wire Everything Together

**Update call sites:**

1. `lib/parser.js` — Return Node (unchanged, interning is separate)
2. `lib/calc.js` — Initialize global store for rules
3. `lib/ruleset.js` — Intern rules once at load time
4. `lib/prover.js` — Pass store through focused prover
5. `libexec/calc-proof` — Create store at CLI entry

### 4.2 Add Proof Memoization

**New module:** `lib/memo.js`

```javascript
class ProofMemo {
  constructor() {
    this.cache = new Map();  // sequentHash → result
  }

  lookup(seq) {
    return this.cache.get(this.hashSequent(seq));
  }

  store(seq, result) {
    this.cache.set(this.hashSequent(seq), result);
  }

  hashSequent(seq) {
    // Combine: sorted ctx hashes + succedent hash
    const ctxHashes = Object.keys(seq.linear_ctx).sort();
    return hash64([...ctxHashes, seq.succedent].join(':'));
  }
}
```

### 4.3 Opaque Primitive Support (Optional)

For large numbers (256-bit EVM words), store as opaque instead of structural.

**Changes:**

1. Add `@storage opaque` annotation parsing (future DSL)
2. FFI predicates work directly with opaque values
3. Lazy expansion to structural form only when pattern matching requires it

---

## Phase 5: Cleanup and Documentation

### 5.1 Remove Dead Code

- Remove `sha3` import from `sequent.js`
- Remove `node.copy()` calls (replaced by hash references)
- Remove `Sequent.copy()` deep copying (replaced by shallow hash copy)
- Clean up `compare.js` (replaced by hash equality)

### 5.2 Update Type Definitions

Update `lib/types/*.d.ts`:

```typescript
// lib/types/term.d.ts
export interface Term {
  store: Store;
  hash: bigint;
  equals(other: Term): boolean;
  constructorId(): number;
  children(): Term[];
  isBin(): boolean;
  isNat(): boolean;
  isString(): boolean;
  isStructural(): boolean;
  isVar(): boolean;
}

// lib/types/sequent.d.ts
export interface Sequent {
  store: Store;
  persistent_ctx: Record<bigint, { hash: bigint }>;
  linear_ctx: Record<bigint, { num: number; hash: bigint }>;
  succedent: bigint;  // hash
}
```

### 5.3 Update Tests

Ensure all existing tests pass with new implementation:

1. `npm test` — All unit tests
2. `npm run test:e2e` — E2E browser tests
3. Manual testing with `calc proof` CLI

---

## Implementation Order

```
Phase 0: Benchmarking (FIRST!)
├── [ ] Phase 0.1: lib/profiler.js + tests
├── [ ] Phase 0.2: Instrument current code
├── [ ] Phase 0.3: Create benchmark suite
├── [ ] Phase 0.4: Collect baseline measurements
└── [ ] Phase 0.5: Add npm scripts

Phase 1: Foundation
├── [ ] Phase 1.1: lib/hash.js + tests
├── [ ] Phase 1.2: lib/store.js + tests
└── [ ] Phase 2.1: lib/term.js + tests

Phase 2: Interning
├── [ ] Phase 2.2: lib/intern.js + tests
└── [ ] Phase 3.1: Refactor sequent.js

Phase 3: Unification
├── [ ] Phase 3.2: Refactor mgu.js
└── [ ] Phase 3.3: Refactor substitute.js

Phase 4: Integration
├── [ ] Phase 3.4: Refactor proofstate.js
├── [ ] Phase 4.1: Wire everything together
└── [ ] Phase 4.2: Proof memoization

Phase 5: Polish
├── [ ] Phase 5.1: Remove dead code
├── [ ] Phase 5.2: Update types
└── [ ] Phase 5.3: Update all tests
├── [ ] Run benchmarks and compare to baseline
└── [ ] Document speedup achieved

Phase 6: Advanced Optimizations (DEFERRED — based on profiling)
├── [ ] If identity is slow → Constructor Index
├── [ ] If proof search repeats → Polynomial Memoization
├── [ ] If unification is slow → Near-Linear Unification
├── [ ] If copying is slow → Persistent Data Structures
├── [ ] If GC is slow → ScopedStore / Arena pattern
└── [ ] If substitution is slow → Explicit Substitutions
```

---

## Success Criteria

1. **All existing tests pass** — No regression
2. **Benchmark improvement:**
   - Sequent equality: O(1) instead of O(n)
   - Sequent copy: O(m) shallow instead of O(m·n) deep
   - Unification: ~2× faster due to O(1) equality
3. **Memory reduction:**
   - Structural sharing reduces memory for large proofs
   - TypedArrays reduce per-node overhead
4. **Clean architecture:**
   - Store is independent module
   - Term is immutable value type
   - No global mutable state in hot paths

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| BigInt Map keys may be slow in V8 | Benchmark early; fallback to string hex if needed |
| TypedArray resize overhead | Pre-allocate larger pools; benchmark growth pattern |
| Hash collisions | 64-bit hash has ~1 in 4B collision; verify on collision if paranoid |
| Breaking existing API | Keep Node.toString() working via externNode() |

---

## Files to Create

```
# Phase 0: Benchmarking
lib/profiler.js       — 100 LOC
tests/profiler.js     — 50 LOC
benchmarks/
├── lib/runner.js     — 100 LOC
├── micro/*.bench.js  — 200 LOC
├── proof/*.bench.js  — 150 LOC
└── fixtures/         — 100 LOC

# Phase 1-4: Content Addressing
lib/hash.js           — 50 LOC
lib/store.js          — 300 LOC
lib/term.js           — 100 LOC
lib/intern.js         — 150 LOC
lib/memo.js           — 50 LOC (optional)

tests/hash.js         — 50 LOC
tests/store.js        — 150 LOC
tests/term.js         — 100 LOC
tests/intern.js       — 100 LOC
tests/mgu.js          — 50 LOC

Total new code: ~1800 LOC
```

## Files to Modify

```
lib/sequent.js        — Major refactor (~200 lines affected)
lib/mgu.js            — Moderate refactor (~30 lines affected)
lib/substitute.js     — Major refactor (~30 lines affected)
lib/proofstate.js     — Moderate refactor (~50 lines affected)
lib/prover.js         — Minor changes (~20 lines affected)
lib/ruleset.js        — Minor changes (~10 lines affected)
```

---

## Additional Optimizations (Future)

These are enabled by content-addressing but not in initial scope:

1. **Parallel proof search** — ScopedStore allows safe parallelism
2. **Incremental parsing** — Content-addressed AST enables incremental updates
3. **Proof compression** — Reference repeated subproofs by hash
4. **Zig export** — TypedArray layout maps directly to Zig arrays
5. **WASM acceleration** — Hot path hashing in WebAssembly

---

## Deep Optimization Analysis

This section analyzes further optimization opportunities for **VERY LARGE** proofs and formulas. Items are categorized by priority and complexity.

### CRITICAL: Hot Path Analysis

From profiling the current code, these are the **actual hot paths** during proof search:

| Location | Operation | Frequency | Current Cost |
|----------|-----------|-----------|--------------|
| `mgu.js:23` | `t0.toString() === t1.toString()` | Every unification attempt | O(n) |
| `proofstate.js:440` | `mgu([[ctxFormula, formula]])` | Every identity check | O(n²) |
| `sequent.js:255` | `sha3(ast.toString())` | Every context add | O(n) |
| `proofstate.js:507` | `Sequent.copy(pt.conclusion)` | Every focus | O(m·n) |
| `proofstate.js:258` | `copyMS(pt.delta_in)` | Every nondeterministic choice | O(m) |
| `sequent.js:47-82` | `seq.substitute(theta)` | Every rule application | O(m·k·n) |

**Key insight:** The identity rule (`tryIdPos`/`tryIdNeg`) is the **dominant cost** because it calls `mgu()` for EACH formula in the context until it finds a match. For a context of size m and formula size n, this is O(m·n²) per identity attempt.

---

### HIGH PRIORITY: Near-Linear Unification

**Current:** Robinson unification with O(n²) complexity (due to naive substitution propagation).

**Better:** [Martelli-Montanari algorithm](https://dl.acm.org/doi/10.1145/357162.357169) with union-find achieves O(n·α(n)) ≈ O(n).

**Implementation:**

```javascript
// Current mgu.js - O(n²) due to eager substitution
theta = propagate(theta, new_theta);  // O(k·n) per iteration
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))  // O(n) per pair

// Martelli-Montanari with union-find - O(n·α(n))
class UnionFind {
  constructor() {
    this.parent = new Map();
    this.rank = new Map();
  }
  find(x) {
    if (!this.parent.has(x)) return x;
    // Path compression
    const root = this.find(this.parent.get(x));
    this.parent.set(x, root);
    return root;
  }
  union(x, y) {
    const rx = this.find(x), ry = this.find(y);
    if (rx === ry) return;
    // Union by rank
    const rankX = this.rank.get(rx) || 0;
    const rankY = this.rank.get(ry) || 0;
    if (rankX < rankY) this.parent.set(rx, ry);
    else if (rankX > rankY) this.parent.set(ry, rx);
    else { this.parent.set(ry, rx); this.rank.set(rx, rankX + 1); }
  }
}
```

**Research direction:** [A practically efficient and almost linear unification algorithm](https://www.sciencedirect.com/science/article/abs/pii/0004370288900057) by Paterson & Wegman achieves true O(n) but is more complex.

**TODO:** Benchmark current mgu vs Martelli-Montanari on realistic proof search workloads.

---

### HIGH PRIORITY: O(1) Identity via Context Index

**Current:** `tryIdPos` iterates through ALL context formulas trying unification.

```javascript
// Current: O(m·n²) - try mgu with each formula
Object.keys(ctx).find(id => {
  theta = mgu([[ctxFormula, formula]]);  // O(n²)
  return !!theta;
});
```

**Better:** Index context by constructor ID for O(1) ground lookup, O(c) variable lookup:

```javascript
class ContextIndex {
  constructor(store) {
    this.store = store;
    this.byHash = new Map();        // hash → entry (ground formulas)
    this.byConstructor = new Map(); // constructorId → [entry] (for unification)
  }

  add(hash, entry) {
    this.byHash.set(hash, entry);
    const data = this.store.getStructural(hash);
    if (!data) return;
    const ctorId = data.constructorId;
    if (!this.byConstructor.has(ctorId)) {
      this.byConstructor.set(ctorId, []);
    }
    this.byConstructor.get(ctorId).push({ hash, entry });
  }

  // O(1) for ground formulas!
  findExact(hash) {
    return this.byHash.get(hash);
  }

  // O(c) where c = formulas with same outermost constructor
  findUnifiable(hash) {
    const data = this.store.getStructural(hash);
    if (!data) return null;
    const candidates = this.byConstructor.get(data.constructorId) || [];
    // Only try unification with same-constructor candidates
    for (const { hash: candHash, entry } of candidates) {
      const theta = mgu_fast(candHash, hash);  // Still O(k) per attempt
      if (theta) return { entry, theta };
    }
    return null;
  }
}
```

**Impact:** For ground formulas (no variables), identity becomes O(1) hash lookup. For variable formulas, reduces from O(m) to O(c) where c = candidates with same constructor.

**TODO:** Implement ContextIndex, measure c/m ratio on real proofs.

---

### HIGH PRIORITY: Explicit Substitutions (Lazy Evaluation)

**Current:** Substitution eagerly traverses entire term.

```javascript
// Current substitute.js - O(n) per substitution
node.vals = node.vals.map(v => sub(v, key, val))
```

**Problem:** When we do `seq.substitute(theta)`, we traverse ALL formulas in ALL contexts even if most are unchanged. For a sequent with m formulas of size n and k substitutions, this is O(m·k·n).

**Better:** [Explicit substitution calculus](https://dl.acm.org/doi/10.1145/96709.96712) delays substitution:

```javascript
// Explicit substitution representation
// Instead of: substitute(term, x, value)
// Represent: Closure(term, {x: value})

class Closure {
  constructor(hash, env) {
    this.hash = hash;      // Original term hash
    this.env = env;        // Map: varHash → valueHash
  }

  // Force evaluation only when needed
  force(store) {
    if (this.env.size === 0) return this.hash;
    // Actually perform substitution
    return forceSubstitute(store, this.hash, this.env);
  }

  // Compose closures without forcing
  compose(otherEnv) {
    const newEnv = new Map(this.env);
    for (const [k, v] of otherEnv) {
      if (!newEnv.has(k)) newEnv.set(k, v);
    }
    return new Closure(this.hash, newEnv);
  }
}
```

**When to force:**
- Rendering (need actual term)
- Hashing for memoization (need canonical form)
- Identity check on ground formula

**Research direction:** [Explaining the lazy Krivine machine using explicit substitution](https://hal.science/inria-00198756/en/)

**TODO:** Analyze how many substitutions are applied before terms are actually needed. If many terms are created but never inspected, explicit substitutions win big.

---

### HIGH PRIORITY: Subformula Property Memoization

**Key insight from research:** [Verified and Optimized Implementation of Orthologic Proof Search](https://arxiv.org/html/2501.09418) shows that subformula property + memoization = polynomial complexity.

**Why it works:**
- Cut-free proofs have subformula property: only subformulas of input appear
- If input has n subformulas, at most O(n²) unique sequents possible
- Memoize proof results: `sequentHash → ProofResult`
- Each unique sequent computed at most once

```javascript
class ProofMemo {
  constructor() {
    this.cache = new Map();  // sequentHash → { success, theta, proofTree }
    this.hits = 0;
    this.misses = 0;
  }

  key(seq, store) {
    // Canonical key: sorted context hashes + succedent hash
    const ctxHashes = Object.keys(seq.linear_ctx)
      .map(BigInt)
      .sort((a, b) => a < b ? -1 : 1);
    const persHashes = Object.keys(seq.persistent_ctx)
      .map(BigInt)
      .sort((a, b) => a < b ? -1 : 1);
    // Use store's hash function for combining
    return store._structHash(0, [...persHashes, ...ctxHashes, seq.succedent]);
  }

  lookup(seq, store) {
    const k = this.key(seq, store);
    if (this.cache.has(k)) {
      this.hits++;
      return this.cache.get(k);
    }
    this.misses++;
    return null;
  }

  store(seq, store, result) {
    const k = this.key(seq, store);
    this.cache.set(k, result);
  }
}
```

**Complexity impact:**
- Without memoization: O(b^d) where b = branching, d = depth
- With memoization: O(n²) where n = subformulas (if subformula property holds)

**TODO:** Verify ILL has subformula property for cut-free proofs. Implement memo and measure hit rate.

---

### MEDIUM PRIORITY: Term Indexing (Substitution Trees)

For very large contexts (100s of formulas), even constructor-indexed lookup may be slow. [Substitution tree indexing](https://pure.mpg.de/rest/items/item_1834191_2/component/file_1857890/content) provides logarithmic lookup.

**When to use:** Context size > 50-100 formulas.

**Complexity:** O(log m) for retrieval vs O(c) for constructor index.

**TODO:** Research threshold where substitution trees beat simple constructor indexing.

---

### MEDIUM PRIORITY: Persistent Data Structures for Sequent

**Current:** `copyMS()` creates new object, `Sequent.copy()` deep copies.

**Better:** [Persistent data structures](https://en.wikipedia.org/wiki/Persistent_data_structure) with path copying:

```javascript
// Immutable context using HAMT (Hash Array Mapped Trie)
// Libraries: immutable.js, immer
import { Map as ImmutableMap } from 'immutable';

class PersistentSequent {
  constructor(persistentCtx, linearCtx, succedent) {
    this.persistentCtx = persistentCtx;  // ImmutableMap
    this.linearCtx = linearCtx;          // ImmutableMap
    this.succedent = succedent;          // hash
  }

  // O(log m) update, O(1) "copy"
  addToLinear(hash, entry) {
    return new PersistentSequent(
      this.persistentCtx,
      this.linearCtx.set(hash, entry),
      this.succedent
    );
  }

  // O(1) "copy" - just return this (immutable!)
  copy() {
    return this;
  }
}
```

**Trade-off:**
- Allocation: O(log m) vs O(m) for full copy
- Access: O(log m) vs O(1) for plain object
- Memory: Sharing across branches saves memory

**TODO:** Benchmark ImmutableMap vs plain object for realistic context sizes.

---

### MEDIUM PRIORITY: Arena Allocation for Proof Branches

**Concept:** Each proof branch gets its own arena. On backtrack, free entire arena at once.

**JavaScript:** Already have ScopedStore design. Main benefit is avoiding GC pauses.

**Zig:** [Arena allocators](https://www.gingerbill.org/article/2019/02/08/memory-allocation-strategies-002/) are idiomatic:

```zig
pub fn searchBranch(parent_arena: *ArenaAllocator) !ProofResult {
    // Create child arena for this branch
    var branch_arena = ArenaAllocator.init(parent_arena.allocator);
    defer branch_arena.deinit();  // Free everything on backtrack

    // All allocations in this branch use branch_arena
    const store = ScopedStore.init(&branch_arena, parent_store);
    // ... proof search ...

    if (success) {
        // Commit: copy results to parent arena before branch_arena dies
        return commitToParent(parent_arena, result);
    }
    // On failure: branch_arena.deinit() frees everything - O(1)!
}
```

**Impact:**
- Failed branches: O(1) deallocation instead of GC traversal
- No GC pauses during search
- Better cache locality

**TODO:** Measure GC time percentage in long proof searches.

---

### MEDIUM PRIORITY: Proof Compression via Lemma Extraction

For VERY LARGE proofs, storage becomes an issue. [Automated Proof Compression by Invention of New Definitions](https://link.springer.com/chapter/10.1007/978-3-642-17511-4_25) shows 10%+ compression.

**Technique:** Find repeated subproofs, extract as lemmas.

```javascript
class ProofCompressor {
  compress(proofTree) {
    // Find repeated subtrees by hash
    const subtreeCount = new Map();
    this.countSubtrees(proofTree, subtreeCount);

    // Extract frequent subtrees as lemmas
    const lemmas = [];
    for (const [hash, count] of subtreeCount) {
      if (count > 1 && this.sizeOf(hash) > THRESHOLD) {
        lemmas.push({ hash, proof: this.getSubtree(hash) });
      }
    }

    // Replace repeated subtrees with lemma references
    return this.replaceWithRefs(proofTree, lemmas);
  }
}
```

**TODO:** Analyze typical proof tree shapes to estimate compression ratio.

---

### LOW PRIORITY: SIMD Hashing

For very large terms, hashing can be accelerated with SIMD:

**JavaScript:** Not directly available, but WASM can use SIMD.

**Zig:** Native SIMD support:

```zig
const std = @import("std");
const Vector = std.meta.Vector;

fn hashChunk(data: [32]u8) u64 {
    // Use SIMD to process 32 bytes at once
    const v: Vector(32, u8) = data;
    // ... SIMD operations ...
}
```

**TODO:** Only worth it for very large opaque values (256-bit+). Benchmark first.

---

### LOW PRIORITY: Parallel Proof Search

Content-addressing enables safe parallelism:

```javascript
// Parallel branch exploration
async function parallelSearch(pt, branches, store) {
  const results = await Promise.all(
    branches.map(branch => {
      const scopedStore = store.fork();
      return searchWorker(branch, scopedStore);
    })
  );

  // Find first success
  const success = results.find(r => r.success);
  if (success) {
    success.store.commit();
    return success;
  }
  return { success: false };
}
```

**Challenges:**
- Worker communication overhead
- Proof tree reconstruction
- Not beneficial for small proofs

**TODO:** Measure branching factor and depth to estimate parallelism benefit.

---

## Research Directions (TODO)

These need more investigation before deciding whether to implement:

### 1. De Bruijn Indices for Alpha-Equivalence

**Question:** Do we need alpha-equivalence? Current system uses named variables.

**If yes:** De Bruijn indices make alpha-equivalent terms identical, improving hash sharing.

**Research:** [De Bruijn index](https://en.wikipedia.org/wiki/De_Bruijn_index)

### 2. E-graphs for Equality Reasoning

**Question:** Do we need congruence closure or equality saturation?

**If yes:** [E-graphs](https://egraphs-good.github.io/) compactly represent equivalence classes.

**Relevance:** Might be useful for arithmetic FFI or when adding equality to the logic.

### 3. BDD-style Reduction Rules

**Question:** Can we apply BDD reduction rules to formula representation?

**Potential:** Some formulas have canonical forms that could be computed during interning.

**Research:** [Binary Decision Diagrams](https://course.khoury.northeastern.edu/csu690/notes/bdd.html)

### 4. Lazy Proof Construction

**Question:** Can we defer proof tree construction until needed?

**Idea:** Return proof "recipe" that can be replayed, not actual tree.

**Benefit:** Saves memory when only checking provability, not extracting proof.

### 5. Incremental Proof Maintenance

**Question:** When input changes slightly, can we reuse partial proofs?

**Relevance:** Important for interactive proving or reactive systems.

**Research:** Incremental computation, self-adjusting computation.

---

## Summary: Optimization Stack

| Layer | Technique | Complexity Improvement | Implementation Effort |
|-------|-----------|------------------------|----------------------|
| 1 | Hash consing (in plan) | O(n) → O(1) equality | MEDIUM |
| 2 | Context index by constructor | O(m) → O(c) identity | LOW |
| 3 | Memoization with subformula property | O(b^d) → O(n²) | MEDIUM |
| 4 | Near-linear unification | O(k²) → O(k·α(k)) | MEDIUM |
| 5 | Explicit substitutions | Deferred O(m·k·n) | HIGH |
| 6 | Persistent sequents | O(m) copy → O(log m) | LOW (use library) |
| 7 | Arena allocation | GC → O(1) bulk free | LOW (Zig), N/A (JS) |
| 8 | Term indexing (substitution trees) | O(c) → O(log m) | HIGH |
| 9 | Proof compression | Storage ÷ factor | MEDIUM |
| 10 | Parallel search | Time ÷ cores | HIGH |

**Recommended implementation order:**
1. **Phase 1:** Hash consing + Context index (biggest bang for buck)
2. **Phase 2:** Memoization (polynomial complexity)
3. **Phase 3:** Near-linear unification (if profiling shows mgu is bottleneck)
4. **Phase 4:** Explicit substitutions (if many unused substitutions)
5. **Future:** Term indexing, parallelism (only for very large scale)
