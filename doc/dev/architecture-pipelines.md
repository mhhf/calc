---
title: Clean Architecture Pipeline
created: 2026-02-10
modified: 2026-02-10
summary: Design for parallel v2 implementation separating core Gentzen machinery from calculus-specific optimizations
tags: [architecture, v2, pipelines, separation-of-concerns]
---

# Architecture: Clean Parallel Implementation

## Philosophy

Instead of backwards-compatible migration, build a **new minimal implementation** alongside the old:

1. **Suckless/Unix**: Small, focused modules with explicit dependencies
2. **No globals**: Pass calculus explicitly, no `Calc.db` singleton
3. **Trusted kernel**: Minimal core that just applies rules
4. **Pluggable strategies**: Proof search algorithms are separate
5. **Test against old**: Cross-check new vs old at each step
6. **Delete old when done**: Once new passes all tests, remove legacy

---

## Current Architecture (Legacy)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              LEGACY PIPELINE                            │
│                                                                         │
│   ll.json ──► Calc.init() ──► Calc.db (global singleton)               │
│                                    │                                    │
│              ┌─────────────────────┼─────────────────────┐              │
│              ▼                     ▼                     ▼              │
│        ┌──────────┐         ┌───────────┐         ┌──────────┐         │
│        │parser.js │         │ prover.js │         │ node.js  │         │
│        │ (Jison)  │         │proofstate │         │ (render) │         │
│        └──────────┘         └───────────┘         └──────────┘         │
│              │                     │                     │              │
│              └─────────────────────┴─────────────────────┘              │
│                          All use Calc.db.rules[id]                      │
└─────────────────────────────────────────────────────────────────────────┘
```

### Problems with Legacy
1. **Global state**: `Calc.db` is a singleton, can't have multiple calculi
2. **Integer IDs**: `node.id` is meaningless number, requires lookup
3. **Mixed concerns**: `Node` has rendering methods calling global `Calc.db`
4. **Jison unmaintained**: Poor errors, no tree-sitter benefits
5. **ll.json monolith**: 600 lines mixing grammar, rules, metadata

---

## New Architecture (lib/v2/)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              NEW PIPELINE (v2)                          │
│                                                                         │
│  .family/.calc/.rules ──► Calculus (explicit object, passed around)     │
│                                │                                        │
│         ┌──────────────────────┼──────────────────────┐                 │
│         ▼                      ▼                      ▼                 │
│   ┌───────────┐         ┌───────────┐         ┌───────────┐            │
│   │  parser   │         │  kernel   │         │  render   │            │
│   │(tree-sit.)│         │  (pure)   │         │  (pure)   │            │
│   └───────────┘         └───────────┘         └───────────┘            │
│         │                      │                      │                 │
│         │               ┌──────┴──────┐               │                 │
│         │               ▼             ▼               │                 │
│         │        ┌──────────┐  ┌───────────┐          │                 │
│         │        │ sequent  │  │strategies │          │                 │
│         │        │  (pure)  │  │ (focused) │          │                 │
│         │        └──────────┘  └───────────┘          │                 │
│         └──────────────────────┴──────────────────────┘                 │
│                    No globals, explicit dependencies                    │
└─────────────────────────────────────────────────────────────────────────┘
```

### Directory Structure

```
lib/v2/
├── spec/                     # Calculus specification layer
│   ├── parser.js             # Tree-sitter parser for .family/.calc/.rules
│   └── calculus.js           # Calculus object {connectives, rules, meta}
│
├── syntax/                   # Formula/sequent syntax
│   ├── parser.js             # Tree-sitter formula parser (generated from spec)
│   ├── ast.js                # Pure AST: {tag, children} (no methods!)
│   └── render.js             # render(ast, format, calculus) → string
│
├── kernel/                   # Trusted kernel (minimal!)
│   ├── sequent.js            # Sequent: {contexts, succedent}
│   ├── unify.js              # MGU (pure function)
│   ├── substitute.js         # Substitution (pure function)
│   └── apply.js              # applyRule(sequent, rule, position) → premises
│
├── provers/                  # Proof search strategies
│   ├── registry.js           # Prover registry (list, select provers)
│   ├── prover.js             # Base Prover interface
│   ├── generic.js            # Generic prover (any calculus, slow)
│   └── focused.js            # ILL-specific (focusing, lazy splitting)
│
├── ffi/                      # Foreign Function Interface
│   └── registry.js           # FFI for computational predicates
│
└── index.js                  # Main API
```

### Key Design Principles

**1. AST is pure data (no methods)**
```javascript
// OLD: Node class with methods calling globals
class Node {
  toString() { return Calc.db.rules[this.id]... }
}

// NEW: Pure data + separate render function
const ast = { tag: 'tensor', children: [a, b] };
const str = render(ast, 'ascii', calculus);
```

**2. No global state**
```javascript
// OLD: Global singleton
Calc.init(json);
const type = Calc.db.rules[node.id];

// NEW: Explicit parameter
const calculus = loadCalculus('./calculus/ill.calc', './calculus/ill.rules');
const type = calculus.getType(ast.tag);
```

**3. Kernel is minimal**
```javascript
// kernel/apply.js - just applies rules, no search strategy
function applyRule(sequent, rule, position, calculus) {
  const theta = unify(rule.conclusion, sequent, position);
  if (!theta) return null;
  const premises = rule.premises.map(p => substitute(p, theta));
  return { premises, theta };
}
```

**4. Strategies are pluggable**
```javascript
// strategies/focused.js
class FocusedProver {
  constructor(calculus) { this.calculus = calculus; }
  prove(sequent) { /* Andreoli focusing */ }
}

// strategies/generic.js
class GenericProver {
  constructor(calculus) { this.calculus = calculus; }
  prove(sequent) { /* Dumb exhaustive search */ }
}
```

---

## Implementation Phases

### Phase 1: Formula Parser (tree-sitter)
**Goal**: Parse formulas/sequents using tree-sitter, output clean AST.

**Tasks**:
- [ ] Create formula grammar from calculus spec (not Jison!)
- [ ] Parser outputs `{tag, children}` AST (pure data)
- [ ] Test: parse old test cases, compare structure

**Cross-check**: Parse same strings with old parser, compare AST shape.

**Files**:
```
lib/v2/syntax/parser.js      # Tree-sitter formula parser
lib/v2/syntax/ast.js         # AST type definitions
tests/v2/parser.test.js      # Parser tests + cross-check
```

### Phase 2: Renderer
**Goal**: Render AST to ascii/latex without calling globals.

**Tasks**:
- [ ] `render(ast, format, calculus)` pure function
- [ ] Support ascii, latex, isabelle
- [ ] Handle precedence/brackets correctly

**Cross-check**: Render same formulas, compare output strings.

**Files**:
```
lib/v2/syntax/render.js      # Pure render function
tests/v2/render.test.js      # Render tests + cross-check
```

### Phase 3: Sequent
**Goal**: Clean sequent representation (no global Calc).

**Tasks**:
- [ ] Sequent class with explicit contexts
- [ ] Content-addressed hashing (keep optimization)
- [ ] No dependency on global state

**Cross-check**: Create same sequents, compare structure.

**Files**:
```
lib/v2/kernel/sequent.js     # Sequent class
tests/v2/sequent.test.js     # Tests + cross-check
```

### Phase 4: Kernel (Rule Application)
**Goal**: Minimal trusted kernel - just applies rules.

**Tasks**:
- [ ] `unify(pattern, term)` - MGU
- [ ] `substitute(term, theta)` - apply substitution
- [ ] `applyRule(sequent, rule, position)` - single rule application
- [ ] Load rules from .rules files

**Cross-check**: Apply same rules to same sequents, compare results.

**Files**:
```
lib/v2/kernel/unify.js       # MGU
lib/v2/kernel/substitute.js  # Substitution
lib/v2/kernel/apply.js       # Rule application
tests/v2/kernel.test.js      # Tests + cross-check
```

### Phase 5: Focused Prover (Strategy)
**Goal**: Port focused proof search as pluggable strategy.

**Tasks**:
- [ ] `FocusedProver` class implementing Andreoli focusing
- [ ] Polarity inference from rule structure
- [ ] Inversion phase, focus phase, identity rules

**Cross-check**: Prove same theorems, compare proof trees.

**Files**:
```
lib/v2/strategies/focused.js  # Focused prover
tests/v2/prover.test.js       # Theorem tests + cross-check
```

### Phase 6: Generic Prover (Verification)
**Goal**: Dumb exhaustive prover for verifying focused prover.

**Tasks**:
- [ ] `GenericProver` - tries all rules exhaustively
- [ ] Loop detection (visited states)
- [ ] Can verify proof trees from focused prover

**Cross-check**: Both provers find proofs for same theorems.

**Files**:
```
lib/v2/strategies/generic.js  # Generic prover
tests/v2/verify.test.js       # Cross-verification tests
```

### Phase 7: Integration
**Goal**: Wire up CLI tools to new implementation.

**Tasks**:
- [ ] Create `lib/v2/index.js` unified API
- [ ] Update CLI tools with `--v2` flag
- [ ] Run full test suite with both implementations
- [ ] Compare all outputs

**Files**:
```
lib/v2/index.js              # Main API
libexec/calc-parse           # Add --v2 flag
libexec/calc-proof           # Add --v2 flag
```

### Phase 8: Cleanup
**Goal**: Remove legacy code once new is proven correct.

**Tasks**:
- [ ] Verify 100% test coverage with v2
- [ ] Remove ll.json
- [ ] Remove lib/calc.js, lib/parser.js (old Jison)
- [ ] Move lib/v2/* to lib/*
- [ ] Update all imports

---

## Cross-Check Strategy

At each phase, run parallel tests:

```javascript
// tests/v2/parser.test.js
describe('parser cross-check', () => {
  const testCases = ['A * B', 'A -o B', '!A', ...];

  for (const input of testCases) {
    it(`parses "${input}" same as legacy`, () => {
      const legacyAst = legacyParser.parse(input);
      const newAst = newParser.parse(input);

      // Compare structure (may need normalization)
      expect(normalizeAst(newAst)).toEqual(normalizeAst(legacyAst));
    });
  }
});
```

---

## Calculus Object (v2)

```javascript
// lib/v2/spec/calculus.js
class Calculus {
  constructor(spec) {
    this.connectives = spec.connectives;  // {tensor: {arity: 2, ascii: '_ * _', ...}}
    this.rules = spec.rules;              // {Tensor_L: {conclusion, premises}, ...}
    this.meta = spec.meta;                // {polarity, precedence, ...}
  }

  // Load from DSL files
  static async load(calcPath, rulesPath) {
    const parser = require('./parser');
    const calcAst = await parser.parseFile(calcPath);
    const rulesAst = await parser.parseFile(rulesPath);
    return new Calculus(extractSpec(calcAst, rulesAst));
  }

  getConnective(tag) { return this.connectives[tag]; }
  getRule(name) { return this.rules[name]; }
  getPolarity(tag) { return this.meta.polarity[tag]; }
}
```

---

## Prover Architecture

### Pluggable Provers per Calculus
```
┌─────────────────────────────────────────────────────────────────┐
│                    PROVER REGISTRY                               │
│                                                                 │
│  For a given calculus (e.g. ILL), multiple provers available:   │
│                                                                 │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐   │
│  │   generic   │ │   focused   │ │   tableaux  │ │  future │   │
│  │  (default)  │ │ (ILL-opt)   │ │  (future)   │ │   ...   │   │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘   │
│        ↑               ↑               ↑              ↑         │
│        └───────────────┴───────────────┴──────────────┘         │
│                     User/CLI chooses                            │
└─────────────────────────────────────────────────────────────────┘
```

### Prover Interface
```javascript
// All provers implement this interface
class Prover {
  constructor(calculus, store, options) { }

  // Returns { success, proofTree, theta, ... }
  prove(sequent) { throw new Error('implement me'); }

  // Metadata
  static get name() { return 'generic'; }
  static get description() { return 'Exhaustive search'; }
  static supports(calculus) { return true; }  // Which calculi this prover works with
}
```

### Prover Registry
```javascript
// lib/v2/provers/registry.js
class ProverRegistry {
  constructor() {
    this.provers = new Map();  // name → ProverClass
  }

  register(ProverClass) {
    this.provers.set(ProverClass.name, ProverClass);
  }

  get(name) {
    return this.provers.get(name);
  }

  listFor(calculus) {
    // Return all provers that support this calculus
    return [...this.provers.values()]
      .filter(P => P.supports(calculus));
  }
}

// Default registry
const registry = new ProverRegistry();
registry.register(GenericProver);
registry.register(FocusedProver);
// Future: registry.register(TableauxProver);
// Future: registry.register(ResolutionProver);
```

### CLI Usage
```bash
calc proof "A -o A" --prover=generic    # Use generic (slow)
calc proof "A -o A" --prover=focused    # Use focused (fast, ILL)
calc proof "A -o A"                     # Use default for calculus
```

### Built-in Provers
| Prover | Supports | Strategy |
|--------|----------|----------|
| `generic` | Any calculus | Exhaustive rule enumeration, loop detection |
| `focused` | ILL | Andreoli focusing, lazy splitting (delta_in/out) |

### Future Provers (examples)
| Prover | Supports | Strategy |
|--------|----------|----------|
| `tableaux` | Classical, ILL | Tableau method |
| `resolution` | Classical | Resolution refutation |
| `inverse` | ILL | Inverse method (bottom-up) |

### Lazy Resource Management (ILL-Specific)

The `delta_in/delta_out` pattern is **ILL-specific** and lives in `FocusedProver`, not the generic kernel. The generic prover enumerates splits explicitly.

---

## FFI Architecture (Computational Predicates)

From `dev/TODO.md`: FFI escapes proof search for computation.

```celf
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus    % JS function
  @mode + + -             % input input output
  @verify true            % check result
  @fallback axioms.       % if mode doesn't match
```

### FFI in v2
```javascript
// lib/v2/ffi/registry.js
class FFIRegistry {
  constructor() {
    this.functions = new Map();  // predicate → JS function
  }

  register(predicate, fn, options) {
    this.functions.set(predicate, {
      fn,
      mode: options.mode,      // ['+', '+', '-'] = inputs, output
      verify: options.verify,
      fallback: options.fallback
    });
  }

  call(predicate, args) {
    const ffi = this.functions.get(predicate);
    if (!ffi) return null;

    // Check mode: are inputs ground?
    const inputs = args.filter((_, i) => ffi.mode[i] === '+');
    if (!inputs.every(isGround)) {
      return ffi.fallback ? 'use_fallback' : null;
    }

    // Call JS function
    const result = ffi.fn(...inputs);

    // Optionally verify
    if (ffi.verify) {
      // Check result matches expected output
    }

    return result;
  }
}
```

### FFI Phase (add to Phase 4.5)
- [ ] FFI registry for computational predicates
- [ ] Mode checking (+/- for input/output)
- [ ] Integration with proof search
- [ ] Fallback to axioms when mode doesn't match

---

## Lazy Resource Management (FocusedProver Only)

From `dev/research/proof-search-oracles.md`: Context splitting is **discovered during proof**, not guessed upfront.

### delta_in / delta_out Pattern
```javascript
// Instead of 2^n context splits:
// delta_in = all available resources
// Prove first premise with ALL resources
// delta_out = leftover resources
// delta_out becomes delta_in for next premise

function proveMultiplicative(premises, delta_in, store) {
  let delta = delta_in;

  for (const premise of premises) {
    const result = prove(premise, delta, store);
    if (!result.success) return { success: false };
    delta = result.delta_out;  // Leftover becomes input for next
  }

  return { success: true, delta_out: delta };
}
```

### Split vs Copy (propagate flag)
| Connective | Mode | Behavior |
|------------|------|----------|
| `Tensor_R` | split | First premise gets all, leftover to second |
| `Loli_L` | split | Same |
| `With_R` | copy | Both premises get full context (additive) |

---

## Profiling Infrastructure

Use `CALC_PROFILE=1` to identify bottlenecks before optimizing.

### v2 Profiling Hooks
```javascript
const { profiler } = require('./profiler');

function unify(a, b, store) {
  profiler.count('unify.calls');
  profiler.time('unify.time', () => {
    // ... actual unification
  });
}
```

### Hot Path (from dev/research/benchmarking.md)
| Rank | Operation | Frequency | Per-call Cost |
|------|-----------|-----------|---------------|
| 1 | `mgu()` | Every rule application | O(n²) → O(n) with interning |
| 2 | `toString()` | Every equality check | O(n) → O(1) with hashing |
| 3 | `substitute()` | k times per mgu | O(n) |
| 4 | `sha3(toString())` | Every context add | O(n) → O(1) with interning |

---

## Deferred Optimizations (from dev/optimization_strategies.md)

| Optimization | When to Implement | Trigger |
|--------------|-------------------|---------|
| Constructor Index | If identity lookup is bottleneck | CALC_PROFILE shows tryIdPos hot |
| Proof Memoization | If proof search repeats subgoals | Large proofs with sharing |
| Near-Linear Unification | If unification is bottleneck | Martelli-Montanari |
| Explicit Substitutions | If many unused substitutions | Lazy evaluation |

### Proof Memoization (Subformula Property)
```javascript
class ProofMemo {
  constructor() {
    this.cache = new Map();  // sequentHash → ProofResult
  }

  key(seq) {
    // Canonical key: sorted context hashes + succedent hash
    return hashCombine(...sortedContextHashes, succedentHash);
  }

  lookup(seq) {
    return this.cache.get(this.key(seq));
  }

  store(seq, result) {
    this.cache.set(this.key(seq), result);
  }
}
```

**Why it works**: Cut-free proofs have subformula property. If input has n subformulas, at most O(n²) unique sequents. With memoization: O(n²) instead of O(b^d).

---

## Existing lib/* Files to Reuse

These files are well-designed and should be reused in v2 with minimal changes:

| File | Purpose | v2 Change |
|------|---------|-----------|
| `lib/store.js` | Content-addressed store | Pass explicitly, not `getStore()` |
| `lib/term.js` | Term wrapper around hash | Keep as-is |
| `lib/hash.js` | FNV-1a 64-bit hashing | Keep as-is (Zig-portable) |
| `lib/intern.js` | Node ↔ Term conversion | Update for new AST format |
| `lib/profiler.js` | CALC_PROFILE support | Keep as-is |

### Files to Replace
| File | Legacy | v2 Replacement |
|------|--------|----------------|
| `lib/parser.js` | Jison generator | Tree-sitter |
| `lib/node.js` | Class with methods | Pure data + render() |
| `lib/calc.js` | Global Calc.db | Explicit Calculus object |
| `lib/sequent.js` | Uses ll.json | Uses Calculus |
| `lib/proofstate.js` | Monolithic | Split: kernel + strategies |
| `lib/prover.js` | Mixed concerns | strategies/focused.js |

---

## Content-Addressed Store (MUST KEEP)

The existing `lib/store.js`, `lib/hash.js`, `lib/intern.js` are well-designed. v2 MUST use them:

### What We Have (lib/store.js)
```javascript
class Store {
  internString(str)                    // hash → store
  internStruct(constructorId, children) // hash → store
  equal(hash1, hash2)                  // O(1) equality
}

class ScopedStore {
  fork()     // Create child scope for proof branch
  commit()   // Merge local to parent (proof succeeded)
  discard()  // Drop local allocations (backtrack)
}
```

### v2 Changes
1. **Pass store explicitly** (not `getStore()` global singleton)
2. **String tags → integer IDs** internally for efficiency, but API uses strings
3. **Keep scoped stores** for backtracking in proof search

```javascript
// v2 usage
const store = new Store();
const calculus = await Calculus.load(calcPath, rulesPath, store);
const prover = new FocusedProver(calculus, store);

// Proof search uses scoped stores
const branchStore = store.fork();
const result = prover.prove(sequent, branchStore);
if (result.success) branchStore.commit();
else branchStore.discard();
```

---

## Zig Portability (DESIGN CONSTRAINT)

v2 is designed for eventual Zig port. All core data structures must be Zig-portable:

### Portable Patterns
| Pattern | JS | Zig |
|---------|----|----|
| Integer IDs | `number` | `u32` |
| Hash | `BigInt` (64-bit) | `u64` |
| Array of children | `[]` | `[]u32` |
| String interning | `Map<hash, string>` | `HashMap(u64, []const u8)` |
| Arena allocation | `ScopedStore` | `std.heap.ArenaAllocator` |

### Non-Portable (avoid in kernel)
- `WeakRef` / `FinalizationRegistry`
- Complex object graphs
- Closures capturing state
- `Map` with object keys

### AST Representation (Zig-friendly)
```javascript
// v2 AST - flat, index-based (like lib/term.js)
{
  tag: 'tensor',           // String for API
  tagId: 7,                // Integer for storage (maps to Zig enum)
  children: [hash1, hash2] // Hashes, not object refs
}

// In Zig:
const Node = struct {
    tag: u16,              // Enum index
    arity: u8,
    children: [4]u64,      // Child hashes (max 4)
};
```

### Hash Function (FNV-1a, already portable)
```javascript
// lib/hash.js - already Zig-portable
const FNV_PRIME = 0x100000001b3n;
const FNV_OFFSET = 0xcbf29ce484222325n;

// Same algorithm in Zig:
// const fnv_prime: u64 = 0x100000001b3;
// const fnv_offset: u64 = 0xcbf29ce484222325;
```

---

## Summary

| Aspect | Legacy | v2 |
|--------|--------|-----|
| State | Global `Calc.db` | Explicit `Calculus` + `Store` |
| AST | `Node` class with methods | Pure data `{tag, tagId, children}` |
| Render | `node.toString()` | `render(ast, format, calc)` |
| Parser | Jison (unmaintained) | tree-sitter (Zig bindings) |
| Kernel | Mixed with strategy | Minimal `applyRule` |
| Strategy | Hardcoded in prover | Pluggable classes |
| IDs | Integer only | String API, integer storage |
| Store | Global singleton | Explicit, passed as param |
| Backtrack | Manual cleanup | `ScopedStore.fork/commit/discard` |
| Zig-ready | No | Yes (portable patterns) |

The old code stays working throughout. Only delete it after v2 passes 100% of tests.

---

## Open Questions / Decisions Needed

### 1. Mutable Proof Trees (like v1)
Keep mutable style from v1 - it works and we understand it. ScopedStore handles backtracking for the store; proof tree mutation is fine.

### 2. AST Representation
**Option A**: Object-based `{tag, children: [child, child]}` - easy to use in JS
**Option B**: Hash-based `{tag, tagId, childHashes: [hash, hash]}` - flat, Zig-portable
**Recommendation**: Use object-based for API, hash-based for storage. Convert at boundary.

### 3. Rule Loading
**Option A**: Load at startup (like ll.json) - simple
**Option B**: Lazy load on demand - faster startup
**Option C**: Build step generates optimized format - best performance
**Recommendation**: Start with (A), optimize later.

### 4. Error Handling
**Option A**: Return `{success: false, error}` - functional style
**Option B**: Throw exceptions - JS-idiomatic
**Recommendation**: Use return values in kernel (portable), exceptions at API boundary.

### 5. When to Implement Optimizations
| Optimization | Immediate | After basic v2 | When real-world testing |
|--------------|-----------|----------------|-------------------------|
| Content-addressing | ✓ | | |
| ScopedStore | ✓ | | |
| delta_in/out (FocusedProver) | ✓ | | |
| FFI for computation | ✓ | | |
| Proof memoization | | | ✓ |
| Constructor index | | | ✓ |
| Explicit substitutions | | | ✓ |

---

## References

- `dev/research/proof-search-oracles.md` - Oracle architecture, trust levels
- `dev/research/content-addressed-formulas.md` - Hash consing, Merkle-DAG
- `dev/research/benchmarking.md` - Hot path analysis, complexity
- `dev/optimization_strategies.md` - Deferred optimizations
- `dev/REFACTOR.md` - Legacy code analysis
- `dev/research/typed-dsl-logical-framework.md` - DSL design
