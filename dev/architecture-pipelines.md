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
├── strategies/               # Pluggable proof search
│   ├── focused.js            # Andreoli's focusing (ILL)
│   └── generic.js            # Dumb exhaustive search (for verification)
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
