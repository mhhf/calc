# Implementation Plan: MDE Parsing and Proving

**Goal:** Parse `.mde` files from `optimism-mde/lib/` and prove things about them.

**Date:** 2026-02-04

---

## Design Philosophy

### Unix / Suckless Principles

This implementation follows the Unix philosophy and suckless.org principles:

1. **Do one thing well.** Each module has a single responsibility.
2. **Small, composable tools.** Functions are pipelines, not monoliths.
3. **No unnecessary abstraction.** If a function can be 10 lines, don't make it 100.
4. **Code that fits in your head.** Any single file should be understandable in one sitting.
5. **Fail fast and loud.** No silent errors, no defensive programming that hides bugs.
6. **Text in, text out.** CLI tools work with stdin/stdout.

**Concrete guidelines:**
- No class hierarchies deeper than 1 level
- No getters/setters—use plain objects
- No frameworks, minimal dependencies
- Prefer `switch` over polymorphism
- Prefer functions over methods
- Maximum file size: ~300 lines

### Content-Addressed Architecture

**The formula IS its hash.** This is the core insight that enables O(1) operations:

```
┌─────────────────────────────────────────────────────────────────┐
│  WRONG: Copy data around                                        │
│    const formula = { tag: 'tensor', children: [A, B] }         │
│    const copy = JSON.parse(JSON.stringify(formula))  // O(n)   │
│    if (deepEqual(f1, f2)) ...                        // O(n)   │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│  RIGHT: Pass pointers (hashes)                                  │
│    const hash = Store.intern({ tag: 'tensor', children: [a, b] })│
│    const ref = hash                                  // O(1)   │
│    if (h1 === h2) ...                                // O(1)   │
└─────────────────────────────────────────────────────────────────┘
```

**Rules:**
- Never pass AST nodes, pass hashes (numbers)
- Never deep-copy, shallow-copy hash references
- Never compare structure, compare hashes
- Store.get() only when you need to inspect structure
- Multisets are `{ [hash]: count }` — O(1) add/remove/lookup

### Computational Complexity Requirements

Every operation must have documented complexity. Unacceptable patterns:

| Pattern | Problem | Fix |
|---------|---------|-----|
| `array.find()` in loop | O(n²) | Use Map/Set |
| `JSON.stringify` for equality | O(n) | Compare hashes |
| `[...array]` spread in recursion | O(n) allocation per call | Reuse, mutate-then-restore |
| `Object.keys().length` | O(n) allocation | `for..in` with early return |

**Target complexities:**
- Unification: O(n) where n = term size
- Rule matching: O(r × m) where r = rules, m = avg match attempts
- Forward step: O(1) amortized (hash lookups)
- State transition: O(k) where k = consumed + produced resources

---

## Executive Summary

Two components, minimal coupling:

1. **Parser Pipeline:** tree-sitter → hash (single pass, no intermediate AST)
2. **Hybrid Prover:** Backward (existing) + Forward (new multiset rewriter)

```
MDE file → tree-sitter → Store.intern() → hash
                              ↓
                    Prover works with hashes only
```

---

## Current State

| Component | Status | Complexity |
|-----------|--------|------------|
| tree-sitter grammar | ✅ Works | O(n) parse |
| Content-addressed Store | ✅ Works | O(1) intern/get |
| v2 backward prover | ✅ Works | O(2^n) worst case, focused pruning |
| Context multiset | ✅ Works | O(1) add/remove |

---

## Phase 1: MDE Parser Integration

### 1.1 Direct tree-sitter → Hash Conversion

**No intermediate AST.** Convert directly to content-addressed hashes.

**Location:** `lib/mde/convert.js` (~100 lines)

```javascript
/**
 * Convert tree-sitter node directly to content-addressed hash.
 * Single pass, no intermediate representation.
 *
 * Complexity: O(n) where n = AST node count
 *
 * @param {TreeSitterNode} node
 * @returns {number} hash
 */
function convert(node) {
  switch (node.type) {
    case 'expr_tensor':
      return Store.intern({
        tag: 'tensor',
        children: [convert(node.childForFieldName('left')),
                   convert(node.childForFieldName('right'))]
      });

    case 'expr_bang':
      return Store.intern({
        tag: 'bang',
        children: [convert(node.childForFieldName('inner'))]
      });

    case 'expr_atom':
      const text = node.text;
      if (text === 'type') return Store.intern({ tag: 'type', children: [] });
      if (/^[A-Z]/.test(text)) return Store.intern({ tag: 'freevar', children: [text] });
      return Store.intern({ tag: 'atom', children: [text] });

    case 'identifier':
      return Store.intern({ tag: 'atom', children: [node.text] });

    // ... 10 more cases, that's it
  }
}
```

**No MDEEnvironment class.** Just a plain object:

```javascript
/**
 * Load MDE file into registry.
 * Returns plain object, not class instance.
 *
 * @param {string} filePath
 * @returns {{ types: Map, clauses: Map, forwardRules: Array }}
 */
async function load(filePath) {
  const tree = await parse(filePath);
  const types = new Map();
  const clauses = new Map();
  const forwardRules = [];

  for (const decl of tree.rootNode.children) {
    if (decl.type !== 'declaration') continue;

    const name = decl.childForFieldName('name').text;
    const body = decl.childForFieldName('body');
    const exprNode = body.childForFieldName('expr');
    const hash = convert(exprNode);

    if (hasMonad(exprNode)) {
      forwardRules.push({ name, hash, antecedent: extractAntecedent(hash), consequent: extractConsequent(hash) });
    } else if (body.childForFieldName('premises')) {
      clauses.set(name, { hash, premises: convertPremises(body) });
    } else {
      types.set(name, hash);
    }
  }

  return { types, clauses, forwardRules };
}
```

### 1.2 Test: Conversion Preserves Structure

```javascript
// test/mde/convert.test.js
it('converts tensor to hash', () => {
  const tree = parse('A * B');
  const h = convert(tree.rootNode);

  // Verify by inspecting Store
  expect(Store.tag(h)).toBe('tensor');
  const [a, b] = Store.children(h);
  expect(Store.tag(a)).toBe('freevar');
  expect(Store.tag(b)).toBe('freevar');
});

it('deduplicates identical subterms', () => {
  const tree = parse('A * A');
  const h = convert(tree.rootNode);
  const [a1, a2] = Store.children(h);

  // Same hash = same pointer
  expect(a1).toBe(a2);  // O(1) check
});
```

---

## Phase 2: Lax Monad

### 2.1 Monad as Connective

Add to `calculus/ill.calc`:

```celf
monad: formula -> formula
  @ascii "{ _ }"
  @latex "\\{#1\\}"
  @prec 90
  @polarity positive.
```

That's it. One line of real content.

### 2.2 Mode Switch Rule

Add to `calculus/ill.rules`:

```celf
monad_r: deriv (seq G D (hyp any (monad A)))
  <- deriv_fwd (seq G D (hyp any A))
  @pretty "{}R"
  @mode_switch forward.
```

### 2.3 Prover Detects Monad

In `lib/v2/prover/focused/prover.js`, add ~20 lines:

```javascript
// In focused decomposition, check for monad
if (Store.tag(focusFormula) === 'monad') {
  const inner = Store.child(focusFormula, 0);
  const fwdState = { linear: delta, cartesian: Seq.getContext(seq, 'cartesian') };

  const fwdResult = runForward(fwdState, opts.forwardRules);
  if (!fwdResult.quiescent) return null;

  // Continue backward with result state
  return search(Seq.fromState(fwdResult.state, inner), inversion(), depth + 1, fwdResult.state.linear);
}
```

---

## Phase 3: Forward Chaining Engine

### 3.1 Minimal Multiset Rewriter

**Location:** `lib/v2/prover/forward.js` (~150 lines total)

```javascript
/**
 * Forward chaining state.
 * All formulas are hashes. Multiset is { hash: count }.
 *
 * @typedef {Object} FwdState
 * @property {Object.<number, number>} linear - Multiset of linear resources
 * @property {Object.<number, boolean>} cartesian - Set of persistent facts
 */

/**
 * Run forward chaining until quiescence.
 *
 * Complexity: O(s × r × m) where:
 *   s = number of steps until quiescence
 *   r = number of forward rules
 *   m = average match complexity per rule
 *
 * @param {FwdState} state
 * @param {Array} rules - Forward rules (precompiled)
 * @param {Object} opts - { maxSteps }
 * @returns {{ state: FwdState, quiescent: boolean, steps: number }}
 */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  let steps = 0;

  while (steps < maxSteps) {
    const match = findMatch(state, rules);
    if (!match) return { state, quiescent: true, steps };

    state = apply(state, match);
    steps++;
  }

  return { state, quiescent: false, steps };
}

/**
 * Find first matching rule.
 * Returns null if no rule matches (quiescence).
 *
 * Complexity: O(r × m) per call
 */
function findMatch(state, rules) {
  for (const rule of rules) {
    const theta = matchAntecedent(rule.antecedent, state);
    if (theta) return { rule, theta };
  }
  return null;
}

/**
 * Match antecedent against state.
 * Antecedent is a list of hashes (linear) and bang-wrapped hashes (persistent).
 *
 * Complexity: O(a) where a = antecedent size
 */
function matchAntecedent(antecedent, state) {
  const theta = [];
  const consumed = {};  // Track what we'd consume

  for (const h of antecedent.linear) {
    // Check if resource available (O(1) lookup)
    const available = (state.linear[h] || 0) - (consumed[h] || 0);
    if (available <= 0) {
      // Try unification with each resource
      const match = unifyWithState(h, state.linear, consumed, theta);
      if (!match) return null;
    } else {
      consumed[h] = (consumed[h] || 0) + 1;
    }
  }

  for (const h of antecedent.persistent) {
    // Persistent: just check existence (O(1))
    if (!state.cartesian[h]) {
      const match = unifyWithCartesian(h, state.cartesian, theta);
      if (!match) return null;
    }
  }

  return { theta, consumed };
}

/**
 * Apply rule: consume antecedent, produce consequent.
 * Returns NEW state (immutable style, but shallow copy is O(k)).
 *
 * Complexity: O(k) where k = |consumed| + |produced|
 */
function apply(state, { rule, theta }) {
  // Shallow copy multisets (O(1) for small changes via COW pattern)
  const linear = { ...state.linear };
  const cartesian = { ...state.cartesian };

  // Remove consumed (O(|consumed|))
  for (const h in theta.consumed) {
    linear[h] -= theta.consumed[h];
    if (linear[h] <= 0) delete linear[h];
  }

  // Add produced (O(|produced|))
  const produced = instantiate(rule.consequent, theta.theta);
  for (const h of produced.linear) {
    linear[h] = (linear[h] || 0) + 1;
  }
  for (const h of produced.persistent) {
    cartesian[h] = true;
  }

  return { linear, cartesian };
}
```

### 3.2 Rule Precompilation

Compile rules once at load time, not per-match:

```javascript
/**
 * Precompile forward rule for efficient matching.
 *
 * Input: hash of `A * B * !C -o { D * E }`
 * Output: { antecedent: { linear: [hA, hB], persistent: [hC] },
 *           consequent: { linear: [hD, hE], persistent: [] } }
 */
function compileRule(hash) {
  // Flatten tensor spine into list (O(rule size))
  const antecedent = { linear: [], persistent: [] };
  const consequent = { linear: [], persistent: [] };

  // Extract from `-o` structure
  const [ante, conseq] = splitLoli(hash);
  flattenTensor(ante, antecedent);
  flattenMonadBody(conseq, consequent);

  return { antecedent, consequent };
}

function flattenTensor(h, out) {
  if (Store.tag(h) === 'tensor') {
    flattenTensor(Store.child(h, 0), out);
    flattenTensor(Store.child(h, 1), out);
  } else if (Store.tag(h) === 'bang') {
    out.persistent.push(Store.child(h, 0));
  } else {
    out.linear.push(h);
  }
}
```

### 3.3 Complexity Analysis

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `findMatch` | O(r × a) | r rules, a avg antecedent |
| `matchAntecedent` | O(a) | a = antecedent atoms |
| `apply` | O(k) | k = consumed + produced |
| `run` (total) | O(s × r × a) | s steps to quiescence |

For EVM simulation with ~50 rules and ~10 atoms per antecedent:
- Per step: ~500 hash lookups (all O(1))
- Memory: Two objects with ~20 keys each

---

## Phase 4: Integration

### 4.1 Unified API

**Location:** `lib/mde/index.js` (~50 lines)

```javascript
const convert = require('./convert');
const forward = require('../v2/prover/forward');
const backward = require('../v2/prover');

/**
 * Load and prepare MDE calculus.
 */
async function load(filePath) {
  const { types, clauses, forwardRules } = await convert.load(filePath);

  // Precompile forward rules
  const compiled = forwardRules.map(r => ({
    ...r,
    ...forward.compileRule(r.hash)
  }));

  return {
    types,
    clauses,
    forwardRules: compiled,
    prove: (goal) => backward.prove(goal, { forwardRules: compiled }),
    exec: (state) => forward.run(state, compiled)
  };
}

module.exports = { load };
```

### 4.2 Test: bin.mde Arithmetic

```javascript
// test/mde/bin.test.js
const mde = require('../../lib/mde');

describe('bin.mde', () => {
  let calc;

  beforeAll(async () => {
    calc = await mde.load('~/src/optimism-mde/lib/bin.mde');
  });

  it('has correct types', () => {
    expect(calc.types.has('bin')).toBe(true);
    expect(calc.types.has('nat')).toBe(true);
  });

  it('proves plus/z1 (0+0=0)', () => {
    const goal = calc.parse('plus e e e');
    const result = calc.prove(goal);
    expect(result.success).toBe(true);
  });

  it('proves 1+1=2', () => {
    // 1 = i(e), 2 = o(i(e))
    const goal = calc.parse('plus (i e) (i e) ?X');
    const result = calc.prove(goal);
    expect(result.success).toBe(true);

    // Check substitution
    const X = result.theta.X;
    expect(Store.tag(X)).toBe('atom');  // 'o'
    expect(Store.tag(Store.child(X, 0))).toBe('atom');  // 'i'
  });
});
```

### 4.3 Test: EVM Forward Execution

```javascript
// test/mde/evm.test.js
describe('evm.mde forward', () => {
  let calc;

  beforeAll(async () => {
    // Load both bin.mde and evm.mde
    const bin = await mde.load('~/src/optimism-mde/lib/bin.mde');
    calc = await mde.load('~/src/optimism-mde/lib/evm.mde', { extend: bin });
  });

  it('executes STOP', () => {
    // Initial state: pc at 0, code[0] = STOP (0x00)
    const state = {
      linear: {
        [calc.parse('pc e')]: 1,
        [calc.parse('code e e')]: 1  // STOP opcode = 0x00
      },
      cartesian: {
        [calc.parse('inc e (i e)')]: true
      }
    };

    const result = calc.exec(state);

    expect(result.quiescent).toBe(true);
    expect(result.state.linear[calc.parse('stop')]).toBe(1);
    expect(result.steps).toBe(1);
  });
});
```

---

## Phase 5: CLI

### 5.1 Minimal CLI Tools

Following Unix philosophy: separate tools, composable via pipes.

**`libexec/calc-mde-parse`** (~30 lines)
```bash
#!/usr/bin/env node
// Parse MDE file, output hash registry as JSON
const mde = require('../lib/mde');
const file = process.argv[2];
mde.load(file).then(c => console.log(JSON.stringify({
  types: [...c.types],
  clauses: [...c.clauses].map(([k,v]) => [k, v.hash]),
  forwardRules: c.forwardRules.length
})));
```

**`libexec/calc-mde-query`** (~40 lines)
```bash
#!/usr/bin/env node
// Query (backward chaining)
const mde = require('../lib/mde');
const [file, query] = process.argv.slice(2);
mde.load(file).then(c => {
  const result = c.prove(c.parse(query));
  console.log(result.success ? 'PROVABLE' : 'NOT PROVABLE');
  if (result.success) console.log(JSON.stringify(result.theta));
});
```

**`libexec/calc-mde-exec`** (~40 lines)
```bash
#!/usr/bin/env node
// Execute (forward chaining)
const mde = require('../lib/mde');
const [file, stateFile] = process.argv.slice(2);
const state = JSON.parse(fs.readFileSync(stateFile));
mde.load(file).then(c => {
  const result = c.exec(state);
  console.log(`Quiescent: ${result.quiescent}`);
  console.log(`Steps: ${result.steps}`);
  console.log(JSON.stringify(result.state));
});
```

---

## File Structure

```
lib/
├── mde/
│   ├── index.js        # 50 lines - API
│   └── convert.js      # 100 lines - tree-sitter → hash
├── v2/
│   └── prover/
│       └── forward.js  # 150 lines - multiset rewriter

libexec/
├── calc-mde-parse      # 30 lines
├── calc-mde-query      # 40 lines
└── calc-mde-exec       # 40 lines

Total new code: ~400 lines
```

---

## Performance Targets

| Operation | Target | Rationale |
|-----------|--------|-----------|
| Load bin.mde | < 50ms | One-time cost |
| Parse formula | < 1ms | tree-sitter is fast |
| Backward proof (simple) | < 10ms | Focused pruning |
| Forward step | < 0.1ms | All O(1) lookups |
| EVM instruction | < 1ms | ~10 forward steps |

**Profiling checkpoints:**
- After Phase 1: `CALC_PROFILE=1 calc-mde-parse bin.mde`
- After Phase 3: `CALC_PROFILE=1 calc-mde-exec evm.mde state.json`

---

## Anti-Patterns to Avoid

| Don't | Do | Why |
|-------|-----|-----|
| `class MDEEnvironment` | Plain object `{ types, clauses }` | No need for encapsulation |
| `formula.clone()` | Pass hash | O(1) vs O(n) |
| `if (deepEqual(a, b))` | `if (a === b)` | O(1) vs O(n) |
| `state.linear.push(x)` | `state.linear[h]++` | O(1) vs O(n) amortized |
| `rules.filter().map()` | Single loop | One pass |
| `async/await` everywhere | Sync where possible | Avoid overhead |
| `try/catch` for control flow | Return null | Clearer intent |

---

## Success Criteria

1. **Phase 1:** bin.mde loads in < 50ms, types/clauses as plain Maps
2. **Phase 2:** Monad detection adds < 20 lines to prover
3. **Phase 3:** Forward engine is < 150 lines, O(1) per operation
4. **Phase 4:** `plus (i e) (i e) (o (i e))` proves in < 10ms
5. **Phase 5:** CLI tools are < 50 lines each

---

## Immediate Next Steps

1. Create `lib/mde/convert.js` with tensor test
2. Verify Store.intern deduplication works
3. Load bin.mde types into plain Map
4. Benchmark: target < 50ms load time
