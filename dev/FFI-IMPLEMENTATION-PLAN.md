# FFI Implementation Plan

**Date:** 2026-02-05
**Status:** Ready for implementation
**Priority:** HIGH

---

## Executive Summary

FFI (Foreign Function Interface) enables escaping proof search for computational predicates. This provides **~2x overall speedup** for EVM execution by replacing O(n) recursive clause applications with O(1) native arithmetic.

**Benchmark Motivation:**
| Operation | Current | With FFI | Speedup |
|-----------|---------|----------|---------|
| `plus 255 1` | 126.5µs | ~1µs | ~100x |
| Full EVM ADD | ~260µs | ~135µs | ~2x |

---

## Design (From Existing Research)

### Syntax

From `dev/dsl_refactor.md` and `dev/TODO.md`:

```celf
% In lib/arithmetic.mde or bin.mde
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus       % JS function path
  @mode + + -                % + = ground input, - = computed output
  @verify true               % optional: check result against axioms
  @fallback axioms.          % if mode doesn't match, use logical rules
```

**Annotation Schema:**

| Annotation | Type | Meaning |
|------------|------|---------|
| `@ffi` | string | JS function path (e.g., `arithmetic.plus`) |
| `@mode` | mode-spec | `+` = ground input, `-` = computed output |
| `@verify` | boolean | Check FFI result against axiom proof |
| `@fallback` | `axioms` | Use clause definitions if mode fails |

### Mode Specifications

Modes determine when FFI can be used:

```celf
% Addition: A + B = ?
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @mode + + -.

% Multiple modes (future extension):
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @modes [
    (+ + -),          % A + B = ? (addition)
    (+ - +),          % A + ? = C (subtraction: C - A)
    (- + +),          % ? + B = C (subtraction: C - B)
  ].
```

**Mode checking rules:**
- `+` argument MUST be ground (no metavariables)
- `-` argument SHOULD be a metavariable (will be unified with result)
- If mode check fails → fall back to clause definitions

---

## Implementation Plan

### Phase 1: Core Infrastructure

**Files to create:**

```
lib/mde/ffi/
├── index.js         # FFI registry and dispatch
├── arithmetic.js    # Built-in arithmetic operations
├── mode.js          # Mode checking utilities
└── convert.js       # bin ↔ BigInt conversion
```

#### 1.1 FFI Registry (`lib/mde/ffi/index.js`)

```javascript
/**
 * FFI Registry - maps function paths to implementations
 */
const registry = new Map();

/**
 * Register an FFI function
 * @param {string} path - Function path (e.g., "arithmetic.plus")
 * @param {Function} fn - Implementation
 */
function register(path, fn) {
  registry.set(path, fn);
}

/**
 * Get an FFI function
 * @param {string} path
 * @returns {Function|undefined}
 */
function get(path) {
  return registry.get(path);
}

/**
 * Check if FFI is available for a predicate
 * @param {string} path
 * @returns {boolean}
 */
function has(path) {
  return registry.has(path);
}

module.exports = { register, get, has, registry };
```

#### 1.2 Binary ↔ BigInt Conversion (`lib/mde/ffi/convert.js`)

```javascript
const Store = require('../../v2/kernel/store');

/**
 * Convert binary term to BigInt
 * Binary representation: e = 0, (i X) = 2*X + 1, (o X) = 2*X
 *
 * @param {number} h - Term hash
 * @returns {bigint|null} - null if not ground
 */
function binToInt(h) {
  const node = Store.get(h);
  if (!node) return null;

  if (node.tag === 'atom' && node.children[0] === 'e') {
    return 0n;
  }

  if (node.tag === 'app') {
    const headNode = Store.get(node.children[0]);
    if (!headNode || headNode.tag !== 'atom') return null;

    const bit = headNode.children[0];
    const rest = binToInt(node.children[1]);

    if (rest === null) return null;

    if (bit === 'i') return rest * 2n + 1n;
    if (bit === 'o') return rest * 2n;
  }

  // Not a valid binary term (e.g., contains metavar)
  return null;
}

/**
 * Convert BigInt to binary term hash
 *
 * @param {bigint} n - Non-negative integer
 * @returns {number} - Term hash
 */
function intToBin(n) {
  if (n === 0n) {
    return Store.intern('atom', ['e']);
  }

  const bit = n % 2n === 1n ? 'i' : 'o';
  const rest = intToBin(n / 2n);

  const bitAtom = Store.intern('atom', [bit]);
  return Store.intern('app', [bitAtom, rest]);
}

/**
 * Check if term is ground (no metavariables)
 *
 * @param {number} h - Term hash
 * @returns {boolean}
 */
function isGround(h) {
  const node = Store.get(h);
  if (!node) return false;

  if (node.tag === 'freevar') {
    const name = node.children[0];
    return !name.startsWith('_');  // Metavars start with _
  }

  if (node.tag === 'atom') return true;

  return node.children.every(c =>
    Store.isTermChild(c) ? isGround(c) : true
  );
}

module.exports = { binToInt, intToBin, isGround };
```

#### 1.3 Arithmetic Operations (`lib/mde/ffi/arithmetic.js`)

```javascript
const { binToInt, intToBin, isGround } = require('./convert');

/**
 * FFI for plus: A + B = C
 * Mode: + + -
 *
 * @param {number[]} args - [A, B, C] as term hashes
 * @returns {{ success: boolean, theta?: Array }} - Result
 */
function plus(args) {
  const [a, b, c] = args;

  // Mode check: A and B must be ground
  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  // Convert to integers
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  // Compute result
  const cInt = aInt + bInt;
  const cHash = intToBin(cInt);

  // Return substitution binding C to result
  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for inc: succ(A) = B
 * Mode: + -
 */
function inc(args) {
  const [a, b] = args;

  if (!isGround(a)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  if (aInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const bInt = aInt + 1n;
  const bHash = intToBin(bInt);

  return {
    success: true,
    theta: [[b, bHash]]
  };
}

/**
 * FFI for mul: A * B = C
 * Mode: + + -
 */
function mul(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt * bInt;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for sub: A - B = C (saturating at 0)
 * Mode: + + -
 */
function sub(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt >= bInt ? aInt - bInt : 0n;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for div: A / B = Q (integer division)
 * Mode: + + -
 */
function div(args) {
  const [a, b, q] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const qInt = aInt / bInt;
  const qHash = intToBin(qInt);

  return {
    success: true,
    theta: [[q, qHash]]
  };
}

/**
 * FFI for mod: A % B = R
 * Mode: + + -
 */
function mod(args) {
  const [a, b, r] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const rInt = aInt % bInt;
  const rHash = intToBin(rInt);

  return {
    success: true,
    theta: [[r, rHash]]
  };
}

/**
 * FFI for lt: A < B
 * Mode: + +
 * Returns success if true, failure if false
 */
function lt(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return {
    success: aInt < bInt,
    theta: []
  };
}

module.exports = { plus, inc, mul, sub, div, mod, lt };
```

#### 1.4 Mode Checking (`lib/mde/ffi/mode.js`)

```javascript
const { isGround } = require('./convert');

/**
 * Parse mode specification string
 * @param {string} modeStr - e.g., "+ + -"
 * @returns {Array<'+'|'-'>}
 */
function parseMode(modeStr) {
  return modeStr.trim().split(/\s+/);
}

/**
 * Check if arguments match mode specification
 * @param {number[]} args - Term hashes
 * @param {string} modeStr - Mode specification
 * @returns {boolean}
 */
function checkMode(args, modeStr) {
  const modes = parseMode(modeStr);

  if (args.length !== modes.length) {
    return false;
  }

  for (let i = 0; i < args.length; i++) {
    if (modes[i] === '+' && !isGround(args[i])) {
      return false;
    }
    // '-' mode: no constraint (will be unified with result)
  }

  return true;
}

module.exports = { parseMode, checkMode };
```

### Phase 2: Prover Integration

Modify `lib/mde/prove.js` to check FFI before clause search.

#### 2.1 FFI Dispatch in Backward Prover

```javascript
// In lib/mde/prove.js

const ffi = require('./ffi');

/**
 * Try FFI for a goal before clause search
 *
 * @param {number} goal - Goal term hash
 * @param {Object} ffiMeta - FFI metadata for predicates
 * @returns {{ success: boolean, theta?: Array }|null} - null if no FFI
 */
function tryFFI(goal, ffiMeta) {
  // Extract predicate name from goal
  const head = getHead(goal);
  if (!head) return null;

  // Check if predicate has FFI
  const meta = ffiMeta[head];
  if (!meta || !meta.ffi) return null;

  // Get arguments
  const args = getArgs(goal);

  // Check mode
  if (!ffi.mode.checkMode(args, meta.mode)) {
    return null;  // Mode mismatch → fall back to clauses
  }

  // Dispatch to FFI function
  const fn = ffi.get(meta.ffi);
  if (!fn) {
    console.warn(`FFI function not found: ${meta.ffi}`);
    return null;
  }

  const result = fn(args);

  // Optionally verify result against axioms
  if (meta.verify && result.success) {
    // TODO: Verify by proving goal with result substitution
  }

  return result;
}

/**
 * Modified search function with FFI support
 */
function search(goal, theta, depth, opts) {
  // ... existing depth check ...

  // TRY FFI FIRST
  if (opts.ffiMeta) {
    const ffiResult = tryFFI(subApply(goal, theta), opts.ffiMeta);
    if (ffiResult && ffiResult.success) {
      // Compose theta with FFI result
      return [...theta, ...ffiResult.theta];
    }
  }

  // ... existing clause search ...
}
```

#### 2.2 Loading FFI Metadata

Modify `lib/mde/index.js` to extract `@ffi` and `@mode` from declarations:

```javascript
/**
 * Extract FFI metadata from type declarations
 *
 * @param {Object} calc - Loaded calculus
 * @returns {Object} - { predicateName: { ffi, mode, verify } }
 */
function extractFFIMeta(calc) {
  const meta = {};

  for (const [name, decl] of calc.types) {
    const annotations = decl.annotations || [];

    const ffiAnnot = annotations.find(a => a.key === 'ffi');
    const modeAnnot = annotations.find(a => a.key === 'mode');

    if (ffiAnnot) {
      meta[name] = {
        ffi: ffiAnnot.value,
        mode: modeAnnot?.value || '+ '.repeat(decl.arity).trim() + ' -',
        verify: annotations.some(a => a.key === 'verify' && a.value === true)
      };
    }
  }

  return meta;
}
```

### Phase 3: Testing

#### 3.1 Unit Tests (`tests/mde/ffi.js`)

```javascript
const assert = require('assert');
const ffi = require('../../lib/mde/ffi');
const { binToInt, intToBin, isGround } = require('../../lib/mde/ffi/convert');
const Store = require('../../lib/v2/kernel/store');

describe('FFI Convert', () => {
  beforeEach(() => Store.clear());

  it('converts e to 0', () => {
    const e = Store.intern('atom', ['e']);
    assert.strictEqual(binToInt(e), 0n);
  });

  it('converts (i e) to 1', () => {
    const e = Store.intern('atom', ['e']);
    const i = Store.intern('atom', ['i']);
    const i_e = Store.intern('app', [i, e]);
    assert.strictEqual(binToInt(i_e), 1n);
  });

  it('converts 255 correctly', () => {
    const h = intToBin(255n);
    assert.strictEqual(binToInt(h), 255n);
  });

  it('round-trips large numbers', () => {
    for (const n of [0n, 1n, 127n, 255n, 256n, 1023n, 65535n]) {
      const h = intToBin(n);
      assert.strictEqual(binToInt(h), n, `Failed for ${n}`);
    }
  });

  it('detects non-ground terms', () => {
    const meta = Store.intern('freevar', ['_X']);
    assert.strictEqual(isGround(meta), false);

    const normal = Store.intern('freevar', ['X']);
    assert.strictEqual(isGround(normal), true);
  });
});

describe('FFI Arithmetic', () => {
  beforeEach(() => Store.clear());

  it('computes plus correctly', () => {
    const a = intToBin(255n);
    const b = intToBin(1n);
    const c = Store.intern('freevar', ['_C']);

    const result = ffi.arithmetic.plus([a, b, c]);

    assert(result.success);
    assert.strictEqual(result.theta.length, 1);
    assert.strictEqual(result.theta[0][0], c);
    assert.strictEqual(binToInt(result.theta[0][1]), 256n);
  });

  it('fails mode check for non-ground input', () => {
    const a = Store.intern('freevar', ['_A']);
    const b = intToBin(1n);
    const c = Store.intern('freevar', ['_C']);

    const result = ffi.arithmetic.plus([a, b, c]);

    assert(!result.success);
    assert.strictEqual(result.reason, 'mode_mismatch');
  });
});
```

#### 3.2 Integration Tests (`tests/mde/ffi-integration.js`)

```javascript
const assert = require('assert');
const mde = require('../../lib/mde');
const path = require('path');

describe('FFI Integration', () => {
  let calc;

  before(async () => {
    calc = await mde.load([
      path.join(__dirname, 'fixtures/bin.mde'),
    ]);
  });

  it('proves plus with FFI', async () => {
    const goal = await mde.parseExpr('plus (i (i (i (i (i (i (i (i e)))))))) (i e) C');
    // 255 + 1 = ?

    const t0 = performance.now();
    const result = calc.prove(goal, { useFFI: true });
    const ffiTime = performance.now() - t0;

    assert(result.success);
    // Verify result is 256 = o(o(o(o(o(o(o(o(i e))))))))

    // Compare with non-FFI
    const t1 = performance.now();
    const resultNoFFI = calc.prove(goal, { useFFI: false });
    const noFFITime = performance.now() - t1;

    console.log(`FFI: ${ffiTime.toFixed(2)}ms, No FFI: ${noFFITime.toFixed(2)}ms`);
    assert(ffiTime < noFFITime / 10, 'FFI should be 10x faster');
  });
});
```

### Phase 4: MDE File Syntax Support

#### 4.1 Grammar Extension (already supported)

From `dev/dsl_refactor.md`, the tree-sitter grammar already supports `@annotations`. We just need to handle `@ffi` and `@mode` in the converter.

#### 4.2 Example bin.mde with FFI

```celf
% lib/arithmetic.mde - Binary arithmetic with FFI

bin : type.
e : bin.
i : bin -> bin.
o : bin -> bin.

% Increment with FFI
inc : bin -> bin -> type
  @ffi arithmetic.inc
  @mode + -.

% Addition with FFI
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @mode + + -.

% Multiplication with FFI
mul : bin -> bin -> bin -> type
  @ffi arithmetic.mul
  @mode + + -.

% Subtraction with FFI (saturating)
sub : bin -> bin -> bin -> type
  @ffi arithmetic.sub
  @mode + + -.

% Division with FFI
div : bin -> bin -> bin -> type
  @ffi arithmetic.div
  @mode + + -.

% Modulo with FFI
mod : bin -> bin -> bin -> type
  @ffi arithmetic.mod
  @mode + + -.

% Less-than comparison
lt : bin -> bin -> type
  @ffi arithmetic.lt
  @mode + +.

% Axiom definitions (used when FFI mode doesn't match, or for verification)
inc/z : inc e (i e).
inc/i : inc (i X) (o Y) <- inc X Y.
inc/o : inc (o X) (i X).

plus/z1 : plus e e e.
plus/z2 : plus e (i N) (i N).
% ... etc
```

---

## File Structure

```
lib/mde/
├── ffi/
│   ├── index.js          # FFI registry
│   ├── arithmetic.js     # Built-in arithmetic
│   ├── mode.js           # Mode checking
│   └── convert.js        # bin ↔ BigInt conversion
├── prove.js              # Modified for FFI dispatch
└── index.js              # Modified to extract FFI metadata

tests/mde/
├── ffi.js                # FFI unit tests
├── ffi-integration.js    # FFI integration tests
└── ffi-benchmark.js      # Performance benchmarks
```

---

## Success Criteria

1. **Unit tests pass:** bin ↔ BigInt conversion, mode checking, arithmetic ops
2. **Integration tests pass:** Prove arithmetic goals with FFI
3. **Performance:** FFI path 10x+ faster than clause search for arithmetic
4. **Fallback works:** Non-ground goals fall back to clause definitions
5. **Syntax supported:** `@ffi` and `@mode` annotations parsed correctly

---

## Future Extensions

### Multiple Modes

```celf
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @modes [
    (+ + -),   % addition
    (+ - +),   % subtraction (C - A = B)
    (- + +),   % subtraction (C - B = A)
  ].
```

### Verification Mode

```celf
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @mode + + -
  @verify true.   % Double-check FFI result with axiom proof
```

### EVM-Specific Operations

```celf
sha3 : bin -> bin -> type
  @ffi evm.sha3
  @mode + -.

ecrecover : bin -> bin -> bin -> bin -> bin -> type
  @ffi evm.ecrecover
  @mode + + + + -.
```

---

## References

- `dev/dsl_refactor.md` - Phase 5: FFI Support
- `dev/TODO.md` - FFI predicates section
- `dev/research/ffi-logics.md` - Detailed FFI design research
- `dev/research/typed-dsl-logical-framework.md` - FFI in typed DSL context
- `dev/architecture-pipelines.md` - FFI hook points
- `dev/research/backward-prover-optimization.md` - Performance analysis showing arithmetic bottleneck
