---
title: Primitives System Implementation
created: 2026-02-10
modified: 2026-02-11
summary: Implementation plan for lazy primitive storage (binlit) and type policies
tags: [primitives, storage, binlit, ffi, implementation]
status: complete
---

# Primitives System Implementation

## Executive Summary

Implement efficient primitive storage with minimal FFI:

1. **binlit/strlit**: Compact storage (implementation optimization)
2. **Unbounded FFI**: `plus`, `mul`, etc. operate on arbitrary BigInt
3. **Fixed-point FFI**: `fixed_mul`, `fixed_div` (genuinely different arithmetic)
4. **Type policies in logic**: `u32_wrap_plus`, `u256_checked_plus` defined as rules

**Key insight**: Types like `u32` vs `u256` are POLICIES (overflow behavior), not different types. The logic should express these policies explicitly, not hide them in FFI.

---

## Design Philosophy

### FFI is for Expensive Operations Only

FFI should only be used where pure logic would be prohibitively expensive:

| Operation | FFI? | Reason |
|-----------|------|--------|
| 256-bit addition | ✓ Yes | Proof search on 257-node tree is slow |
| Fixed-point multiply | ✓ Yes | Different arithmetic: `(a*b)/scale` |
| Boolean AND | ✗ No | 4 rules, trivial unification |
| Range checking | ✗ No | Single `lt` call, explicit in logic |

### Type = Storage + Policy

```
binlit(10n)  ← Storage (no inherent type)
     ↓
   plus      ← Unbounded FFI
     ↓
  policy     ← Logic-level: wrap? check? saturate?
```

The same `binlit(10n)` can be used as u32, u256, or unbounded bin. The POLICY determines overflow behavior, and policies belong in the logic where they're explicit and inspectable.

---

## Design Decisions

### Primitives as Storage Formats

| Format | Stores | Example |
|--------|--------|---------|
| `binlit` | BigInt | `Store.put('binlit', [10n])` |
| `strlit` | String | `Store.put('strlit', ['hello'])` |
| `charlit` | Code point | `Store.put('charlit', [97])` |
| atom | Bool | `atom('true')`, `atom('false')` |

**Note**: `binlit` stores the VALUE only. No type information.

### FFI: Minimal and Unbounded

Core FFI operates on unbounded BigInt:

```
plus A B C.    % C = A + B (arbitrary precision)
mul A B C.     % C = A * B
sub A B C.     % C = A - B (see open questions: negative numbers)
div A B C.     % C = A / B (truncating)
mod A B C.     % C = A mod B
lt A B.        % A < B
le A B.        % A <= B
eq A B.        % A = B
```

Fixed-point FFI (genuinely different arithmetic):

```
fixed_mul D A B C.   % C = (A * B) / 10^D
fixed_div D A B C.   % C = (A * 10^D) / B
```

### Type Policies in Logic

```
% Range bounds (constants)
u8_bound 256.
u32_bound 4294967296.
u256_bound 115792089237316195423570985008687907853269984665640564039457584007913129639936.

% Wrapping policy
wrap_plus Bound A B C :-
  plus A B Temp,
  mod Temp Bound C.

% Checked policy (fails on overflow)
checked_plus Bound A B C :-
  plus A B C,
  lt C Bound.

% Convenience predicates
u32w_plus A B C :- u32_bound M, wrap_plus M A B C.
u32c_plus A B C :- u32_bound M, checked_plus M A B C.
u256w_plus A B C :- u256_bound M, wrap_plus M A B C.
```

**Why this is better:**
- Policies are explicit and inspectable
- Easy to define new policies (saturating, trapping, etc.)
- Easy to define new types (just add bound constant)
- Two FFI calls per operation (measure if this matters)

### Booleans: Logic-Level

No FFI needed. An atom is 1 node.

```
true : bool.
false : bool.

and true true true.
and true false false.
and false true false.
and false false false.

or true X true.
or false X X.

not true false.
not false true.
```

---

## Implementation Phases

### Phase 1: binlit/strlit/charlit in Store (~30 lines)

**File:** `lib/v2/kernel/store.js`

```javascript
function hashBigInt(n) {
  if (n === 0n) return 0;
  const hex = n.toString(16);
  let h = hashString('bigint');
  for (let i = 0; i < hex.length; i += 8) {
    const chunk = hex.slice(i, Math.min(i + 8, hex.length));
    h = hashCombine(h, parseInt(chunk, 16) | 0);
  }
  return h;
}

function hashStr(s) {
  let h = hashString('str');
  for (let i = 0; i < s.length; i++) {
    h = hashCombine(h, s.charCodeAt(i));
  }
  return h;
}

// Modify computeHash to handle BigInt, String, and Number children
// binlit: children = [BigInt]
// strlit: children = [String]
// charlit: children = [Number] (code point)
function computeHash(tag, children) {
  let h = hashString(tag);
  h = hashCombine(h, children.length);
  for (const c of children) {
    if (typeof c === 'bigint') {
      h = hashCombine(h, hashBigInt(c));
    } else if (typeof c === 'number') {
      h = hashCombine(h, c);
    } else if (typeof c === 'string') {
      h = hashCombine(h, hashStr(c));
    }
  }
  return h;
}
```

### Phase 2: binlit in convert.js (~20 lines)

**File:** `lib/mde/ffi/convert.js`

```javascript
// O(1) storage
function intToBin(n) {
  return Store.put('binlit', [n]);
}

// Handles both binlit and expanded forms
function binToInt(h) {
  const node = Store.get(h);
  if (!node) return null;

  // Direct binlit - O(1)
  if (node.tag === 'binlit') {
    return node.children[0];
  }

  // Legacy: recursive form - O(log n)
  if (node.tag === 'atom' && node.children[0] === 'e') return 0n;
  if (node.tag === 'app') {
    const head = Store.get(node.children[0]);
    if (!head || head.tag !== 'atom') return null;
    const rest = binToInt(node.children[1]);
    if (rest === null) return null;
    if (head.children[0] === 'i') return rest * 2n + 1n;
    if (head.children[0] === 'o') return rest * 2n;
  }
  return null;
}

// String storage
function strToHash(s) {
  return Store.put('strlit', [s]);
}

function hashToStr(h) {
  const node = Store.get(h);
  if (!node || node.tag !== 'strlit') return null;
  return node.children[0];
}
```

### Phase 3: binlit in unify.js (~50 lines)

**File:** `lib/v2/kernel/unify.js`

```javascript
/**
 * Unify constructor pattern with binlit term (ephemeral expansion)
 *
 * binlit(10n) vs (o X) → X = binlit(5n)
 * binlit(0n) vs e → success
 * binlit(7n) vs (i X) → X = binlit(3n)
 */
function unifyBinlit(pattern, term, G, theta) {
  const termNode = Store.get(term);
  if (termNode.tag !== 'binlit') return false;
  const value = termNode.children[0];

  const patternNode = Store.get(pattern);

  // e (zero)
  if (patternNode.tag === 'atom' && patternNode.children[0] === 'e') {
    return value === 0n;
  }

  // app(o, X) or app(i, X)
  if (patternNode.tag === 'app') {
    const head = Store.get(patternNode.children[0]);
    if (!head || head.tag !== 'atom') return false;

    const bit = head.children[0];
    const tailPattern = patternNode.children[1];

    if (bit === 'o') {
      if (value === 0n || value % 2n !== 0n) return false;
      const tailValue = Store.put('binlit', [value / 2n]);
      G.push([tailPattern, tailValue]);
      return true;
    }

    if (bit === 'i') {
      if (value % 2n !== 1n) return false;
      const tailValue = Store.put('binlit', [value / 2n]);
      G.push([tailPattern, tailValue]);
      return true;
    }
  }

  // binlit vs binlit
  if (patternNode.tag === 'binlit') {
    return patternNode.children[0] === value;
  }

  return false;
}

/**
 * Unify constructor pattern with strlit term (ephemeral expansion)
 *
 * strlit("hello") vs cons(H, T) → H = charlit('h'), T = strlit("ello")
 * strlit("") vs nil → success
 * strlit("a") vs cons(H, nil) → H = charlit('a')
 */
function unifyStrlit(pattern, term, G, theta) {
  const termNode = Store.get(term);
  if (termNode.tag !== 'strlit') return false;
  const str = termNode.children[0];

  const patternNode = Store.get(pattern);

  // nil (empty string)
  if (patternNode.tag === 'atom' && patternNode.children[0] === 'nil') {
    return str === '';
  }

  // cons(H, T)
  if (patternNode.tag === 'app') {
    const head = Store.get(patternNode.children[0]);
    if (head && head.tag === 'app') {
      const consAtom = Store.get(head.children[0]);
      if (consAtom && consAtom.tag === 'atom' && consAtom.children[0] === 'cons') {
        if (str === '') return false;  // Can't destructure empty string
        const headPattern = head.children[1];  // H
        const tailPattern = patternNode.children[1];  // T
        const firstChar = Store.put('charlit', [str.charCodeAt(0)]);
        const restStr = Store.put('strlit', [str.slice(1)]);
        G.push([headPattern, firstChar]);
        G.push([tailPattern, restStr]);
        return true;
      }
    }
  }

  // strlit vs strlit
  if (patternNode.tag === 'strlit') {
    return patternNode.children[0] === str;
  }

  return false;
}

// In main unify loop, add cases:

// strlit: equality or ephemeral pattern matching
if (n0.tag === 'strlit' || n1.tag === 'strlit') {
  if (n0.tag === 'strlit' && n1.tag === 'strlit') {
    if (n0.children[0] !== n1.children[0]) return null;
    continue;
  }
  const [pat, lit] = n0.tag === 'strlit' ? [t1, t0] : [t0, t1];
  if (!unifyStrlit(pat, lit, G, theta)) return null;
  continue;
}

// binlit: equality or ephemeral pattern matching
if (n0.tag === 'binlit' || n1.tag === 'binlit') {
  if (n0.tag === 'binlit' && n1.tag === 'binlit') {
    if (n0.children[0] !== n1.children[0]) return null;
    continue;
  }
  const [pat, lit] = n0.tag === 'binlit' ? [t1, t0] : [t0, t1];
  if (!unifyBinlit(pat, lit, G, theta)) return null;
  continue;
}
```

### Phase 4: Fixed-Point FFI (~30 lines)

**File:** `lib/mde/ffi/arithmetic.js` (extend)

```javascript
// Fixed-point multiplication: C = (A * B) / 10^D
register('fixed_mul', (args) => {
  const [d, a, b, c] = args;
  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }
  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }
  const scale = 10n ** decimals;
  const result = (aInt * bInt) / scale;
  return { success: true, theta: [[c, intToBin(result)]] };
});

// Fixed-point division: C = (A * 10^D) / B
register('fixed_div', (args) => {
  const [d, a, b, c] = args;
  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }
  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }
  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }
  const scale = 10n ** decimals;
  const result = (aInt * scale) / bInt;
  return { success: true, theta: [[c, intToBin(result)]] };
});
```

### Phase 5: String FFI (~20 lines)

**File:** `lib/mde/ffi/arithmetic.js` (extend)

```javascript
register('string_concat', (args) => {
  const [a, b, c] = args;
  const aStr = hashToStr(a);
  const bStr = hashToStr(b);
  if (aStr === null || bStr === null) {
    return { success: false, reason: 'not_string' };
  }
  return { success: true, theta: [[c, strToHash(aStr + bStr)]] };
});

register('string_length', (args) => {
  const [s, len] = args;
  const str = hashToStr(s);
  if (str === null) {
    return { success: false, reason: 'not_string' };
  }
  return { success: true, theta: [[len, intToBin(BigInt(str.length))]] };
});
```

### Phase 6: Type Policies Prelude (~40 lines)

**File:** `calculus/prelude/types.mde` (new)

```
% === Type Bounds ===
u8_bound 256.
u16_bound 65536.
u32_bound 4294967296.
u64_bound 18446744073709551616.
u128_bound 340282366920938463463374607431768211456.
u256_bound 115792089237316195423570985008687907853269984665640564039457584007913129639936.

% === Generic Policies ===

% Wrapping: result = (a + b) mod bound
wrap_plus Bound A B C :-
  plus A B Temp,
  mod Temp Bound C.

wrap_mul Bound A B C :-
  mul A B Temp,
  mod Temp Bound C.

% Checked: fails if result >= bound
checked_plus Bound A B C :-
  plus A B C,
  lt C Bound.

checked_mul Bound A B C :-
  mul A B C,
  lt C Bound.

% === Convenience Predicates ===

u32w_plus A B C :- u32_bound M, wrap_plus M A B C.
u32c_plus A B C :- u32_bound M, checked_plus M A B C.
u256w_plus A B C :- u256_bound M, wrap_plus M A B C.
u256c_plus A B C :- u256_bound M, checked_plus M A B C.

% === Booleans ===
true : bool.
false : bool.

and true true true.
and true false false.
and false true false.
and false false false.

or true X true.
or false X X.

not true false.
not false true.
```

### Phase 7: Tests (~100 lines)

**File:** `tests/mde/primitives.test.js`

```javascript
describe('Primitive Storage', () => {
  describe('binlit', () => {
    it('stores numbers compactly', () => {
      Store.clear();
      const h = Store.put('binlit', [256n]);
      assert.strictEqual(Store.size(), 1);
    });

    it('deduplicates identical values', () => {
      const h1 = Store.put('binlit', [42n]);
      const h2 = Store.put('binlit', [42n]);
      assert.strictEqual(h1, h2);
    });
  });

  describe('strlit', () => {
    it('stores strings', () => {
      const h = Store.put('strlit', ['hello']);
      assert.strictEqual(Store.get(h).children[0], 'hello');
    });

    it('handles unicode', () => {
      const h = Store.put('strlit', ['hello 世界 🌍']);
      assert.strictEqual(Store.get(h).children[0], 'hello 世界 🌍');
    });
  });
});

describe('binlit Unification', () => {
  it('unifies binlit with e when zero', async () => {
    const zero = Store.put('binlit', [0n]);
    const e = await mde.parseExpr('e');
    const result = unify(e, zero);
    assert(result !== null);
  });

  it('unifies binlit with (o X) for even numbers', async () => {
    const ten = Store.put('binlit', [10n]);
    const oX = await mde.parseExpr('o X');
    const result = unify(oX, ten);
    assert(result !== null);
  });

  it('fails to unify binlit with (i X) for even numbers', async () => {
    const ten = Store.put('binlit', [10n]);
    const iX = await mde.parseExpr('i X');
    const result = unify(iX, ten);
    assert(result === null);
  });
});

describe('Type Policies', () => {
  it('u32 wrapping works', async () => {
    const calc = await loadTestCalc();
    // 4294967295 + 1 should wrap to 0
    const goal = await mde.parseExpr('u32w_plus 4294967295 1 X');
    const result = calc.prove(goal);
    assert(result.success);
    // X should be 0
  });

  it('u32 checked fails on overflow', async () => {
    const calc = await loadTestCalc();
    const goal = await mde.parseExpr('u32c_plus 4294967295 1 X');
    const result = calc.prove(goal);
    assert(!result.success);  // Should fail
  });

  it('unbounded plus has no overflow', async () => {
    const calc = await loadTestCalc();
    const goal = await mde.parseExpr('plus 4294967295 1 X');
    const result = calc.prove(goal);
    assert(result.success);
    // X should be 4294967296
  });
});

describe('Fixed-Point Arithmetic', () => {
  it('fixed18 multiplication scales correctly', async () => {
    const calc = await loadTestCalc();
    // 1.5 * 2.0 = 3.0 (with 18 decimals)
    // 1.5 = 1500000000000000000
    // 2.0 = 2000000000000000000
    // result = (1.5e18 * 2e18) / 1e18 = 3e18
    const goal = await mde.parseExpr(
      'fixed_mul 18 1500000000000000000 2000000000000000000 X'
    );
    const result = calc.prove(goal);
    assert(result.success);
  });
});

describe('Boolean Logic', () => {
  it('and works', async () => {
    const calc = await loadTestCalc();
    const goal = await mde.parseExpr('and true true X');
    const result = calc.prove(goal);
    assert(result.success);
  });

  it('not works', async () => {
    const calc = await loadTestCalc();
    const goal = await mde.parseExpr('not true X');
    const result = calc.prove(goal);
    assert(result.success);
  });
});

describe('strlit Unification', () => {
  it('unifies strlit with nil when empty', async () => {
    const empty = Store.put('strlit', ['']);
    const nil = await mde.parseExpr('nil');
    const result = unify(nil, empty);
    assert(result !== null);
  });

  it('unifies strlit with cons(H, T)', async () => {
    const hello = Store.put('strlit', ['hello']);
    const consHT = await mde.parseExpr('cons H T');
    const result = unify(consHT, hello);
    assert(result !== null);
    // H should be charlit('h'), T should be strlit("ello")
  });

  it('fails to unify empty strlit with cons', async () => {
    const empty = Store.put('strlit', ['']);
    const consHT = await mde.parseExpr('cons H T');
    const result = unify(consHT, empty);
    assert(result === null);
  });
});
```

### Phase 8: Benchmarks (~80 lines)

**File:** `tests/mde/primitives-benchmark.js`

```javascript
describe('Primitive Performance', function() {
  this.timeout(60000);

  it('binlit vs recursive storage', () => {
    const sizes = [8, 32, 64, 128, 256];
    const results = [];

    for (const bits of sizes) {
      const value = (1n << BigInt(bits)) - 1n;

      Store.clear();
      const t0 = performance.now();
      for (let i = 0; i < 1000; i++) {
        Store.put('binlit', [value - BigInt(i)]);
      }
      const binlitTime = performance.now() - t0;
      const binlitNodes = Store.size();

      Store.clear();
      const t1 = performance.now();
      for (let i = 0; i < 1000; i++) {
        intToBinRecursive(value - BigInt(i));
      }
      const recursiveTime = performance.now() - t1;
      const recursiveNodes = Store.size();

      results.push({
        bits,
        binlit: `${binlitTime.toFixed(1)}ms / ${binlitNodes} nodes`,
        recursive: `${recursiveTime.toFixed(1)}ms / ${recursiveNodes} nodes`,
        speedup: `${(recursiveTime / binlitTime).toFixed(1)}x`,
      });
    }

    console.table(results);
  });

  it('type policy overhead', async () => {
    const calc = await loadTestCalc();
    const iterations = 1000;

    // Unbounded (1 FFI call)
    const t0 = performance.now();
    for (let i = 0; i < iterations; i++) {
      calc.prove(await mde.parseExpr('plus 1000 1000 X'));
    }
    const unboundedTime = (performance.now() - t0) / iterations;

    // Wrapped (2 FFI calls: plus + mod)
    const t1 = performance.now();
    for (let i = 0; i < iterations; i++) {
      calc.prove(await mde.parseExpr('u32w_plus 1000 1000 X'));
    }
    const wrappedTime = (performance.now() - t1) / iterations;

    console.log(`Unbounded: ${unboundedTime.toFixed(3)}ms`);
    console.log(`Wrapped: ${wrappedTime.toFixed(3)}ms`);
    console.log(`Overhead: ${((wrappedTime / unboundedTime - 1) * 100).toFixed(0)}%`);
  });
});
```

---

## Files Summary

| File | Type | Lines |
|------|------|-------|
| `lib/v2/kernel/store.js` | Modify | ~30 |
| `lib/mde/ffi/convert.js` | Modify | ~20 |
| `lib/v2/kernel/unify.js` | Modify | ~100 |
| `lib/mde/ffi/arithmetic.js` | Extend | ~50 |
| `calculus/prelude/types.mde` | New | ~40 |
| `tests/mde/primitives.test.js` | New | ~140 |
| `tests/mde/primitives-benchmark.js` | New | ~80 |

**Total: ~460 lines**

---

## Decision Log

| Question | Decision | Rationale |
|----------|----------|-----------|
| Types in FFI vs logic? | Logic | Explicit, inspectable, extensible |
| Overflow policy? | Per-predicate | `u32w_plus` (wrap) vs `u32c_plus` (check) |
| Booleans? | Logic-level atoms | No performance gain from FFI |
| Fixed-point? | FFI | Genuinely different arithmetic |
| Negative numbers? | Fail (unprovable) | `sub 5 10 X` fails; matches linear logic (no negative resources) |
| Division by zero? | Fail (unprovable) | `div 10 0 X` fails; undefined operation |
| String matching? | Ephemeral expansion | `strlit("hello")` vs `cons(H, T)` → `H = charlit('h'), T = strlit("ello")` |
| charlit? | Keep | Distinguishes character semantics from integers |
| mask FFI? | Measure first | Add optimization only if benchmarks show overhead |

---

## References

- `lib/v2/kernel/store.js:34-44` — Current computeHash
- `lib/mde/ffi/convert.js:14-37` — Current binToInt/intToBin
- `lib/v2/kernel/unify.js:59-120` — Current unify
- `lib/mde/ffi/arithmetic.js` — Existing FFI operations
- Research: [[graded-resource-tracking]] — Object-level quantities
- Research: [[ffi-logics]] — FFI patterns
