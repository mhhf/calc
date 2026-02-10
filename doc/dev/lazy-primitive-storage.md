# Lazy Primitive Storage

Implementation design for efficient storage of numeric types using lazy expansion.

---

## The Problem

Storing `10` as `o (i (o (i (o e))))` creates 5+ nodes in the Store:

```javascript
h1 = { tag: 'atom', children: ['e'] }
h2 = { tag: 'app', children: [o_hash, h1] }
h3 = { tag: 'app', children: [i_hash, h2] }
// ... 5 levels for 10, 256 levels for 256-bit numbers!
```

For EVM words (256-bit), this is **256 nodes per number**.

---

## Solution: Opaque Primitive Storage

Store numeric values as single opaque leaves:

```javascript
// Instead of 256-level tree:
{ tag: 'app', children: [i_hash, { tag: 'app', ... }] }

// Store as single node:
{ tag: 'binlit', children: [10n] }  // BigInt value
```

**Benefits:**
- O(1) storage per number
- O(1) FFI operations (direct BigInt arithmetic)
- Content-addressed (different values have different hashes)

---

## Store Extension

Extend `lib/v2/kernel/store.js` to handle BigInt children:

```javascript
function computeHash(tag, children) {
  let h = hashString(tag);
  h = hashCombine(h, children.length);
  for (const c of children) {
    if (typeof c === 'bigint') {
      h = hashCombine(h, hashBigInt(c));  // New: hash BigInt
    } else if (typeof c === 'number') {
      h = hashCombine(h, c);
    } else {
      h = hashCombine(h, hashString(String(c)));
    }
  }
  return h;
}

function hashBigInt(n) {
  // Hash BigInt by converting to hex string chunks
  const hex = n.toString(16);
  let h = 0;
  for (let i = 0; i < hex.length; i += 8) {
    h = hashCombine(h, parseInt(hex.slice(i, i + 8), 16) | 0);
  }
  return h;
}
```

---

## Ephemeral Expansion

**Critical insight:** Pattern matching is ephemeral. We never store intermediate forms.

### Pattern Match Example

```
Input:   binlit(10n)
Pattern: o X

1. Check: 10 % 2 == 0 ✓ (matches `o`)
2. Compute child value: 10 / 2 = 5
3. Create new binlit: Store.intern('binlit', [5n])
4. Bind: X → binlit(5n)

The `o` is NEVER stored. It's part of match logic, not result.
```

### What Gets Stored

```
Before match: binlit(10n)
After match:  binlit(5n)  ← New canonical form

No intermediate `o(binlit(5n))` ever created!
```

### Content-Addressing Preserved

| Structure | Hash | Notes |
|-----------|------|-------|
| `binlit(10n)` | h1 | Canonical for value 10 |
| `binlit(5n)` | h5 | Canonical for value 5 |
| `o(i(o(i(o(e)))))` | h2 | Legacy/render only, h1 ≠ h2 |
| `o(binlit(5n))` | — | **Never created** |

Different hashes for `binlit(10n)` vs expanded form is **correct** — they ARE different structures representing the same semantic value.

---

## Unification Integration

Modify `unify()` to detect `binlit` and handle pattern matching:

```javascript
function unifyWithBinlit(patternHash, termHash) {
  const pattern = Store.get(patternHash);
  const term = Store.get(termHash);

  if (term.tag !== 'binlit') return null;
  const value = term.children[0];  // BigInt

  switch (pattern.tag) {
    case 'e':
      return value === 0n ? [] : null;

    case 'o':
      if (value % 2n !== 0n) return null;
      const oChild = Store.intern('binlit', [value / 2n]);
      return unify(pattern.children[0], oChild);

    case 'i':
      if (value % 2n !== 1n) return null;
      const iChild = Store.intern('binlit', [value / 2n]);
      return unify(pattern.children[0], iChild);

    case 'freevar':
      // Variable matches binlit directly
      return [[patternHash, termHash]];

    default:
      return null;  // Pattern doesn't match binlit
  }
}
```

---

## FFI Integration

When both arguments are `binlit`, use FFI directly:

```javascript
function ffiPlus(aHash, bHash) {
  const a = Store.get(aHash);
  const b = Store.get(bHash);

  if (a.tag === 'binlit' && b.tag === 'binlit') {
    const result = a.children[0] + b.children[0];
    return Store.intern('binlit', [result]);
  }

  return null;  // Fall back to proof search
}
```

**No expansion needed!** FFI operates on BigInt directly.

---

## Rendering

Render `binlit` values in compact form by default:

```javascript
function renderBinlit(hash, options = {}) {
  const node = Store.get(hash);
  if (node.tag !== 'binlit') return null;

  const value = node.children[0];
  const format = options.format || 'compact';

  switch (format) {
    case 'compact':
      return value.toString();  // "10"
    case 'hex':
      return '0x' + value.toString(16);  // "0xa"
    case 'binary':
      return '0b' + value.toString(2);  // "0b1010"
    case 'expanded':
      return expandToStructure(value);  // "o (i (o (i (o e))))"
  }
}

function expandToStructure(value) {
  if (value === 0n) return 'e';
  const bit = value % 2n === 0n ? 'o' : 'i';
  return `${bit} (${expandToStructure(value / 2n)})`;
}
```

---

## Implementation Tasks

### Phase 1: Store Extension
- [ ] Add `hashBigInt()` function
- [ ] Update `computeHash()` to handle BigInt children
- [ ] Test: `Store.intern('binlit', [10n])` produces consistent hash

### Phase 2: Unification
- [ ] Add `unifyWithBinlit()` function
- [ ] Integrate into main `unify()` dispatch
- [ ] Test: `binlit(10n)` matches `o X` → `X = binlit(5n)`

### Phase 3: FFI
- [ ] Modify FFI dispatch to check for `binlit` arguments
- [ ] Implement `ffiPlus`, `ffiMul`, `ffiInc`, `ffiGt`
- [ ] Test: `plus binlit(10n) binlit(5n) X` → `X = binlit(15n)`

### Phase 4: Rendering
- [ ] Add `renderBinlit()` function
- [ ] Integrate into renderer with format options
- [ ] Test: render options (compact, hex, binary, expanded)

---

## Cross-References

- `dev/optimization_strategies.md` §8 — Original opaque storage concept
- `dev/research/explicit-substitutions.md` — Analogous lazy evaluation pattern
- `dev/research/graded-modalities.md` — Why object-level quantities need this
- `dev/research/ffi-logics.md` — FFI mode declarations

---

*Created: 2026-02-10*
