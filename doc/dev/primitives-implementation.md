---
title: Primitives System Implementation
created: 2026-02-10
modified: 2026-02-11
summary: Implementation plan for @import, lazy primitive storage, and syntactic sugar
tags: [primitives, import, storage, sugar, ffi, implementation]
status: active
---

# Primitives System Implementation

Implementation plan for the primitives system: @import mechanism, lazy storage, and syntactic sugar.

## Overview

Three interconnected features:

| Feature | Purpose | Layer |
|---------|---------|-------|
| **@import** | Module system for primitives | Loader |
| **Lazy storage** | O(1) numeric storage with `binlit` | Store/Unify |
| **Syntactic sugar** | `@literal` and `@sugar` for ergonomics | Parser |

## 1. @import Mechanism

### Syntax

```
@import primitives.      % Built-in bin, nat, string
@import lnl.             % LNL family infrastructure
@import "./mymodule".    % Relative path
```

### Resolution Order

1. **Built-in modules** — `lib/calculus/foo.calc` or `lib/foo/`
2. **Project-local** — `./foo.calc` in same directory
3. **Explicit path** — if starts with `./` or `/`

### Primitives Module Structure

```
lib/primitives/
├── primitives.calc     # Declarative: types, constructors
├── bin.js              # JS: fromLiteral, match, ffi, render
├── nat.js
└── string.js
```

**Declarative part** (`primitives.calc`):
```
bin: type @primitive bigint.
e: bin @ascii "0".
i: bin -> bin @prec 90.
o: bin -> bin @prec 90.
@literal bin /[0-9]+/.
```

**JS part** (`bin.js`):
```javascript
module.exports = {
  name: 'bin',
  primitiveType: 'bigint',
  fromLiteral: (str) => BigInt(str),
  match: (value, pattern) => {
    if (pattern === 'e') return value === 0n ? {} : null;
    if (pattern === 'o') return value % 2n === 0n ? { tail: value / 2n } : null;
    if (pattern === 'i') return value % 2n === 1n ? { tail: value / 2n } : null;
    return null;
  },
  ffi: { plus: (a, b) => a + b, mul: (a, b) => a * b }
};
```

## 2. Lazy Primitive Storage

### Problem

Storing `10` as `o(i(o(i(o(e)))))` creates 5+ nodes. For 256-bit EVM words: 256 nodes.

### Solution

Single opaque node: `{ tag: 'binlit', children: [10n] }`

### Store Extension

```javascript
function hashBigInt(n) {
  const hex = n.toString(16);
  let h = 0;
  for (let i = 0; i < hex.length; i += 8) {
    h = hashCombine(h, parseInt(hex.slice(i, i + 8), 16) | 0);
  }
  return h;
}
```

### Ephemeral Pattern Matching

**Critical:** Pattern matching is ephemeral. No intermediate forms stored.

```
Input:   binlit(10n)
Pattern: o X

1. Check: 10 % 2 == 0 ✓
2. Compute: 10 / 2 = 5
3. Create: Store.intern('binlit', [5n])
4. Bind: X → binlit(5n)

No o(binlit(5n)) ever created!
```

### Unification

```javascript
function unifyWithBinlit(patternHash, termHash) {
  const term = Store.get(termHash);
  if (term.tag !== 'binlit') return null;
  const value = term.children[0];

  switch (Store.get(patternHash).tag) {
    case 'e': return value === 0n ? [] : null;
    case 'o':
      if (value % 2n !== 0n) return null;
      return unify(pattern.children[0], Store.intern('binlit', [value / 2n]));
    case 'i':
      if (value % 2n !== 1n) return null;
      return unify(pattern.children[0], Store.intern('binlit', [value / 2n]));
    case 'freevar':
      return [[patternHash, termHash]];
  }
}
```

## 3. Syntactic Sugar

### @literal — Lexer-level transformation

```
@literal bin /[0-9]+/.           % "123" → binlit(123n)
@literal bin /0x[0-9a-fA-F]+/.   % "0xff" → binlit(255n)
```

### @sugar — Parser-level transformation

```
graded: bin -> formula -> formula
  @ascii "[]_{ #1 } #2"
  @prec 85
  @sugar NUMBER formula.
```

Parsing `10 eth`:
1. Lexer: `10` → `binlit(10n)`
2. Parser: NUMBER followed by formula
3. Result: `graded(binlit(10n), atom(eth))`

## Implementation Phases

### Phase 1: @import Parsing
- [ ] Parse `@import` directives in `.calc` loader
- [ ] Implement module resolution (builtin, local, explicit)
- [ ] Handle circular import prevention
- [ ] Create primitive type registry

### Phase 2: Lazy Storage
- [ ] Add `hashBigInt()` function to store
- [ ] Update `computeHash()` for BigInt children
- [ ] Implement `unifyWithBinlit()`
- [ ] Test: `binlit(10n)` matches `o X` → `X = binlit(5n)`

### Phase 3: FFI Integration
- [ ] Modify FFI dispatch for `binlit` arguments
- [ ] Implement `ffiPlus`, `ffiMul` with BigInt
- [ ] Mode checking for inverse operations

### Phase 4: Syntactic Sugar
- [ ] Parse `@literal` annotations
- [ ] Parse `@sugar` annotations on constructors
- [ ] Integrate into lexer and parser
- [ ] Test: `10 eth` → `graded(binlit(10n), atom(eth))`

## Implementation Files

| File | Changes |
|------|---------|
| `lib/v2/calculus/index.js` | @import parsing, module loading |
| `lib/v2/kernel/store.js` | `hashBigInt()`, BigInt children |
| `lib/v2/kernel/unify.js` | `unifyWithBinlit()` |
| `lib/v2/parser/` | @literal, @sugar handling |
| `lib/primitives/` | New directory for bin.js, nat.js, etc. |

## References

- Research: [[graded-resource-tracking]] — Why object-level quantities
- Research: [[ffi-logics]] — FFI patterns, mode declarations
- Dev: [[dsl_refactor]] — DSL migration context
