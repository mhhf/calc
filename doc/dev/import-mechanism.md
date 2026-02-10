---
title: Import Mechanism Design
created: 2026-02-10
modified: 2026-02-10
summary: Module system implementation for @import directives including built-in primitives and resolution order
tags: [import, modules, primitives, resolution]
---

# @import Mechanism

Implementation design for module system in `.calc` files.

---

## Syntax

```
@import <module>.
```

### Examples

```
@import primitives.      % Built-in bin, nat, string, etc.
@import lnl.             % LNL family infrastructure
@import "./mymodule".    % Relative path to local module
```

---

## Resolution Order

When resolving `@import foo`:

1. **Built-in modules** — `lib/calculus/foo.calc` or `lib/foo/`
2. **Project-local** — `./foo.calc` in same directory
3. **Explicit path** — if `foo` starts with `./` or `/`

### Built-in Modules

| Module | Path | Description |
|--------|------|-------------|
| `primitives` | `lib/primitives/` | bin, nat, string with FFI |
| `lnl` | `lib/calculus/lnl.family` | LNL infrastructure |
| `ill` | `lib/calculus/ill.calc` | ILL connectives |

---

## Primitives Module

The `primitives` module is special: it has both declarative definitions AND JS implementation.

### Declarative Part: `lib/primitives/primitives.calc`

```
% Binary numbers with lazy storage
bin: type
  @primitive bigint.

e: bin
  @ascii "0"
  @latex "\\epsilon".

i: bin -> bin
  @ascii "i #1"
  @prec 90.

o: bin -> bin
  @ascii "o #1"
  @prec 90.

@literal bin /[0-9]+/.
@literal bin /0x[0-9a-fA-F]+/.
@literal bin /0b[01]+/.

% Natural numbers
nat: type @primitive bigint.
z: nat @ascii "0".
s: nat -> nat @ascii "S #1".

% Strings
string: type @primitive string.
```

### JS Part: `lib/primitives/bin.js`

```javascript
module.exports = {
  name: 'bin',
  primitiveType: 'bigint',

  // Create binlit node from parsed value
  fromLiteral: (str) => {
    if (str.startsWith('0x')) return BigInt(str);
    if (str.startsWith('0b')) return BigInt('0b' + str.slice(2));
    return BigInt(str);
  },

  // Pattern matching for lazy expansion
  match: (value, pattern) => {
    if (pattern === 'e') return value === 0n ? {} : null;
    if (pattern === 'i') return value % 2n === 1n ? { tail: value / 2n } : null;
    if (pattern === 'o') return value % 2n === 0n ? { tail: value / 2n } : null;
    return null;
  },

  // FFI operations
  ffi: {
    plus: (a, b) => a + b,
    mul: (a, b) => a * b,
    inc: (a) => a + 1n,
    gt: (a, b) => a > b,
  },

  // Rendering
  render: (value, format) => {
    if (format === 'hex') return '0x' + value.toString(16);
    if (format === 'binary') return '0b' + value.toString(2);
    return value.toString();
  }
};
```

---

## Loader Implementation

### Parsing @import

```javascript
function parseImport(line) {
  const match = line.match(/@import\s+([^\s.]+)\./);
  if (!match) return null;
  return match[1];  // module name
}
```

### Module Resolution

```javascript
function resolveModule(name, currentPath) {
  // 1. Built-in modules
  const builtinPath = path.join(__dirname, 'lib', name);
  if (fs.existsSync(builtinPath + '.calc') ||
      fs.existsSync(path.join(builtinPath, 'index.calc'))) {
    return { type: 'builtin', path: builtinPath };
  }

  // 2. Project-local
  const localPath = path.join(path.dirname(currentPath), name + '.calc');
  if (fs.existsSync(localPath)) {
    return { type: 'local', path: localPath };
  }

  // 3. Explicit path
  if (name.startsWith('./') || name.startsWith('/')) {
    return { type: 'explicit', path: name };
  }

  throw new Error(`Module not found: ${name}`);
}
```

### Loading with Dependencies

```javascript
async function loadCalc(path, loaded = new Set()) {
  if (loaded.has(path)) return;  // Prevent cycles
  loaded.add(path);

  const content = fs.readFileSync(path, 'utf-8');
  const lines = content.split('\n');

  // First pass: resolve imports
  for (const line of lines) {
    const importName = parseImport(line);
    if (importName) {
      const resolved = resolveModule(importName, path);
      await loadCalc(resolved.path, loaded);
    }
  }

  // Second pass: parse definitions
  // ... normal .calc parsing
}
```

---

## Primitive Type Registry

Track which types have primitive implementations:

```javascript
const primitiveRegistry = new Map();

function registerPrimitive(typeName, jsModule) {
  primitiveRegistry.set(typeName, jsModule);
}

function getPrimitive(typeName) {
  return primitiveRegistry.get(typeName);
}

// Usage in unification
function unify(pattern, term) {
  const termNode = Store.get(term);

  // Check if term is a primitive
  if (termNode.tag.endsWith('lit')) {
    const typeName = termNode.tag.slice(0, -3);  // 'binlit' → 'bin'
    const primitive = getPrimitive(typeName);
    if (primitive) {
      return primitive.match(termNode.children[0], pattern);
    }
  }

  // Normal unification
  // ...
}
```

---

## Implementation Tasks

### Phase 1: @import Parsing
- [ ] Parse `@import` directives in `.calc` loader
- [ ] Implement module resolution (builtin, local, explicit)
- [ ] Handle circular import prevention
- [ ] Test: `@import primitives` loads bin, nat, string

### Phase 2: Primitive Registry
- [ ] Create primitive type registry
- [ ] Load JS modules for primitives on import
- [ ] Integrate registry with unification
- [ ] Test: `bin` type has `match`, `ffi`, `render` functions

### Phase 3: Built-in Modules
- [ ] Create `lib/primitives/primitives.calc`
- [ ] Create `lib/primitives/bin.js`, `nat.js`, `string.js`
- [ ] Ensure primitives auto-registered on import

---

## Cross-References

- `dev/lazy-primitive-storage.md` — How primitive values are stored
- `dev/syntactic-sugar.md` — @literal uses primitive registry
- `lib/v2/calculus/index.js` — Module loader implementation

---

*Created: 2026-02-10*
