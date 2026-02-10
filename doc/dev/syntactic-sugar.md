# Syntactic Sugar

Implementation design for `@literal` and `@sugar` annotations in `.calc` files.

---

## Overview

Two kinds of syntactic sugar:

1. **Literal sugar** (`@literal`): Lexer-level transformation of tokens
2. **Pattern sugar** (`@sugar`): Parser-level transformation of grammar patterns

---

## Literal Sugar

Transform tokens at lexer level before parsing.

### Syntax

```
@literal <type> /<regex>/.
```

### Example

```
bin: type @primitive bigint.

@literal bin /[0-9]+/.           % "123" → binlit(123n)
@literal bin /0x[0-9a-fA-F]+/.   % "0xff" → binlit(255n)
@literal bin /0b[01]+/.          % "0b1010" → binlit(10n)
```

### Semantics

When the lexer sees a token matching the regex:
1. Determine the target type (`bin`)
2. Look up the primitive handler for that type
3. Parse the literal value (decimal, hex, binary)
4. Create a `binlit` node with the BigInt value

### Implementation

In `.calc` loader:

```javascript
function parseLiteralDirective(line) {
  const match = line.match(/@literal\s+(\w+)\s+\/(.+)\//);
  if (!match) return null;
  return { type: match[1], pattern: new RegExp('^' + match[2]) };
}

// In lexer
function tokenize(src, literals) {
  for (const { type, pattern } of literals) {
    const match = src.match(pattern);
    if (match) {
      const value = parseLiteralValue(match[0], type);
      return { tag: type + 'lit', value };
    }
  }
  // ... normal tokenization
}
```

---

## Pattern Sugar

Transform grammar patterns at parser level.

### Syntax

On a constructor:

```
<constructor>: <type>
  @sugar <pattern>.
```

### Example

```
graded: bin -> formula -> formula
  @ascii "[]_{ #1 } #2"
  @latex "\\Box_{#1} #2"
  @prec 85
  @sugar NUMBER formula.
```

### Semantics

The `@sugar NUMBER formula` says:
- When parser sees NUMBER followed by formula at this precedence
- Build a `graded` node with:
  - First argument = the NUMBER (already tokenized as `binlit`)
  - Second argument = the formula

**No explicit `=> graded($1, $2)` needed** — it's implicit from the constructor.

### Pattern Elements

| Element | Matches | Notes |
|---------|---------|-------|
| `NUMBER` | Numeric literal | Must have `@literal` for type |
| `STRING` | String literal | Quoted text |
| `IDENT` | Identifier | Variable or atom |
| `formula` | Any formula | Recursive parse |
| `<type>` | Term of type | Type-constrained |

### Implementation

In parser builder:

```javascript
function buildSugarRule(constructor, sugar) {
  const elements = sugar.split(/\s+/);
  const arity = constructor.arity;

  return {
    precedence: constructor.prec,
    parse: (parser) => {
      const args = [];
      for (const elem of elements) {
        if (elem === 'NUMBER') {
          args.push(parser.expectNumber());
        } else if (elem === 'formula') {
          args.push(parser.parseFormula());
        } else {
          throw new Error(`Unknown sugar element: ${elem}`);
        }
      }
      return Store.intern(constructor.name, args);
    }
  };
}
```

---

## Composition

Literal and pattern sugar compose naturally.

### Example: `10 eth`

Given:
```
@literal bin /[0-9]+/.

graded: bin -> formula -> formula
  @sugar NUMBER formula.
```

Parsing `10 eth`:

1. **Lexer** sees `10`, matches `/[0-9]+/`, produces `binlit(10n)`
2. **Parser** sees NUMBER followed by formula
3. **Sugar** applies: `graded(binlit(10n), atom(eth))`

The `10` is stored as `binlit(10n)`, NOT expanded to `o(i(o(i(o(e)))))`.

---

## Precedence

Sugar inherits precedence from the constructor's `@prec` annotation.

```
graded: bin -> formula -> formula
  @prec 85              % Higher than ⊗ (60), ⊸ (50)
  @sugar NUMBER formula.
```

So `10 eth ⊗ 5 btc` parses as `(10 eth) ⊗ (5 btc)`.

---

## Implementation Tasks

### Phase 1: @literal
- [ ] Parse `@literal` directives in `.calc` loader
- [ ] Store literal patterns per type
- [ ] Modify lexer to check literal patterns
- [ ] Test: `123` → `binlit(123n)`

### Phase 2: @sugar
- [ ] Parse `@sugar` annotations on constructors
- [ ] Build sugar rules during parser construction
- [ ] Integrate sugar matching into `parseAtom()`
- [ ] Test: `10 eth` → `graded(binlit(10n), atom(eth))`

### Phase 3: Precedence
- [ ] Sugar inherits precedence from constructor
- [ ] Test: `10 eth ⊗ 5 btc` parses correctly

---

## Cross-References

- `dev/lazy-primitive-storage.md` — How `binlit` nodes are stored
- `dev/import-mechanism.md` — Module system for primitives
- `lib/v2/calculus/index.js` — Parser builder implementation

---

*Created: 2026-02-10*
