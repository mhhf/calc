# Parser Pipeline

One tree-sitter grammar, three interpreters.

## Architecture

```
                     lib/tree-sitter-mde/grammar.js
                              │ (Celf-style syntax)
                              │
               ┌──────────────┼──────────────┐
               │              │              │
         Meta Interpreter  Program Int.  Sequent Parser
         lib/meta-parser/  lib/engine/   lib/rules/
               │           convert.js    rules2-parser.js
               │              │              │
         Structured AST   Hash Store     Rule Descriptors
         (constructors,   (content-      (premises,
          annotations)    addressed)      context flow)
```

## Three Parser Paths

### 1. Meta Interpreter — defining calculi

**Files:** `lib/meta-parser/cst-to-ast.js` + `lib/meta-parser/loader.js`

**Input:** `.calc` and `.family` files (e.g., `calculus/ill/ill.calc`)

**Output:** Structured AST — connective declarations with types, annotations (`@ascii`, `@latex`, `@prec`, `@polarity`), and `@extends` chains.

**Used by:** `lib/calculus/index.js` to build the runtime calculus object (parser, renderer, AST constructors).

```
ill.calc → tree-sitter CST → cst-to-ast.js → loader.js (@extends chain) → calculus/index.js
```

### 2. Program Interpreter — running programs

**File:** `lib/engine/convert.js`

**Input:** `.ill` program files (e.g., `calculus/ill/programs/evm.ill`)

**Output:** Content-addressed hashes in the global Store. Types become backward-chaining clauses, forward rules become multiset rewriting rules.

**Used by:** `lib/engine/index.js` (the execution engine).

```
evm.ill → tree-sitter CST → convert.js → Store (hash → {tag, children})
```

### 3. Sequent Parser — defining inference rules

**File:** `lib/rules/rules2-parser.js`

**Input:** `.rules` files with sequent notation (e.g., `calculus/ill/ill.rules`)

**Output:** Rule descriptors (`{ connective, side, arity, contextSplit, contextFlow, premises }`).

**Used by:** `lib/calculus/index.js` and `lib/prover/rule-interpreter.js`.

```
ill.rules → custom parser (regex-based, not tree-sitter) → rule descriptors
```

## File Formats

| Extension | Purpose | Parser | Example |
|-----------|---------|--------|---------|
| `.calc` | Connective definitions | Meta interpreter | `tensor : formula -> formula -> formula @ascii "_ * _"` |
| `.family` | Family with `@extends` | Meta interpreter | `@extends ill.calc` |
| `.rules` | Inference rules | Sequent parser | `tensor_r: G ; D, A, B |- C  ==>  G ; D, A * B |- C` |
| `.ill` | Object-level programs | Program interpreter | `add (s X) Y (s Z) :- add X Y Z.` |

## Key Distinction

The meta interpreter and program interpreter share the SAME tree-sitter grammar but produce different outputs:
- **Meta:** structured AST for defining what connectives exist (used at build time)
- **Program:** content-addressed hashes for execution (used at runtime)
