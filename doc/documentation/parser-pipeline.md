# Parser Pipeline

One Earley parser, three configurations.

## Architecture

```
              lib/parser/earley-grammar.js
              computeEarleyGrammarFromTables(tables)
              buildParserFromGrammar(spec)
                        │
                        │  (via lib/calculus/builders.js
                        │   buildParserFromTables)
                        │
         ┌──────────────┼──────────────┐
         │              │              │
   Meta Interpreter  Program Int.  Sequent Parser
   lib/meta-parser/  lib/engine/   lib/rules/
   loader.js         convert.js    rules2-parser.js
         │              │              │
   Structured AST   Hash Store     Rule Descriptors
   (constructors,   (content-      (premises,
    annotations)    addressed)      context flow)
```

## Three Parser Paths

### 1. Meta Interpreter — defining calculi

**Files:** `lib/meta-parser/loader.js` + `lib/parser/declarations.js`

**Input:** `.calc` and `.family` files (e.g., `calculus/ill/ill.calc`)

**Output:** Structured AST — connective declarations with types, annotations (`@ascii`, `@latex`, `@prec`, `@polarity`), and `@extends` chains.

**Used by:** `lib/calculus/index.js` to build the runtime calculus object (parser, renderer, AST constructors).

**Parser config:** Framework-only (arrows + application). No connective operators — `.calc` files **define** connectives, they don't **use** them.

```
ill.calc → declarations.js → loader.js (@extends chain) → calculus/index.js
```

### 2. Program Interpreter — running programs

**File:** `lib/engine/convert.js`

**Input:** `.ill` program files (e.g., `calculus/ill/programs/evm.ill`)

**Output:** Content-addressed hashes in the global Store. Types become backward-chaining clauses, forward rules become multiset rewriting rules.

**Used by:** `lib/engine/index.js` (the execution engine).

**Parser config:** Formula operators derived from `.calc` constructors + all extensions: binders, numbers, multi-char freevars, application, arrows, forward rules, binary normalization.

```
evm.ill → declarations.js + Earley parser → Store (hash → {tag, children})
```

### 3. Sequent Parser — defining inference rules

**File:** `lib/rules/rules2-parser.js`

**Input:** `.rules` files with sequent notation (e.g., `calculus/ill/ill.rules`)

**Output:** Rule descriptors (`{ connective, side, arity, contextSplit, contextFlow, premises }`).

**Used by:** `lib/calculus/index.js` and `lib/prover/rule-interpreter.js`.

**Parser config:** Full connective operator tables (via `buildParser()`).

```
ill.rules → custom parser (uses buildParser for formula fragments) → rule descriptors
```

## Two Layers

### Layer 1 — Expression parser (Earley)

**Core engine:** `lib/parser/earley.js` — generic Earley recognizer with Aycock-Horspool nullable handling, back-pointer tree extraction, configurable lexer. O(n³) general, O(n) for the unambiguous stratified grammars CALC generates.

**Grammar generation:** `lib/parser/earley-grammar.js` — generates a stratified CFG from `.calc` constructor annotations (Danielsson-Norell style). Each precedence level becomes a distinct nonterminal; associativity is encoded via same/next references. Binder scoping uses open/closed nonterminals.

**Factory:** `lib/calculus/builders.js:buildParserFromTables(tables)` — delegates to `computeEarleyGrammarFromTables` + `buildParserFromGrammar`. Same interface for all three parser paths. Opt-in extensions via tables fields:

| Extension | Tables field | Example |
|---|---|---|
| Binders | `binders: { exists: 'exists' }` | `exists X. body` → de Bruijn |
| Numbers | `numbers: true` | `42`, `0xff` → binlit |
| Multi-char freevars | `multiCharFreevars: true` | `Sender` → metavar(`Sender`) |
| Application | `application: true` | `f x y` → `Store.put('f', [x, y])` |
| Arrows | `arrows: true` | `A -> B` → arrow(A, B) |
| Forward rules | `forwardRules: true` | `A -o { B }` → loli(A, monad(B)) |
| Preserved sugar | (auto with forwardRules) | `$P` → preserved(P), desugared by convert.js |
| Binary normalization | `binaryNormalization: true` | `(i (o e))` → binlit(2n) |

### Layer 2 — Declaration parser (`lib/parser/declarations.js`)

`parseDeclarations(source, parseExpr, opts)` — calculus-agnostic. Handles:
- `name: body.` — type/clause declarations
- `name: body <- premise.` — clauses with premises
- `A -o { B }.` — forward rules (detected by caller via `hasMonad`)
- `@key value` — annotations (opt-in)
- `@directive args.` — standalone directives
- `#kind body.` — query directives
- `#import(path)` — import directives
- `% comment` — line comments

Takes an expression parser function as input — the same declaration parser handles `.ill`, `.calc`, and `.family` files with different expression parser configurations.

## File Formats

| Extension | Purpose | Expr parser config | Example |
|---|---|---|---|
| `.calc` | Connective definitions | Framework only (arrows, application) | `tensor: formula -> formula -> formula @ascii "_ * _"` |
| `.family` | Family with `@extends` | Framework only (arrows, application) | `@extends ill.calc` |
| `.rules` | Inference rules | Full tables (connective operators) | `tensor_r: G ; D, A, B \|- C ==> G ; D, A * B \|- C` |
| `.ill` | Object-level programs | Full tables + all extensions | `add (s X) Y (s Z) :- add X Y Z.` |

## Key Design Properties

1. **Calculus-derived**: Operator precedence and associativity come from `@prec`/`@assoc` annotations in `.calc` files. Change the calculus, parser updates automatically.
2. **Single source of truth**: Browser, engine, rules parser, and meta-parser all use `buildParserFromTables`. No divergence risk.
3. **Calculus-agnostic**: Nothing ILL-specific. A new calculus with different connectives works without new parser code.
4. **Synchronous**: All parsing is fully synchronous (no WASM, no async/await).
5. **No bootstrapping problem**: `.calc` files define connectives but only use framework syntax (arrows, application) in their bodies. Connective operators are what's being defined, not used.
6. **Earley over Pratt**: The Earley parser handles all CFGs, supports general mixfix operators, and is table-driven (portable to Zig). Trade-off: ~50-80µs higher per-parse constant overhead vs the previous hand-coded Pratt parser. Negligible for real workloads (<1% of engine runtime).
