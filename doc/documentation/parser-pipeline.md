---
title: Parser Pipeline
modified: 2026-08-20
summary: One Earley parser, three configurations — sorted-template grammar generation, ambiguity instrument, parcel sugar.
tags: [parser, implementation, architecture, ill]
---

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

**Ambiguity instrument** (TODO_0268 §5a): static CFG ambiguity is undecidable, so detection is per-input — an always-on counter records dual-derivation chart items (a second distinct back-pointer for an existing item = a first-wins site) and multiple accepting items; `setStrictAmbiguity(true)` turns either into a parse error. `tests/parser-fold-fuzz.test.js` sweeps the whole corpus plus grammar-sampled strings in strict mode (baseline: zero findings). The decidable static layer is the generator-level collision throws below (duplicate circumfix, one graded prefix, mixfix-shape errors). Item-level detection is a documented over-approximation (a duplicate may sit off the accepted spine).

**Grammar generation:** `lib/parser/earley-grammar.js` — generates a stratified CFG from `.calc` constructor annotations (Danielsson-Norell style). Each precedence level becomes a distinct nonterminal; associativity is encoded via same/next references. Binder scoping uses open/closed nonterminals.

**Sorted mixfix templates — the ONE grammar mechanism** (TODO_0268 item A + §5c fold): any `#N`-hole `@ascii` template classifies by the position of its SAME-SORT holes — none → closed (ATOM), right edge → prefix (UNARY), left edge → postfix (tight level above UNARY), both edges → infix (precedence chain), literal-delimited at both ends → closed with interior holes parsing at START (a closed operator's inner expressions are unrestricted). Cross-sort holes target the auxiliary grade chain. This is how till declares its timed surface (`at: formula -> grade -> formula @ascii "#1@#2"`, `after`, `before`, `readPreserved`) and woplus's `A +[Q] B` — a calculus parses what it declares.

Since the §5c fold, the historic families are *normalized into synthetic template records* and emitted by the same machinery: the binary operator table (`_ * _`) → infix templates, unary prefix → prefix templates, nullary constants → closed templates, circumfix (`{ _ }`, `{ #2 }`) → closed templates with an `elide` attribute (unit grade fill), graded prefix (`! #2`) → prefix templates with `elide`/`d15Guard`/`countGrade` attributes covering `!`/`!_0`/`!_ω`/`!_k`. The family tables remain the input surface (the serialized `ill.json` shape, still consulted for lexer-config derivation); only rule emission is folded. Fold parity was verified against the pre-fold builder: 12,000 grammar-sampled strings, hash-identical, before the legacy emission was deleted. `at`'s stamp/grade pun (`{B}@d` regrades the computation) stays kernel-owned in the grammar's atAction, like `$`/preserved.

**Parcel sugar** (§5d, D4): under a grammar with a graded prefix AND a grade chain (till), `4wood` lexes as ONE `PARCEL` token — hash-identical to `!_4 wood`. Fused by construction: identifiers can't start with a digit, so the lexeme is unambiguous, whereas a spaced `4 wood` production is genuinely ambiguous with application juxtaposition (`f 4 wood` = f(4, wood)) — detector-verified in `sorted-templates.test.js`. `4wood@3` and `f 4wood` are loud errors (write `!_4 wood@3`; parcels are formula operands, not term args).

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
