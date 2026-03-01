---
title: "Precompiled SDK Loading"
created: 2026-03-01
modified: 2026-03-01
summary: "Eliminated 51ms mde.load() setup via binary precompilation + Pratt parser. Source load ~11ms (was 51ms), precompiled ~2.6ms. Tree-sitter removed entirely (-1105 lines)."
tags:
  - performance
  - symexec
  - evm
  - benchmarking
  - compilation
  - architecture
type: implementation
status: done
priority: 3
cluster: Performance
depends_on: []
required_by: []
---

# Precompiled SDK Loading

## Problem

`mde.load()` takes **51ms** of setup before `explore()` can run. The `calc-vs-hevm.md` comparison reports "calc 22ms vs hevm 52ms = 2.4× faster" — but 22ms is explore-only. True end-to-end is **61ms, making calc 17% slower than hevm**.

```
MEASURED (median of 10, warm, tree-sitter cached):

SETUP (51.5ms):
  convert.load (I/O + parse + hash):  48.9ms   (3896 Store entries)
  compileRule (73 rules):              2.4ms
  buildIndex (41 clauses):             0.1ms
  decomposeQuery:                      0.15ms

EXECUTION:
  explore (structural memo):           9.2ms

TOTAL:                                 60.7ms
hevm reference:                        52ms
```

## Root Cause Breakdown

`convert.load()` dominates at 49ms. Internal breakdown:

| Phase | Time | Notes |
|---|---|---|
| File I/O + #import resolution | 1.5ms | 3 files, 51K chars total |
| Hex expansion | 0.1ms | N_XX → binary notation |
| **Tree-sitter parse** | **12ms** | ~11ms fixed WASM overhead + ~1ms proportional |
| **AST conversion (Store.put)** | **35ms** | 3896 content-addressed entries |

Two independent bottlenecks:
1. **Tree-sitter WASM call overhead** — 11ms fixed cost per parse, regardless of input size (767-line code file: 11.5ms, full 51K file: 12.7ms)
2. **Store.put volume** — 3896 entries × ~9µs/entry. Each entry: FNV-1a hash + DEDUP Map lookup + TypedArray write + string interning

## Prerequisites (done)

### Store.put collision detection

`Store.put()` used FNV-1a 32-bit hashing for DEDUP with **no structural equality check**. On hash collision, it silently returned the wrong term — a soundness violation. Fixed: `matchesEntry()` now verifies tag + arity + children on every DEDUP hit. On collision, throws with diagnostic message. Cost: O(arity) per put (arity 0-4), negligible vs the 9µs/entry total.

Birthday paradox at 3896 entries: ~0.18% per run. Low but non-zero. The fix turns a silent wrong answer into a loud error. Future: upgrade to 64-bit hash if scale demands it.

### oplus/with precedence fix

`ill.calc` declared both `with` and `oplus` at `@prec 70 left`. The tree-sitter grammar gave `&` higher precedence than `+` (separate grammar levels). This meant `A + B & C` parsed differently between the two parser paths. Fixed: oplus changed to `@prec 65 left`. Both parsers now agree: `&` (70) binds tighter than `+` (65).

### Pratt parser binder support

`buildParserFromTables` extended with opt-in features via tables fields:
- `binders: { exists: 'exists', forall: 'forall' }` — `exists X. body` with de Bruijn encoding
- `multiCharFreevars: true` — uppercase multi-char identifiers → freevar with `_` prefix
- `numbers: true` — decimal/hex literals → `Store.put('binlit', [BigInt(n)])`

These are opt-in: existing callers (browser, rules parser) are unaffected. 9 new tests cover binders, nested binders, de Bruijn indices, multi-char freevars, and number literals.

## Why Pratt, Not Tree-sitter, Not Naive Recursive Descent

**History**: The original parser was a naive recursive descent that crashed with stack overflow on deeply nested binary notation — `(i (o (i (o ... (e)))))` at 256 levels. Tree-sitter was adopted because its GLR parser handles arbitrary depth in O(n) without stack growth.

**Problem with tree-sitter**: 11ms fixed WASM overhead per parse. The grammar is manually maintained (`grammar.js`) and drifted from the calculus definition (the oplus/with precedence bug). Two separate parser implementations for the same syntax = divergence risk.

**Why Pratt works**: A Pratt parser uses ~2 stack frames per nesting level (vs ~7x amplification in tree-sitter CST walking). At 256 levels (deepest in the codebase — hand-written binary mask in `bin.ill`), that's ~512 frames. Node.js stack limit is ~12,800 frames. Safety margin: **25x**.

The deepest nesting comes from `bin.ill`'s `to256` clause (256 levels). EVM bytecode files (`_code.ill`) use `0x` hex literals parsed as atomic tokens (zero nesting). `N_XX` hex expansion produces max 8-level nesting per byte.

**Why not just recursive descent**: Pratt IS a form of recursive descent — specifically, operator-precedence climbing. The key advantage over a naive RD parser: the operator table is **derived from the calculus definition** (`ill.calc` `@prec`/`@assoc` annotations). Change the calculus, and the parser updates automatically. Single source of truth — no hand-maintained grammar that can drift.

**Extra safety**: For binary prefix chains `(i (i (i ...)))`, an iterative accumulator can be added to `parseAtom` — detect `i`/`o` heads and accumulate bits in a loop instead of recursing. This would make binary parsing O(1) in stack depth.

## Precompilation Boundary

The import chain for symbolic multisig:

```
multisig_nocall_solc_symbolic.ill  (29 lines, query)
├── #import(evm.ill)               (1436 lines, 44 EVM opcodes + rules)
│   └── #import(bin.ill)           (217 lines, arithmetic primitives)
└── #import(multisig_nocall_solc_code.ill)  (767 lines, contract bytecode)
```

Store entry distribution:

| Layer | Entries | % | Stability |
|---|---|---|---|
| SDK: bin.ill + evm.ill | 1599 | 41% | Stable (changes with CALC versions) |
| User: bytecode + query | 2297 | 59% | Per-contract (code.ill generated, query hand-written) |

**hevm equivalence**: hevm's EVM semantics are compiled into the Haskell binary. Our precompiled SDK is the same thing — stable EVM semantics loaded once. hevm loads bytecode at runtime; we load code.ill + query at runtime. Fair comparison = precompiled SDK + runtime user program.

## TODO_0060.Opt_A — Precompiled Store Binary

### Binary Format (Zig-friendly)

The Store's SoA layout maps directly to flat typed arrays:

```
HEADER (20 bytes):
  u32 magic              0x43414C43 ("CALC")
  u16 version            1 (format version — increment on breaking changes)
  u8  endian             1 (1 = little-endian)
  u8  reserved           0
  u32 nodeCount          (e.g. 1599 for SDK)
  u32 stringCount        (e.g. ~150)
  u32 bigintCount        (e.g. ~40)

SOA ARRAYS:
  u8[nodeCount]          tags       (~1.6 KB)
  u8[nodeCount]          arities    (~1.6 KB)
  PADDING                0-3 bytes to next 4-byte boundary
  u32[nodeCount]         child0     (~6.4 KB)
  u32[nodeCount]         child1     (~6.4 KB)
  u32[nodeCount]         child2     (~6.4 KB)
  u32[nodeCount]         child3     (~6.4 KB)

DEDUP HASHES (precomputed content hashes):
  u32[nodeCount]         contentHashes  (~6.4 KB)

STRING TABLE:
  u16 len, utf8[len]     × stringCount    (~2 KB)

BIGINT TABLE:
  u8 sign, u16 byteLen, bytes[byteLen]  × bigintCount    (~0.5 KB)

TAG REGISTRY:
  u16 tagCount
  (u16 nameLen, utf8[nameLen])  × tagCount  (~0.3 KB)
  Tag IDs are implicit: pre-registered tags (0..PRED_BOUNDARY-1) are not
  stored; dynamic tags start at PRED_BOUNDARY and are registered in order.

SDK METADATA (JSON):
  u32 metaLen
  utf8[metaLen]          { types, clauses, forwardRules, compiledRules, queries }

FOOTER:
  u32 crc32              CRC32 of everything before this field

TOTAL: ~38 KB for SDK-only, ~65 KB for full program
```

**Alignment**: Padding between u8 arrays (tags, arities) and u32 arrays (child0-3) is required. Both JS (`new Uint32Array(buffer, offset)` requires 4-byte-aligned offset) and Zig (`@alignCast(4, ptr)`) reject unaligned u32 access. Padding = `(4 - (2 * nodeCount) % 4) % 4` bytes of zeros.

**Endianness**: Standardized on little-endian (all target platforms: x86, ARM, RISC-V). Reader checks endian byte — mismatch is a format error, not silent corruption.

**CRC32**: Detects truncated or corrupted cache files. Cheap (~0.01ms for 38 KB). On mismatch, cache miss → regenerate.

This is directly `mmap`-able in Zig as packed slices — zero parsing, zero allocation, just pointer arithmetic. `tags[i]`, `child0[i]` etc. are immediate memory offsets. The content hashes enable DEDUP rebuild via pure `Map.set` — no FNV-1a recomputation.

In Node.js: `fs.readFileSync` → `Buffer` → create `Uint8Array`/`Uint32Array` views → `Store.bulkLoad()`.

### Store API Changes

```javascript
// lib/kernel/store.js — new exports

/** Serialize Store state to flat binary buffer */
function snapshot() {
  // Copy SoA arrays (tags, arities, child0-3) as slices
  // Precompute content hashes (computeHash per entry)
  // Serialize string table, bigint table, tag registry
  // Return Buffer
}

/** Restore Store state from binary buffer */
function restore(buffer) {
  // 1. Reset dynamic tags (TAG entries for IDs >= PRED_BOUNDARY)
  // 2. Replay tag registry from binary
  // 3. Bulk memcpy typed array slices (tags, arities, child0-3)
  // 4. Rebuild string interning tables (STRING_TO_ID + ID_TO_STRING)
  // 5. Rebuild bigint table (BIGINT_TABLE)
  // 6. Rebuild DEDUP map from precomputed hashes (Map.set per entry)
  // 7. Set nextId, nextStringId, nextBigIntId, nextTag
}
```

**Correctness: tag registry reset is required.** `Store.clear()` does NOT reset dynamic tags — `TAG['stack']` persists across `clear()` with its old ID. If a different file was loaded first (registering tags in a different order), tag IDs in the binary won't match the live registry. The restore must reset all dynamic tags (IDs ≥ `PRED_BOUNDARY`) before replaying the binary's tag registry.

DEDUP rebuild is required because `explore()` calls `Store.put()` during execution (substitution results, FFI-computed terms). Without DEDUP, duplicate terms would get different IDs, breaking content-addressing.

Measured restore cost breakdown (1599 SDK entries):

| Restore phase | Time | Notes |
|---|---|---|
| Bulk TypedArray.set × 6 | 0.002ms | memcpy, O(1) per array |
| DEDUP Map.set × 1599 | 0.07ms | from precomputed hashes |
| String table rebuild | ~0.01ms | ~150 strings, Map.set each |
| BigInt table rebuild | ~0.001ms | ~40 entries, array push |
| **Total Store.restore** | **~0.22ms** | measured median |

For comparison, Store.put replay (recomputing hashes): **0.55ms** — 2.5× slower.

### Incremental Loading

After SDK restore at Store IDs 1..N, user program loads incrementally at IDs N+1..M. Content-addressing guarantees ID stability: same (tag, children) → same ID via DEDUP.

```javascript
// Load flow
Store.restore(sdkBinary);          // IDs 1..1599 from binary, 0.22ms
const sdk = JSON.parse(metaJSON);  // types, clauses, rawForwardRules, ~0.05ms

// User program adds IDs 1600..3896
const user = await convert.load('multisig.ill', { skipImport: 'evm.ill' });
// merge: sdk.forwardRules ∪ user.forwardRules, sdk.clauses ∪ user.clauses
```

**SDK metadata**: `types` (Map<string, hash>), `clauses` (Map<string, {hash, premises}>), `rawForwardRules` (array of {name, hash, antecedent, consequent}). All reference Store IDs that exist after restore. Serialized as JSON section in the binary (~2 KB, parse cost ~0.05ms).

**`parseExpr` API**: `convert.parseExpr(source)` is used by tests and externally. Must remain functional — the new parser must support standalone expression parsing (not just full-file parsing).

### Cache Invalidation

Content hash of source files as cache key:

```javascript
// Cache key = FNV-1a hash of all source files in dependency set
const key = hashCombine(
  hashString(fs.readFileSync('evm.ill', 'utf8')),
  hashString(fs.readFileSync('bin.ill', 'utf8'))
);
const cachePath = `out/cache/${key.toString(16)}.bin`;

// On load: if cachePath exists → restore; else → full load + write cache
```

Cache file naming: `out/cache/<hex-hash>.bin`. No manifest file needed — the hash IS the version. If `evm.ill` changes, hash changes, old cache is stale (never loaded). Periodically clean stale caches.

**Further optimization (out of scope)**: Precompiling user program code blocks (e.g., `multisig_nocall_solc_code.ill`) via Store.restore could eliminate ~4ms of user-program parse time. Worth exploring alongside generalized array structures — encoding program code as a single linear array predicate instead of hundreds of individual `code` facts. Separate research task.

### Expected Performance

```
PRECOMPILED SETUP (Opt_A only, tree-sitter for user program):
  Store.restore (SDK binary):   0.22ms  (bulk copy + DEDUP from precomputed hashes)
  compileRule (73 rules):       2.4ms   (deterministic, could also cache — see Opt_C)
  buildIndex:                   0.1ms
  User program parse:          ~33ms    (12ms tree-sitter WASM + ~21ms Store.put × 2297)
  ───
  TOTAL SETUP:                ~36ms    (down from 51ms)
  + explore:                    9.2ms
  TOTAL END-TO-END:           ~45ms    (down from 61ms, vs hevm 52ms)
```

Tree-sitter's 11ms fixed WASM cost still dominates the user program parse. See Opt_B below.

## TODO_0060.Opt_B — Calculus-Generated .ill Parser

### The Parser Already Exists

`lib/calculus/builders.js` has a **Pratt precedence-climbing parser** generated from the calculus definition. It's used by the browser (`lib/browser.js`), the rules parser (`lib/rules/rules2-parser.js`), and the sequent parser. The only place it's NOT used is `lib/engine/convert.js` — which instead uses tree-sitter.

The generated parser works from `parserTables` (precomputed in `out/ill.json`):

```json
{
  "operators": [
    { "name": "loli", "op": "-o", "precedence": 50, "assoc": "right" },
    { "name": "tensor", "op": "*", "precedence": 60, "assoc": "left" },
    { "name": "oplus", "op": "+", "precedence": 65, "assoc": "left" },
    { "name": "with", "op": "&", "precedence": 70, "assoc": "left" }
  ],
  "nullary": { "I": "one", "zero": "zero" },
  "unaryPrefix": {
    "!": { "name": "bang", "precedence": 80, "keyword": false },
    "exists": { "name": "exists", "precedence": 45, "keyword": true },
    "forall": { "name": "forall", "precedence": 45, "keyword": true }
  }
}
```

These tables are **derived from the calculus definition** (ill.calc `@prec` and `@assoc` annotations). This is the whole point of CALC: the calculus defines the logic, and everything — including the parser — falls out of that definition.

### What's Missing

The generated parser handles **connectives** (the calculus-defined part). For .ill files, it needs **framework-level extensions** (ambient term syntax that any calculus needs) and a **meta-syntax wrapper** (declarations, imports):

| Feature | Category | Current handler | Status in generated parser |
|---|---|---|---|
| `A * B`, `A -o B`, `!A`, etc. | Calculus connectives | parserTables | Done |
| `exists X. body` (binders) | Framework term syntax | convert.js:104-115 | Done (tables.binders) |
| `42`, `0xff` (numbers) | Framework term syntax | convert.js:58-59 | Done (tables.numbers) |
| `Sender` (multi-char freevars) | Framework term syntax | convert.js:70 | Done (tables.multiCharFreevars) |
| `f x y z` (application) | Framework term syntax | convert.js:152-192 | Missing |
| `i`/`o` (binary normalization) | Framework term syntax | convert.js:172-179 | Missing |
| `A -> B` (arrow types) | Structural | convert.js:120-121 | Missing |
| `A -o { B }` (forward rule) | Structural (monad wrap) | convert.js:126-128 | Missing |
| `name: expr.` | Meta-syntax | tree-sitter | Not expr parser's job |
| `#import(path)` | Meta-syntax | resolveImports | Not expr parser's job |
| `#kind expr.` | Meta-syntax | tree-sitter | Not expr parser's job |
| `<- premise` | Meta-syntax | tree-sitter | Not expr parser's job |
| `% comment` | Meta-syntax | tree-sitter | Not expr parser's job |

### Design: Two Layers (calculus-agnostic)

The naming and architecture must not be calculus-specific. "ILL" is one calculus. A different .calc/.family (say, classical linear logic, or a custom process algebra) must use the same parser infrastructure with different tables.

**Layer 1 — Expression parser** (`lib/calculus/builders.js`, already done):

`buildParserFromTables(tables)` takes a tables object and returns a `parse(input) → hash` function. The tables are **derived from the calculus definition** — change the calculus, parser updates automatically. Extended features are opt-in via tables fields:

```javascript
const tables = computeParserTables(constructors);
// Opt-in extensions for .ill/.calc/.family parsing:
tables.binders = { exists: 'exists', forall: 'forall' };
tables.multiCharFreevars = true;
tables.numbers = true;
```

Remaining extensions (application, arrow, forward rule) are also framework-level and calculus-independent. They'll be added to `buildParserFromTables` as additional opt-in fields:

```javascript
tables.application = true;    // f x y → Store.put(f, [x, y])
tables.arrows = true;         // A -> B → Store.put('arrow', [A, B])
tables.forwardRules = true;   // A -o { B } → loli(A, monad(B))
```

Application is handled by adding a high-precedence "juxtaposition" rule to `parseExpr`: after parsing a primary, if the next token is another primary (not an operator, not `)`, not `.`), it's left-associative application with flat predicate form. This is standard Pratt parser technique.

**Layer 2 — Declaration parser** (`lib/parser/declarations.js`, ~70 lines):

```javascript
// Calculus-agnostic. Parses any .ill, .calc, .family file.
// Delegates expression parsing to a provided parser function.

function parseDeclarations(source, parseExpr) {
  let pos = 0;
  const declarations = [];

  while (pos < source.length) {
    skipWS();
    if (atEnd()) break;
    if (peek('%')) { skipLine(); continue; }        // comments
    if (peek('#')) { parseQuery(); continue; }      // #kind directives
    if (peek('@')) { parseDirective(); continue; }  // @family, @extends, etc.
    parseDeclaration();                             // name: body @annotations.
  }

  return declarations;
}
```

Each declaration extracts the text between `:` and `.` (or `<-`), then calls the provided expression parser on that substring. No precedence logic in the wrapper — all operator handling is in the expression parser. `@annotations` are parsed as key-value pairs (same grammar for all file types).

**Why two layers, not one**: The expression parser is a reusable function (also used by `parseExpr()` API, sequent parsing, rules parsing). The declaration parser is a thin framing layer. Separating them means:
- `parseExpr('A * B')` works standalone (tests, REPL)
- `parseDeclarations(fileContent, parseExpr)` wraps files
- Different file types (`.ill`, `.calc`, `.family`) use the same declaration parser — only the expression parser configuration differs (`.calc` has no connective operators, `.ill` has the full table)

**File placement**: `lib/parser/declarations.js` alongside the existing `lib/parser/sequent-parser.js`. Both are calculus-agnostic parsers that take an expression parser function as input. The `lib/parser/` directory becomes the home for all parsing modules.

### Why This Is Better

1. **Calculus-derived**: Operator precedence and associativity come from `@prec`/`@assoc` annotations. Change the calculus, and the parser updates automatically.
2. **Single source of truth**: The browser, prover, rules parser, and engine all use the same `buildParserFromTables`. No divergence risk.
3. **Calculus-agnostic**: Nothing in the parser is ILL-specific. A new calculus with different connectives, a different `.calc` file, different precedences — everything works, no new parser code needed.
4. **Already tested**: `buildParserFromTables` is in production (browser UI, sequent parsing). Extensions (binders, numbers, multi-char freevars) have 9 new tests. Only application/arrow/forward-rule remain.
5. **Minimal new code**: ~40 lines of extensions to builders.js + ~70 lines declaration parser. Compare to tree-sitter: grammar.js (192 lines) + WASM binary (11 KB) + cst-to-ast.js (520 lines).

### Error Reporting

Tree-sitter gives line/column info for syntax errors for free. The Pratt parser currently only reports `pos` (character offset). Need position tracking (~5 lines):
```javascript
let line = 1, col = 1;
// Update in ws(): if (src[pos] === '\n') { line++; col = 1; } else col++;
// Errors: `Parse error at line ${line}:${col}: ...`
```

### Impact

```
WITHOUT calculus-generated parser (Opt_A only):
  User program: 12ms tree-sitter + 21ms Store.put = ~33ms

WITH calculus-generated parser (Opt_A + Opt_B):
  User program: ~4ms parse+Store.put (fused, no WASM)
  SDK restore:                                         0.22ms
  compileRule:                                         2.4ms
  ───
  TOTAL SETUP:                                         ~6.7ms
  + explore:                                             9.2ms
  TOTAL END-TO-END:                                   ~16ms  (vs hevm 52ms = 3.3× faster)
```

The fused parse eliminates both the 11ms tree-sitter WASM overhead AND the separate AST conversion pass. User program (~2300 entries) at ~1.7µs/entry fused parse+put = ~4ms.

### Scope: Replace tree-sitter entirely

The .calc/.family syntax is identical to .ill syntax plus `@key value` annotations:

```
% ill.calc
tensor: formula -> formula -> formula
  @ascii "_ * _"
  @prec 60 left.

% lnl.family
lin_exchange: deriv (seq G (comma X Y) C)
  <- deriv (seq G (comma Y X) C)
  @pretty "XL"
  @structural exchange.
```

Same declarations, same expressions (arrows + application), same comments, same `<-` premises. The meta-syntax wrapper needs ~10 more lines for `@annotations` and standalone `@directives` (`@family`, `@extends`, `@metavar`, `@schema`).

**No bootstrapping problem**: .calc files define connectives but their expression bodies only use arrows and application — framework syntax that doesn't depend on parser tables. The connective operators (tensor `*`, loli `-o`, etc.) are what's BEING defined, not used in the definition.

Bootstrap path:
1. Parse .calc/.family with meta-syntax wrapper + framework syntax (arrows, application)
2. Extract `@prec`/`@assoc` annotations → build `parserTables`
3. Use `parserTables` to parse .ill/.rules files (with connective operators)

```
lib/engine/convert.js   →  uses calculus-generated parser  (runtime, .ill)
lib/meta-parser/         →  uses same parser               (build time, .calc/.family)
lib/rules/rules2-parser  →  already uses buildParser()     (build time, .rules)
lib/tree-sitter-mde/     →  DELETE entirely
```

**Cleanup**: remove `lib/tree-sitter-mde/` (~11 KB WASM + grammar.js + bindings), `lib/meta-parser/cst-to-ast.js` (~400 lines), and the `build:ts:wasm` npm script. The meta-parser's `loader.js` (`@extends` chain resolution) stays but switches to the new parser.

## TODO_0060.Opt_C — Precompile Rules Too

`compileRule()` is deterministic: same raw rule → same compiled rule. The compiled rules contain Maps (`metavarSlots`, `linearMeta`, `existentialGoals`) and Sets (`freevars`, `persistentDeps`), but no closures — all are serializable.

### Serialization

**Plan:** `v8.serialize`/`v8.deserialize` for native Map/Set support. **Actual:** JSON with explicit Set↔Array conversion helpers (`_serializeCompiledRules` / `_deserializeCompiledRules` in `lib/engine/index.js`).

v8.serialize measured 1.38ms deserialize — no better than recompiling (1.41ms). Instead, compiled rules are embedded in the existing JSON metadata section of the binary cache. This avoids the v8 wire format versioning problem entirely (no cache key per Node.js major version needed).

**Gotcha — Set serialization**: `linearMeta[p].freevars` and `.persistentDeps` are JavaScript `Set` objects. `JSON.stringify(new Set(...))` produces `{}`, silently dropping entries. The serialize/deserialize helpers convert Set↔Array at the serialization boundary.

Store the compiled rules in the binary alongside the Store snapshot. Saves 2.4ms. Combined with Opt_A + Opt_B: total setup ~4.6ms.

This is medium priority — 2.4ms is 37% of the remaining setup cost after Opt_A + B.

## Implementation Plan

### Stage 0: Prerequisites (done)

- `lib/kernel/store.js` — collision detection in `Store.put()` via `matchesEntry()`
- `calculus/ill/ill.calc` — oplus precedence fixed to `@prec 65 left`
- `lib/calculus/builders.js` — binder, number, multi-char freevar extensions (opt-in)
- `tests/calculus.test.js` — 9 new tests for extended parser + precedence
- `out/ill.json` — regenerated with updated parser tables

### Stage 1: Store.snapshot/restore + binary format

Files to modify:
- `lib/kernel/store.js` — add `snapshot()`, `restore()`, `resetDynamicTags()` exports. **Critical**: `restore()` must reset dynamic tags (IDs ≥ `PRED_BOUNDARY`) before loading. `snapshot()` must precompute content hashes (via `computeHash` per entry).
- `lib/engine/index.js` — add `precompile()`, `loadPrecompiled()` API
- `lib/hash.js` — already has FNV-1a (use for cache key)

New files:
- `lib/engine/store-binary.js` — binary serialization/deserialization (~120 lines): write/read SoA arrays + precomputed hashes + string/bigint tables + tag registry + SDK metadata JSON. Include alignment padding, format version, endianness marker, CRC32.
- `tools/precompile.js` — CLI: `node tools/precompile.js evm.ill → out/cache/<hash>.bin`

### Stage 2: Incremental loading

Files to modify:
- `lib/engine/convert.js` — `resolveImports()` skip directive for precompiled imports
- `lib/engine/index.js` — `load()` checks cache before full parse, auto-writes cache on miss

### Stage 3: Declaration parser + tree-sitter removal

Files to modify:
- `lib/calculus/builders.js` — add remaining extensions: application (juxtaposition), arrow, forward-rule syntax, binary normalization (`i`/`o`), position tracking (~40 lines)

New files:
- `lib/parser/declarations.js` — calculus-agnostic declaration parser (~70 lines): `name: body.`, `<- premise`, `% comment`, `#kind body.`, `@key value`. Takes an expression parser function as input. Handles `.ill`, `.calc`, and `.family` files — the expression parser configuration (which tables, which extensions) determines what connective operators are available.

Files to modify:
- `lib/engine/convert.js` — replace `mdeParser.parse()` with `parseDeclarations(source, exprParser)`, keep `parseExpr()` API working (now just calls the expression parser directly — no more wrapping in `_tmp: expr.` hack)
- `lib/meta-parser/loader.js` — switch from cst-to-ast.js to `parseDeclarations()` + framework-only expression parser (no connective operators — .calc files only use arrows and application)

Files to delete:
- `lib/meta-parser/cst-to-ast.js` (~520 lines)
- `lib/tree-sitter-mde/` — entire directory (WASM + grammar.js + bindings)

### Stage 4: Benchmark & comparison update

Files to modify:
- `benchmarks/engine/symexec-bench.js` — add precompiled-load variant
- `tools/hevm-bench.sh` — use precompiled SDK for fair comparison
- `doc/documentation/calc-vs-hevm.md` — already updated (2026-03-01)

## Zig Portability

The binary format is designed for zero-copy loading in Zig:

```zig
const StoreSnapshot = struct {
    tags: []const u8,
    arities: []const u8,
    child0: []const u32,
    child1: []const u32,
    child2: []const u32,
    child3: []const u32,
};

fn loadSnapshot(data: []const u8) StoreSnapshot {
    const header = @ptrCast(*const Header, data.ptr);
    const n = header.nodeCount;
    // After header (20 bytes), u8 arrays, then padding to 4-byte boundary
    const u8_end = 20 + 2 * n;
    const u32_start = (u8_end + 3) & ~@as(usize, 3); // align to 4
    return .{
        .tags = data[20..][0..n],
        .arities = data[20 + n ..][0..n],
        .child0 = @ptrCast([*]const u32, @alignCast(4, data[u32_start..].ptr))[0..n],
        // child1 at u32_start + 4*n, child2 at u32_start + 8*n, etc.
    };
}
```

No JSON parsing, no object allocation, no GC pressure. Just pointer arithmetic into memory-mapped file. The alignment padding between u8 and u32 sections ensures `@alignCast` never traps. The SoA layout means cache-friendly iteration over any single field (e.g., scan all tags without touching children).

## Tree-sitter: Replace Entirely

The generated parser replaces tree-sitter for ALL file types. One declaration parser, one expression parser, different configurations:

| File type | Expression parser config | Declaration features | When |
|---|---|---|---|
| `.ill` (programs) | Full tables + all extensions | `name:`, `#kind`, `<-`, `%` | Runtime |
| `.calc` (calculus defs) | No connective ops (framework only) | + `@annotations` | Build time |
| `.family` (structural rules) | No connective ops (framework only) | + `@annotations`, `@directives` | Build time |
| `.rules` (inference rules) | Full tables (already uses `buildParser()`) | Sequent notation | Build time |

The key insight: `.calc` and `.family` files define connectives but their expression bodies only use arrows and application — framework syntax. Connective operators (`*`, `-o`, etc.) are what's BEING defined, not used. So their expression parser needs no operator tables. `.ill` files use the full tables (including the connectives defined by `.calc`).

```
lib/calculus/builders.js        expression parser (Pratt, calculus-generated tables)
lib/parser/declarations.js      declaration parser (calculus-agnostic, takes expr parser)
lib/parser/sequent-parser.js    sequent parser (already exists, uses buildParser)
lib/engine/convert.js           load orchestration (creates parser chain, classifies)
lib/meta-parser/loader.js       @extends resolution (switches to declarations.js)
```

**Cleanup**: delete `lib/tree-sitter-mde/` (~11 KB WASM + grammar.js + bindings), `lib/meta-parser/cst-to-ast.js` (~520 lines), `build:ts:wasm` npm script. `loader.js` stays.

## Testing Strategy

**200+ existing tests** depend on the parsing pipeline (`mde.load`, `mde.parseExpr`). Migration must be staged:

1. **Parity testing** (before deletion): Run both tree-sitter and the new parser on every `.ill` file. Assert identical Store entries for all 3896 SDK entries + all test fixtures. Catches any divergence.

2. **Replace convert.js internals**: Swap tree-sitter for new parser inside `convert.js`. All 200+ existing tests serve as regression tests. `parseExpr` API unchanged — tests don't know about the internal switch.

3. **Replace cst-to-ast.js**: Swap tree-sitter for new parser in `loader.js`. Run `npm run build:bundle` → verify `out/ill.json` is bit-identical. Build-time only — lower risk.

4. **Delete tree-sitter**: Only after stages 2+3 pass with full test suite green.

**New tests to add**:
- Binary snapshot/restore round-trip: snapshot → restore → verify all entries match
- Incremental loading: restore SDK → load user program → verify Store consistency
- Binary format: alignment, endianness detection, CRC32 corruption detection
- Application syntax: `f x y` → flat predicate form (critical for engine correctness)
- Binary normalization: `(i (o (i e)))` → binlit via iterative accumulation
- Arrow and forward rule: `A -> B`, `A -o { B }` parsing

## Projected Timeline (measured)

| Stage | Savings | Cumulative setup | End-to-end | vs hevm |
|---|---|---|---|---|
| **Baseline** | — | 51ms | 61ms | 0.85× |
| **Opt_A**: Store binary (precomputed hashes) | −15ms | 36ms | 45ms | 1.2× |
| **Opt_B**: Calculus-generated parser | −29ms | 6.7ms | 16ms | 3.3× |
| **Opt_C**: Precompile rules | −2.4ms | 4.3ms | 14ms | 3.7× |

Measured inputs: Store.restore = 0.22ms (bulk copy + DEDUP from precomputed hashes), compileRule = 2.4ms, user program gen-parser = ~4ms, explore = 9.2ms.

End state: **4.3ms setup + 9.2ms explore = 13.5ms** (vs hevm 52ms = **3.9× faster**).

## Actual Results (measured 2026-03-01)

All three optimizations implemented. Tree-sitter removed entirely (-1105 lines net).

| Metric | Before | After | Speedup |
|---|---|---|---|
| Source load (EVM SDK) | 51ms | ~11ms | 4.7x |
| Precompiled load | N/A | ~2.6ms | 4.2x vs source |
| Warm total (load+explore) | ~56ms | ~4.7ms | 11.9x |
| Binary cache size | N/A | 211 KB | — |
| Tree-sitter WASM | 11ms | 0ms | eliminated |
| Rule compilation | 1.4ms | 0ms (cached) | eliminated |
| Tests | 611 | 663 | +52 new tests |
| Lines of code | +1531 | -810 net | -1105 lines from tree-sitter |

Implementation:
- **Opt_A**: `Store.snapshot()`/`restore()` + `lib/engine/store-binary.js` (binary format with CRC32)
- **Opt_B**: `lib/parser/declarations.js` + `buildParserFromTables` extensions (application, arrows, forwardRules, binaryNormalization). All parsers now synchronous.
- **Opt_C**: Compiled rules stored in binary cache metadata (JSON, not v8.serialize — v8 showed no improvement over recompile). Set fields in `linearMeta` (freevars, persistentDeps) require explicit Array↔Set conversion for JSON round-trip.

The v8.serialize approach from the plan (1.2ms estimated) measured at 1.38ms — no better than recompiling (1.41ms). Instead, compiled rules are included in the existing JSON metadata section of the binary cache, avoiding rule compilation entirely on cache hit.
