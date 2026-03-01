---
title: "Precompiled SDK Loading"
created: 2026-03-01
modified: 2026-03-01
summary: "Eliminate 51ms mde.load() setup cost via binary precompilation of SDK (evm.ill + bin.ill). Fixes unfair hevm comparison. Zig-friendly binary format."
tags:
  - performance
  - symexec
  - evm
  - benchmarking
  - compilation
  - architecture
type: implementation
status: ready for implementation
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
HEADER (12 bytes):
  u32 nodeCount          (e.g. 1599 for SDK)
  u32 stringCount        (e.g. ~150)
  u32 bigintCount        (e.g. ~40)

SOA ARRAYS (nodeCount entries each):
  u8[nodeCount]          tags       (~1.6 KB)
  u8[nodeCount]          arities    (~1.6 KB)
  u32[nodeCount]         child0     (~6.4 KB)
  u32[nodeCount]         child1     (~6.4 KB)
  u32[nodeCount]         child2     (~6.4 KB)
  u32[nodeCount]         child3     (~6.4 KB)

STRING TABLE:
  u16 len, utf8[len]     × stringCount    (~2 KB)

BIGINT TABLE:
  u16 len, ascii[len]    × bigintCount    (~0.5 KB)

TAG REGISTRY:
  u8 tagCount
  u16 len, utf8[len]     × tagCount       (~0.3 KB)

TOTAL: ~32 KB for SDK
```

This is directly `mmap`-able in Zig as packed slices — zero parsing, zero allocation, just pointer arithmetic. `tags[i]`, `child0[i]` etc. are immediate memory offsets.

In Node.js: `fs.readFileSync` → `Buffer` → create `Uint8Array`/`Uint32Array` views → `Store.bulkLoad()`.

### Store API Changes

```javascript
// lib/kernel/store.js — new exports

/** Serialize Store state to flat binary buffer */
function snapshot() {
  // Copy SoA arrays (tags, arities, child0-3) as slices
  // Serialize string table, bigint table, tag registry
  // Return Buffer
}

/** Restore Store state from binary buffer */
function restore(buffer) {
  // memcpy typed array slices into SoA arrays
  // Rebuild string interning tables
  // Rebuild bigint table
  // Rebuild DEDUP map (computeHash per entry, ~3ms for 1599 entries)
  // Set nextId, nextStringId, nextBigIntId, nextTag
}
```

DEDUP rebuild is required because `explore()` calls `Store.put()` during execution (substitution results, FFI-computed terms). Without DEDUP, duplicate terms would get different IDs, breaking content-addressing.

Measured DEDUP rebuild cost: **~0.8ms** for 1599 entries (in-memory Store.put replay without I/O).

### Incremental Loading

After SDK restore at Store IDs 1..N, user program loads incrementally at IDs N+1..M. Content-addressing guarantees ID stability: same (tag, children) → same ID via DEDUP.

```javascript
// Load flow
Store.restore(sdkBinary);          // IDs 1..1599 from binary
const sdk = deserializeCalc(meta); // compiled rules, clauses, types

// User program adds IDs 1600..3896
const user = await convert.load('multisig.ill', { skipImport: 'evm.ill' });
// merge: sdk.forwardRules ∪ user.forwardRules, sdk.clauses ∪ user.clauses
```

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

### Expected Performance

```
PRECOMPILED SETUP:
  Store.restore (SDK binary):   0.8ms   (memcpy + DEDUP rebuild)
  compileRule (73 rules):       2.4ms   (deterministic, could also cache)
  buildIndex:                   0.1ms
  User program parse:          15-20ms  (tree-sitter + Store.put for 2297 entries)
  ───
  TOTAL SETUP:                ~19ms    (down from 51ms)
  + explore:                    9.2ms
  TOTAL END-TO-END:           ~28ms    (down from 61ms, vs hevm 52ms)
```

This is already an improvement, but tree-sitter's 11ms fixed WASM cost still dominates the user program parse. See Opt_B below.

## TODO_0060.Opt_B — Calculus-Generated .ill Parser

### The Parser Already Exists

`lib/calculus/builders.js` has a **Pratt precedence-climbing parser** generated from the calculus definition. It's used by the browser (`lib/browser.js`), the rules parser (`lib/rules/rules2-parser.js`), and the sequent parser. The only place it's NOT used is `lib/engine/convert.js` — which instead uses tree-sitter.

The generated parser works from `parserTables` (precomputed in `out/ill.json`):

```json
{
  "operators": [
    { "name": "tensor", "op": "*", "precedence": 60, "assoc": "left" },
    { "name": "loli", "op": "-o", "precedence": 50, "assoc": "right" },
    { "name": "with", "op": "&", "precedence": 70, "assoc": "left" },
    { "name": "oplus", "op": "+", "precedence": 70, "assoc": "left" }
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
| `A * B`, `A -o B`, `!A`, etc. | Calculus connectives | parserTables | Already works |
| `f x y z` (application) | Framework term syntax | convert.js:152-192 | Missing |
| `42`, `0xff` (numbers) | Framework term syntax | convert.js:58-59 | Missing |
| `Sender` (multi-char freevars) | Framework term syntax | convert.js:70 | Partial (only single-char) |
| `i`/`o` (binary normalization) | Framework term syntax | convert.js:172-179 | Missing |
| `A -> B` (arrow types) | Structural | convert.js:120-121 | Missing |
| `A -o { B }` (forward rule) | Structural (monad wrap) | convert.js:126-128 | Missing |
| `name: expr.` | Meta-syntax | tree-sitter | Not parser's job |
| `#import(path)` | Meta-syntax | resolveImports | Not parser's job |
| `#kind expr.` | Meta-syntax | tree-sitter | Not parser's job |
| `<- premise` | Meta-syntax | tree-sitter | Not parser's job |
| `% comment` | Meta-syntax | tree-sitter | Not parser's job |

### Design: Two Layers

**Layer 1 — Extended expression parser** (extend `buildParserFromTables`):

The Pratt parser in builders.js needs three additions to `parseAtom`:

```javascript
// 1. Number literals → binlit
const numMatch = src.slice(pos).match(/^(0x[0-9a-fA-F]+|\d+)/);
if (numMatch) {
  pos += numMatch[0].length; ws();
  return Store.put('binlit', [BigInt(numMatch[0])]);
}

// 2. Multi-char freevars (uppercase start)
if (/[A-Z]/.test(src[pos])) {
  const m = src.slice(pos).match(/^[A-Z][a-zA-Z0-9_']*/);
  pos += m[0].length; ws();
  return Store.put('freevar', ['_' + m[0]]);
}

// 3. Application: after parsing an atom, if next token is also
//    an atom (not an operator, not ')', not '.'), it's application.
//    Collect spine, flatten: atom(head) + args → Store.put(head, args)
```

Application is handled by adding a high-precedence "juxtaposition" rule to `parseExpr`: after parsing a primary, if the next token is another primary (not an operator), it's left-associative application. This is standard Pratt parser technique.

Arrow (`->`) and forward rule (`-o { }`) are added to parserTables as structural operators, or handled as special cases in `parseExpr`.

These extensions are **calculus-independent** — they're the framework's ambient term language. Any calculus loaded into CALC gets application, numbers, and freevars for free.

**Layer 2 — Meta-syntax wrapper** (~60 lines):

```javascript
// lib/engine/parse-ill.js
// Delegates expression parsing to the calculus-generated parser.

function parseILLFile(source, exprParser) {
  let pos = 0;
  const types = new Map(), clauses = new Map();
  const forwardRules = [], queries = new Map();

  while (pos < source.length) {
    skipWS();
    if (atEnd()) break;
    if (peek('%')) { skipLine(); continue; }
    if (peek('#')) { parseQueryOrImport(); continue; }
    parseDeclaration();
  }

  return { types, clauses, forwardRules, queries };
}
```

Each declaration extracts the text between `:` and `.` (or `<-`), then calls the generated expression parser on that substring. No precedence logic in the wrapper — all operator handling is in the calculus-generated parser.

### Why This Is Better Than a Hand-Written Parser

1. **Calculus-derived**: Operator precedence and associativity come from ill.calc `@prec`/`@assoc` annotations. Change the calculus, and the parser updates automatically.
2. **Single source of truth**: The browser, prover, rules parser, and now the engine all use the same generated parser tables. No divergence risk.
3. **Already tested**: `buildParserFromTables` is in production (browser UI, sequent parsing). Only the extensions (application, numbers) are new code.
4. **Minimal new code**: ~30 lines of extensions to builders.js + ~60 lines meta-syntax wrapper. Compare to tree-sitter: grammar.js (192 lines) + WASM binary (11 KB) + cst-to-ast.js integration.

### Impact

```
WITHOUT calculus-generated parser (Opt_A only):
  User program: 12ms tree-sitter + 8ms Store.put = 20ms

WITH calculus-generated parser (Opt_A + Opt_B):
  User program: ~1ms parse+Store.put (fused, no WASM) = ~1ms
  SDK restore:                                           3ms
  ───
  TOTAL SETUP:                                         ~4ms
  + explore:                                             9ms
  TOTAL END-TO-END:                                   ~13ms  (vs hevm 52ms = 4× faster)
```

The fused parse eliminates both the 11ms tree-sitter WASM overhead AND the separate AST conversion pass.

### Scope

Replace tree-sitter for `.ill` files only. The meta-parser (`cst-to-ast.js`) keeps tree-sitter for `.calc`/`.family` files — those are parsed at build time only (`npm run build:bundle`), and tree-sitter's error reporting is valuable there.

```
lib/engine/convert.js  →  uses calculus-generated parser  (runtime, .ill files)
lib/meta-parser/        →  keeps tree-sitter               (build time, .calc files)
```

## TODO_0060.Opt_C — Precompile Rules Too

`compileRule()` is deterministic: same raw rule → same compiled rule. The compiled rules contain Maps (`metavarSlots`, `linearMeta`, `existentialGoals`) and arrays, but no closures — all are serializable with a custom encoder.

Store the compiled rules in the binary alongside the Store snapshot. Saves 2.4ms. Combined with Opt_A + Opt_B: total setup ~1.5ms.

This is low priority — 2.4ms is small relative to explore()'s 9ms.

## Implementation Plan

### Stage 1: Store.snapshot/restore + binary format

Files to modify:
- `lib/kernel/store.js` — add `snapshot()`, `restore()` exports
- `lib/engine/index.js` — add `precompile()`, `loadPrecompiled()` API
- `lib/hash.js` — already has FNV-1a (use for cache key)

New files:
- `lib/engine/store-binary.js` — binary serialization/deserialization (~100 lines)
- `tools/precompile.js` — CLI: `node tools/precompile.js evm.ill → out/cache/<hash>.bin`

### Stage 2: Incremental loading

Files to modify:
- `lib/engine/convert.js` — `resolveImports()` skip directive for precompiled imports
- `lib/engine/index.js` — `load()` checks cache before full parse

### Stage 3: Calculus-generated .ill parser

Files to modify:
- `lib/calculus/builders.js` — extend `buildParserFromTables` with application, numbers, multi-char freevars, arrow, forward-rule syntax (~30 lines)

New files:
- `lib/engine/parse-ill.js` — meta-syntax wrapper (~60 lines): declarations, imports, queries, comments. Delegates expression parsing to the extended calculus-generated parser.

Files to modify:
- `lib/engine/convert.js` — replace `mdeParser.parse()` with `parseILLFile()`
- `lib/engine/convert.js` — remove `require('../tree-sitter-mde')` for .ill path

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
    // string table, bigint table as separate slices
};

fn loadSnapshot(data: []const u8) StoreSnapshot {
    const header = @ptrCast(*const Header, data.ptr);
    const n = header.nodeCount;
    return .{
        .tags = data[12..][0..n],
        .arities = data[12 + n ..][0..n],
        .child0 = @ptrCast([*]const u32, @alignCast(4, data[12 + 2*n ..].ptr))[0..n],
        // ...
    };
}
```

No JSON parsing, no object allocation, no GC pressure. Just pointer arithmetic into memory-mapped file. The SoA layout means cache-friendly iteration over any single field (e.g., scan all tags without touching children).

## Tree-sitter: Keep or Replace?

**Keep for .calc/.family files** (build-time only, meta-parser path):
- Error messages for calculus definition syntax
- `@annotations` and `@extends` chain resolution
- Only runs during `npm run build:bundle`
- Performance irrelevant (one-time)

**Replace for .ill files** (runtime, engine path):
- The calculus-generated Pratt parser already handles all connectives
- Extending it for application/numbers/freevars is ~30 lines
- 11ms WASM overhead is 78% of user-program parse time
- Direct-to-Store single pass eliminates intermediate CST allocation
- Same parser tables used everywhere (browser, prover, rules, engine)

## Projected Timeline

| Stage | Savings | Cumulative setup | Effort |
|---|---|---|---|
| **Baseline** | — | 51ms | — |
| **Stage 1**: Store binary + precompile SDK | −34ms | 17ms | ~200 lines |
| **Stage 2**: Incremental loading | −2ms | 15ms | ~50 lines |
| **Stage 3**: Calculus-generated .ill parser | −11ms | 4ms | ~90 lines (30 ext + 60 wrapper) |
| **Stage 4**: Precompile rules (Opt_C) | −2.4ms | 1.6ms | ~80 lines |

End state: **1.6ms setup + 9.2ms explore = 10.8ms total** (vs hevm 52ms = **4.8× faster**).
