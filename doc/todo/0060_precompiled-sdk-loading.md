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

## TODO_0060.Opt_B — Hand-Written .ill Parser

### Why Tree-sitter Is Overkill

The .ill grammar (`lib/tree-sitter-mde/grammar.js`) has **23 rules** with 6 precedence levels. Tree-sitter provides error recovery, incremental parsing, and syntax highlighting — **none of which are used**. The CST is consumed in a single linear walk by `convertExpr()` which calls `Store.put()` directly.

Tree-sitter adds:
- 11ms fixed WASM VM overhead per parse call (dominates for small inputs)
- 11 KB WASM binary dependency
- Async initialization (`TreeSitter.Parser.init()`)
- WASM rebuild required after grammar changes (`npm run build:ts:wasm`)

### .ill Syntax (Complete)

```
program     ::= (declaration | query | import | comment)*
declaration ::= name ':' expr ('<-' expr)* '.'
query       ::= '#' identifier expr '.'
import      ::= '#import(' path ')'
comment     ::= '%' .* '\n'

expr        ::= plus ('->' expr | '-o' expr | '-o' '{' expr '}')
              | 'exists' VAR '.' expr
              | 'forall' VAR '.' expr
              | plus
plus        ::= with ('+' with)*
with        ::= tensor ('&' tensor)*
tensor      ::= bang ('*' bang)*
bang        ::= '!' bang | app
app         ::= atom+ (left-associative application)
atom        ::= IDENT | VAR | NUMBER | '(' expr ')'

name        ::= (IDENT | VAR) ('/' (IDENT | VAR | DIGIT+))*
IDENT       ::= [a-z_][a-zA-Z0-9_']*
VAR         ::= [A-Z][a-zA-Z0-9_']*
NUMBER      ::= [0-9]+ | 0x[0-9a-fA-F]+
```

This is a textbook operator-precedence grammar. Hand-written recursive descent: **~150 lines**.

### Design: Direct-to-Store Parser

```javascript
// lib/engine/parse-ill.js (~150 lines)
// Single-pass: source text → Store.put() calls. No intermediate CST.

function parseILL(source) {
  let pos = 0;
  const types = new Map(), clauses = new Map();
  const forwardRules = [], queries = new Map();

  while (pos < source.length) {
    skipWhitespaceAndComments();
    if (pos >= source.length) break;
    if (source[pos] === '#') { parseDirective(); continue; }
    parseDeclaration();
  }

  return { types, clauses, forwardRules, queries };
}

function parseExpr() { return parseArrow(); }

function parseArrow() {
  let left = parsePlus();
  if (match('->'))  return Store.put('arrow', [left, parseArrow()]);
  if (match('-o')) {
    if (match('{')) {
      const body = parseExpr(); expect('}');
      return Store.put('loli', [left, Store.put('monad', [body])]);
    }
    return Store.put('loli', [left, parseArrow()]);
  }
  return left;
}

function parsePlus() {
  let left = parseWith();
  while (match('+')) left = Store.put('oplus', [left, parseWith()]);
  return left;
}
// ... 5 more precedence levels, each ~5 lines
```

**Key advantage**: no intermediate CST allocation. Source bytes → Store entries in one pass.

### Impact

```
WITHOUT hand-written parser (Opt_A only):
  User program: 12ms parse + 8ms Store.put = 20ms

WITH hand-written parser (Opt_A + Opt_B):
  User program: 1ms parse+Store.put (fused) = 1ms
  SDK restore:                                 3ms
  ───
  TOTAL SETUP:                                ~4ms
  + explore:                                   9ms
  TOTAL END-TO-END:                          ~13ms  (vs hevm 52ms = 4× faster)
```

The fused parse eliminates both the 11ms tree-sitter WASM overhead AND the separate AST conversion pass.

### Scope

Replace tree-sitter for `.ill` files only. The meta-parser (`cst-to-ast.js`) uses tree-sitter for `.calc`/`.family` files — keep those. `.calc` files are only parsed at build time (`npm run build:bundle`), not at runtime.

```
lib/engine/convert.js  →  uses new parseILL()  (runtime, .ill files)
lib/meta-parser/        →  keeps tree-sitter    (build time, .calc files)
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

### Stage 3: Hand-written .ill parser

New files:
- `lib/engine/parse-ill.js` — recursive descent parser (~150 lines)

Files to modify:
- `lib/engine/convert.js` — replace `mdeParser.parse()` with `parseILL()`
- `lib/engine/convert.js` — remove `require('../tree-sitter-mde')` for .ill path

### Stage 4: Benchmark & comparison update

Files to modify:
- `benchmarks/engine/symexec-bench.js` — add precompiled-load variant
- `tools/hevm-bench.sh` — use precompiled SDK for fair comparison
- `doc/documentation/calc-vs-hevm.md` — honest numbers with setup cost

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
- Trivial grammar (6 precedence levels, ~150 LOC parser)
- No error recovery needed (trusted input from our own tool chain)
- No incremental parsing needed (single full parse)
- 11ms WASM overhead is 78% of user-program parse time
- Direct-to-Store single pass eliminates intermediate CST allocation

## Projected Timeline

| Stage | Savings | Cumulative setup | Effort |
|---|---|---|---|
| **Baseline** | — | 51ms | — |
| **Stage 1**: Store binary + precompile SDK | −34ms | 17ms | ~200 lines |
| **Stage 2**: Incremental loading | −2ms | 15ms | ~50 lines |
| **Stage 3**: Hand-written .ill parser | −11ms | 4ms | ~150 lines |
| **Stage 4**: Precompile rules (Opt_C) | −2.4ms | 1.6ms | ~80 lines |

End state: **1.6ms setup + 9.2ms explore = 10.8ms total** (vs hevm 52ms = **4.8× faster**).
