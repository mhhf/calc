# Loader & Precompile

## Public API (`lib/engine/index.js`)

```js
const mde = require('./lib/engine');

// Auto-cached load (default) — content-hash keyed, two-tier cache
const calc = mde.load('program.ill');

// Cache imports only — SDK cached, top file parsed fresh each time
const calc = mde.load('program.ill', { cache: 'imports' });

// No caching
const calc = mde.load('program.ill', { cache: false });

// Custom cache directory (default: os.tmpdir()/calc-cache/)
const calc = mde.load('program.ill', { cacheDir: '/tmp/my-cache' });

// Explicit precompile — writes binary cache to specific path
mde.precompile('program.ill', '/tmp/program.bin');

// Load from precompiled binary
const calc = mde.loadPrecompiled('/tmp/program.bin');
```

All paths return the same **calc context**:

```
{ types: Map<name, hash>,
  clauses: Map<name, { hash, premises }>,
  queries: Map<name, hash>,
  forwardRules: CompiledRule[],
  prove(goal, opts),
  exec(state, opts) }
```

## Data Flow

```mermaid
graph LR
  A[".ill source"] -->|resolveImports| B["flat source"]
  B -->|parseDeclarations + Earley| C["Store entries + decl list"]
  C -->|classify| D["types / clauses / forwardRules / queries"]
  D -->|compileRule| E["CompiledRule[]"]
  D -->|buildIndex| F["backwardIndex"]
  E --> G["calc context"]
  F --> G
```

### Source load path (`convert.load`)

1. **`resolveImports`** — inline `#import(path)` directives recursively (dedup via Set)
2. **`parseDeclarations`** — split source into name/body/premise declarations
3. **`_exprParser`** (Earley) — parse each body/premise to content-addressed Store hash
4. **Classify** — `hasMonad(hash)` → forward rule, has premises → clause, else → type

### Precompiled load path (`loadPrecompiled`)

1. **`fs.readFileSync`** → raw Buffer
2. **`deserialize`** → snapshot object (SoA arrays + metadata JSON)
3. **`Store.restore`** — bulk memcpy arrays, rebuild DEDUP/string/bigint tables, restore dynamic tags
4. **`_deserializeCompiledRules`** — convert Array fields back to Set (freevars, persistentDeps)
5. **`_buildCalc`** — build backward index, return calc context

## Binary Format (`lib/engine/store-binary.js`)

Little-endian, CRC32-checked. ~65 KB for multisig program.

| Section | Layout |
|---|---|
| Header (20B) | magic `CALC` (u32), version (u16), endian (u8), reserved (u8), nodeCount (u32), strCount (u32), bigCount (u32) |
| SoA arrays | tags (u8[N]), arities (u8[N]), padding to 4B align, child0..3 (u32[N] each) |
| DEDUP | hashes (u32[N]) — content hash per node for rebuilding DEDUP map |
| Strings | per entry: length (u16) + utf8 bytes |
| BigInts | per entry: sign (u8) + byteLen (u16) + LE bytes |
| Tag registry | tagCount (u16), per tag: nameLen (u16) + utf8 |
| Metadata | metaLen (u32) + JSON bytes (types, clauses, forwardRules, compiledRules, queries) |
| Footer (4B) | CRC32 of everything above |

## Store Snapshot/Restore (`lib/kernel/store.js`)

**`snapshot(metadata)`** — copies SoA slices (1-based → 0-based), precomputes DEDUP hashes, copies string/bigint/tag tables. Returns plain object ready for `serialize()`.

**`restore(data)`** — clears dynamic tags (>= `PRED_BOUNDARY`), re-registers snapshot tags, bulk memcpy into SoA arrays, rebuilds DEDUP map + string/bigint tables. O(N) where N = nodeCount.

Content-addressing is preserved: `Store.put(tag, children)` after restore returns the same ID as before snapshot.

## Compiled Rules in Cache

Forward rules are compiled (`compile.js`) at cache-write time and stored in metadata JSON. This avoids recompilation on load (~2.4ms saved).

**Gotcha — Set serialization**: `linearMeta[p].freevars` and `.persistentDeps` are JavaScript `Set` objects. `JSON.stringify(new Set(...))` produces `{}`, silently dropping entries. The `_serializeCompiledRules`/`_deserializeCompiledRules` helpers convert Set↔Array at the serialization boundary.

## Import Resolution

`resolveImports(source, basePath)` inlines `#import(path)` directives recursively. A `Set` of resolved absolute paths prevents circular imports.

Import chain example: `multisig.ill → evm.ill → bin.ill`.

`loadFile` accepts `opts.alreadyImported` — a pre-populated Set of paths to skip during import resolution. Used by auto-caching to avoid re-parsing cached imports.

## Auto-Caching

`load()` uses content-hash keyed two-tier caching by default. Cache files are stored in `os.tmpdir()/calc-cache/` (survives session, cleared on reboot).

### Cache key: recursive content hash

Each file's hash includes its source text and transitive dependency hashes:

```
fileHash(bin.ill)  = hashString(source)
fileHash(evm.ill)  = hashCombine(hashString(source), fileHash(bin.ill))
fullHash           = hashCombine(hashString(multisig.ill), fileHash(evm.ill), ...)
importsHash        = hashCombine(sorted top-level import fileHashes)
```

Change any source file → all downstream hashes change → stale caches never loaded.

### Two-tier cache

| File | Purpose |
|---|---|
| `<fullHash>.bin` | Full program snapshot (all files) |
| `<importsHash>.bin` | SDK-only snapshot (top-level imports + transitive deps) |

**Top-level imports** = `#import` directives before any declarations. Inline imports (e.g. `#import(code.ill)` inside `#symex`) are part of the top file.

### Load paths (cache: true)

1. **Full cache hit** → `loadPrecompiled(fullHash.bin)` (~2.6ms)
2. **Imports cache hit** → restore SDK, parse top file on top, write full cache (~3ms)
3. **Double miss** → parse SDK bottom-up → snapshot imports cache, parse top file → snapshot full cache (~11ms + ~1ms write)

### cache: 'imports'

Same as above but never writes full cache. Top file always parsed fresh. Useful for benchmarking user programs against a cached SDK.

### Incremental loading after SDK restore

After `Store.restore(sdkSnapshot)`, Store has IDs 1..N. User program calls `Store.put()` → allocates N+1..M. Content-addressing ensures same (tag, children) → same ID via DEDUP. No conflicts. Only new forward rules need `compileRule()`.

### Edge cases

- **Corrupted cache**: CRC32 check fails → delete stale file → fallback to fresh parse
- **Concurrent writes**: deterministic (same source → same content), last writer wins
- **No imports**: single-tier cache only, `cache: 'imports'` degrades to `cache: false`

## Performance (multisig_nocall_solc_symbolic, 689 nodes, warm)

| Path | Load | Explore | Total |
|---|---|---|---|
| Source (Earley parser) | ~13.5ms | ~10ms | ~23.5ms |
| Auto-cache hit (full) | ~2.6ms | ~10ms | ~12.6ms |
| Auto-cache hit (imports) | ~3ms | ~10ms | ~13ms |
| Explicit precompiled | ~2.6ms | ~10ms | ~12.6ms |
| Before (tree-sitter) | ~51ms | ~10ms | ~61ms |
