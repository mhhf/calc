---
title: "Compose Disk Cache"
created: 2026-04-17
modified: 2026-04-17
summary: Per-file content-addressed disk cache for post-compose Store arenas — 10× cold load on multisig symex.
tags: [performance, optimization, engine, symbolic-execution, implementation]
---

# Compose Disk Cache

Per-file, content-addressed cache for compose-stage results (fused rules, specialized rules, tabling closures). Targets the ~200ms load overhead for multisig symbolic-exec programs.

## Activation

The compose cache is **opt-in**. Four equivalent ways to enable it:

| Form | Example | Notes |
|---|---|---|
| Option sugar | `mde.load(p, { cache: 'compose' })` | recommended |
| Verify mode | `mde.load(p, { cache: 'verify' })` | cold + cached + diff (for audits) |
| Legacy option | `mde.load(p, { composeDiskCache: dir })` | back-compat; `true` = default dir |
| Env flag | `CALC_COMPOSE_CACHE=1 node ...` | process-wide enable |

Disable:
- `cache: false` or `CALC_CACHE=0` — overrides everything else.
- `composeDiskCache: false` — overrides the compose-specific options.

## Cache directory

Lookup order (first match wins):

1. `composeDiskCache` option (if string)
2. `opts.cacheDir`
3. `CALC_CACHE_DIR` env var
4. `~/.cache/calc/snapshots` (default)

## Cache key

```
sha256(
  'ev=' + engineVersion()     // content-hash of lib/**/*.js
  + ';file=' + treeHash       // import-tree content hash
  + [';bc=' + sha256(bcHex)]  // only if { bytecode } was passed
  + ';' + cacheFlagFingerprint(opts)  // env flags + opt-affecting fields
  + ';v=' + COMPOSE_DISK_VERSION
)[:16]
```

Key-affecting env flags (registry in `lib/engine/cache-flags.js`):
- `CALC_POOL_DISJOINT` ('0' disables the pool-disjoint invariant for A/B; 'strict' adds rename-site asserts)

Key-affecting options: `fuseBasicBlocks`, `cacheVersion`.

## Bytecode API

Pass `bytecode: '0x...'` to `mde.load()` instead of `extraGrade0Facts` + `scopeGuard`:

```js
mde.load('program.ill', {
  cache: 'compose',
  bytecode: '0x6080604052...',
  fuseBasicBlocks: true
});
```

The two APIs are mutually exclusive — passing both throws. Under the hood `bytecode` calls `loadBytecode()` and plugs in `bytecodeArrGetGuard`; the raw hex also participates in the cache key.

## Atomic writes

`_saveCSnap` writes to `compose-<key>.bin.tmp.<pid>-<rand>` then `fs.renameSync` to the final path. Torn writes are impossible on a POSIX filesystem; concurrent writers just clobber atomically.

## Verify mode

`cache: 'verify'` (or `CALC_CACHE_VERIFY=1`) runs the cold path, writes the cache, then replays from the cache and diffs forward-rule names. Any divergence throws loudly. Use this on CI to guard against compose-result drift.

## LRU eviction & format migration

`lib/engine/cache-evict.js`:

- `ensureVersionTag(dir, version)` writes `version.txt` on first use. If the tag is missing or mismatched, wipes all `compose-*.bin` entries (leaves unrelated files alone) before writing the new tag. Engine version is the content hash of `lib/**/*.js`, so code changes auto-invalidate stale caches.
- `lruEvict(dir, maxBytes)` ranks `compose-*.bin` by `atimeMs`; if total size exceeds the budget, deletes oldest-first until under budget. Default budget: 256 MB. Override with `opts.cacheMaxBytes`.

Both run best-effort: any IO error leaves the cache as-is. Correctness never depends on eviction; the cache key is authoritative.

## Measured performance

Benchmark: `multisig_nocall_solc_symbolic.ill` (see `/tmp/calc-p4-bench.js`).

| Metric | Value |
|---|---|
| Cold miss | ~155 ms |
| Cache hit (median of 5) | ~16 ms |
| Speedup | ~9.8× |

Comfortably under the TODO_0218 target of 40 ms cold load.

## What is **not** cached

The compose cache stores the post-compose Store arena plus rule/definition metadata. It does **not** cache:

- Downstream specialization/fusion/tabling artefacts produced after `load()` (if ever reinvoked differently)
- Exploration results, witness traces, or proof search state
- The backward prover's proof caches

A cache hit on a file-that-was-cached skips parser + converter + composer entirely; everything downstream reruns per call.

## Files

| Path | Role |
|---|---|
| `lib/engine/index.js` | `load()` entry, cache key, save/load, verify mode |
| `lib/engine/engine-version.js` | Content hash of `lib/**/*.js` |
| `lib/engine/cache-flags.js` | Registry of cache-affecting env + opt flags |
| `lib/engine/cache-evict.js` | `ensureVersionTag`, `lruEvict` |
| `lib/engine/cache/store-binary.js` | `serialize`/`deserialize`/`compact` of Store arena |

## Related

- `TODO_0218` — this cache's spec (phases 0–7)
- `doc/documentation/content-addressed-store.md` — Store arena layout that gets serialized
