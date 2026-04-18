# Runtime Evaluation: node vs bun

Cold-start benchmark for the CALC engine across JavaScript runtimes and bun
build modes. Harness: `tools/bench-runtime.js`. Probe workload: load
`multisig_nocall_solc_symbolic.ill` + bytecode facts, decompose `symex` query,
run `explore`.

Most recent run: 2026-04-18, after TODO_0219 Phase 6 (ESM migration + bun
feature detection + bunfig).

## Setup

- **node**: 22.22.0 (`/nix/store/cv3yxgf7zp70wk8d8lg5zi84lg35nyxs-nodejs-22.22.0/bin/node`)
- **bun**: 1.3.11 (`/nix/store/4b7jvqsqywnsb273svingfmpqschkszi-bun-1.3.11/bin/bun`)
- runs=7, warmup=2 per config
- cache-hit column uses a primed `CALC_CACHE_DIR` with `CALC_COMPOSE_CACHE=1`
- cold column has no compose cache

## Results

| config                     | cold wall | cold load | cold explore | cache-hit wall |
| -------------------------- | --------: | --------: | -----------: | -------------: |
| node + unbundled           |     168ms |      42ms |         58ms |          137ms |
| **bun + unbundled**        | **128ms** |  **42ms** |     **35ms** |      **115ms** |
| bun + bundled (`--target=bun`) | 124ms | 41ms | 38ms |              — |
| bun `--compile`            |     120ms |      40ms |         35ms |              — |
| bun `--compile --bytecode` |     108ms |      35ms |         33ms |           78ms |

Relative to **node + unbundled** cold wall:
- bun + unbundled:         **−40ms (−24%)**
- bun + bundled:            −44ms (−26%)
- bun `--compile`:          −48ms (−28%)
- bun `--compile --bytecode`: −60ms (−36%)

## Findings

### Post-ESM, bun's unbundled lead widened

The Phase 0 snapshot (pre-ESM, CJS sources) showed bun unbundled at 145ms cold
— a −15% gap to node. Post-ESM with static `import` chains throughout, that
gap widens to −24%. Bun's ESM loader is faster than node's, and the load path
is simpler (no CJS↔ESM bridging).

The explore hot loop dropped from 58ms (node) to 35ms (bun) — a 40% speedup
that holds independent of runtime startup. JSC's monomorphic paths outperform
V8 on this workload.

### The ≤80ms goal is achievable — but only with `--compile --bytecode`

Cache-hit wall-time for `bun --compile --bytecode`: **78ms**. This mode is
the only configuration measured to cross the original TODO_0219 target floor.
The cost: a ~99 MB self-contained binary.

For unbundled invocation (the production default after Phase 1), cache-hit is
115ms — a 22ms improvement over node's 137ms, but well above the 80ms target.
The residual is spawn + runtime init (~40ms) + module resolution (~35ms) +
compose-cache read (~20-30ms), none of which the runtime choice alone changes.

### Bundled and `--compile` modes break engine-version hashing

`lib/engine/engine-version.js` walks `path.resolve(import.meta.dirname, '..')`
to content-hash `lib/**/*.js` for the compose-cache key. Under bundled or
plain `--compile`, that path does not resolve to the calc source tree:

- **bundled**: `import.meta.dirname` is `/tmp/calc-bench-runtime/`; the walk
  hits `/tmp/systemd-private-*` with EACCES.
- **`--compile`**: resolves to `/$bunfs` (virtual FS), which `readdirSync`
  cannot scan (ENOENT).
- **`--compile --minify --bytecode`**: works — minification eliminates or
  inlines the failing walk at bundle time.

The cache-hit column shows "—" for configs where the walk fails. The cold
column works because `engineVersion()` is only computed when
`CALC_COMPOSE_CACHE=1` is set. Unbundled `bun` (the production path) is
unaffected: `import.meta.dirname` points into the real `lib/engine/` tree.

### The unbundled cache-hit floor is ~115ms

Unbundled bun cache-hit: 115ms. Breakdown (approximate):
- spawn + bun runtime init: ~35ms
- module resolution/parse (17 top-level imports): ~35ms
- compose-cache read + deserialize: ~25ms
- decompose + explore: ~20ms

Shrinking this further requires moving work off the spawn path (resident
daemon), shrinking the compose-cache payload (TODO_0218), or cutting top-level
imports in `lib/engine/index.js` (lazy load).

## Implications for bun migration (TODO_0219)

- **Adopt unbundled bun as the invocation runtime** (Phase 1, landed). Zero
  code changes, 40ms off cold wall, 22ms off cache-hit wall.
- **Do NOT ship `--compile --bytecode` as production binary.** It hits the
  ≤80ms target, but the 99 MB artifact and engine-version fragility (only
  `--minify --bytecode` works; plain `--compile` breaks) are disqualifying.
- **ESM migration (Phase 2) paid off.** Post-ESM numbers are strictly better
  than the Phase 0 CJS baseline across all configurations.
- **Engine-version walk is a latent bundled/compiled bug.** If we ever want
  bundled deployment with compose cache, `engine-version.js` needs a fallback
  hash for contexts where `lib/` is not on disk. Tracked as follow-up.
- **Any further startup gain must come from shrinking the work itself** —
  lazier imports in `lib/engine/index.js`, smaller compose-cache payload
  (TODO_0218), or shifting symex to a resident process.

## Per-workload numbers

Real tooling invocations (wall time, 3-run median):

| workload                                     | node  | bun   | gap          |
| -------------------------------------------- | ----: | ----: | -----------: |
| `libexec/calc-bundle` (build:bundle script)  |  56ms |  40ms | −16ms (−29%) |

## Dual-runtime test harness

- `npm test`          → node `--test`  — 2471 pass / 0 fail, ~27s wall
- `npm run test:bun`  → `tools/test-bun.sh` (xargs -P8 per-file) — 87/87 pass, ~11s wall

Per-file invocation is required for bun: bun runs all test files in a single
process, which leaks module-scope state (Store arena, parser caches) across
files. `tools/test-bun.sh` matches node's per-file isolation model.

## Re-running the benchmark

```bash
# Primary measurement (all configs, 7 runs each):
BUN_BIN=$(which bun) node tools/bench-runtime.js --runs=7 --warmup=2

# skip rebuilds of bundled/compiled artifacts (uses cache in /tmp):
node tools/bench-runtime.js --runs=7 --warmup=2 --skip-build

# machine-readable:
node tools/bench-runtime.js --runs=7 --json
```
