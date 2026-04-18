#!/usr/bin/env node
/**
 * Benchmark History — explore solc_symbolic across N commits.
 *
 * Benchmarks the last N commits (via git worktrees) running two scenarios:
 *   - symex: explore.explore() on a pre-loaded state (hot path only)
 *   - e2e:   load + decomposeQuery + explore, each iteration in a FRESH Node
 *            subprocess so the Store hash-cons table, lazy-built expression
 *            parser, module require cache, and V8 JIT all start cold. This is
 *            the true "first-invocation" cost users pay — not the warm re-parse
 *            cost you'd get running the load loop in a single process.
 *
 * Usage:
 *   node --expose-gc tools/bench-history.js [--commits=50] [--runs=21] [--warmup=10]
 *
 * Options:
 *   --commits=N      Number of commits to benchmark (default: 50)
 *   --runs=N         Symex timed runs per benchmark (default: 21)
 *   --warmup=N       Symex warmup runs before timing (default: 10)
 *   --e2e-runs=N     E2E timed runs per benchmark (default: 5, each a fresh Node process)
 *   --e2e-warmup=N   E2E warmup runs (fresh processes, prime OS page cache) (default: 2)
 *   --no-e2e         Disable end-to-end benchmark (symex only)
 *   --branch=REF     Branch/ref to walk (default: HEAD)
 *   --resume=FILE    Resume from partial results JSON file
 *   --out=FILE       Write results JSON to file
 *
 * Examples:
 *   node --expose-gc tools/bench-history.js --commits=20
 *   node --expose-gc tools/bench-history.js --commits=50 --runs=30 --warmup=10
 *   node --expose-gc tools/bench-history.js --branch=main --commits=30
 *   node --expose-gc tools/bench-history.js --resume=bench-history.json --commits=60
 */

const { execSync, spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const { performance } = require('perf_hooks');

const ROOT = path.resolve(__dirname, '..');
const WORKTREE_DIR = path.join(ROOT, '.bench-history');
const MARKER = '---BENCH-HISTORY---';

// ─── Arg parsing ──────────────────────────────────────────────────────────────

function parseArgs() {
  const args = process.argv.slice(2);
  let commits = 50;
  let runs = 21;
  let warmup = 10;
  let e2eRuns = 5;
  let e2eWarmup = 2;
  let e2eEnabled = true;
  let branch = 'HEAD';
  let resume = null;
  let out = null;

  for (const arg of args) {
    if (arg.startsWith('--commits=')) commits = parseInt(arg.slice(10), 10);
    else if (arg.startsWith('--runs=')) runs = parseInt(arg.slice(7), 10);
    else if (arg.startsWith('--warmup=')) warmup = parseInt(arg.slice(9), 10);
    else if (arg.startsWith('--e2e-runs=')) e2eRuns = parseInt(arg.slice(11), 10);
    else if (arg.startsWith('--e2e-warmup=')) e2eWarmup = parseInt(arg.slice(13), 10);
    else if (arg === '--no-e2e') e2eEnabled = false;
    else if (arg.startsWith('--branch=')) branch = arg.slice(9);
    else if (arg.startsWith('--resume=')) resume = arg.slice(9);
    else if (arg.startsWith('--out=')) out = arg.slice(6);
  }

  return { commits, runs, warmup, e2eRuns, e2eWarmup, e2eEnabled, branch, resume, out };
}

// ─── Git helpers ──────────────────────────────────────────────────────────────

function getCommitList(branch, count) {
  const log = execSync(
    `git log --format="%H %h %ai %s" -n ${count} "${branch}" --`,
    { cwd: ROOT, encoding: 'utf8' }
  ).trim();

  if (!log) return [];

  return log.split('\n').map(line => {
    const [fullHash, shortHash, ...rest] = line.split(' ');
    // rest is: date time tz subject...
    // date format: 2026-03-21 12:34:56 +0100
    const date = rest[0];
    const subject = rest.slice(3).join(' ');
    return { fullHash, shortHash, date, subject };
  });
}

// ─── Store hash collision workaround ──────────────────────────────────────────
// Between 03dceb2 and 64370df, a hex literal in to256 (bin.ill) combined with
// arr.ill predicates causes FNV-1a hash collisions that corrupt the symex query.
// The specific collisions are environment-dependent (insertion order varies by
// Node.js build). Patching .ill content or tag IDs is fragile. Instead, we
// change the FNV offset basis in lib/hash.js — this shifts the entire hash
// landscape without altering any tag IDs, term semantics, or code paths.

function patchHashSeed(wtPath) {
  const hashJs = path.join(wtPath, 'lib/hash.js');
  try {
    if (!fs.existsSync(hashJs)) return;
    const content = fs.readFileSync(hashJs, 'utf8');
    // Only patch if using the standard FNV offset and collision is possible
    if (!content.includes('0x811c9dc5')) return;
    // Check if this commit's store.js already has metavar (collision-free)
    const storeJs = path.join(wtPath, 'lib/kernel/store.js');
    if (fs.existsSync(storeJs)) {
      const storeContent = fs.readFileSync(storeJs, 'utf8');
      if (storeContent.includes("'metavar'")) return;
    }
    // Change FNV offset basis: 0x811c9dc5 → 0x811c9dc6 (shifts all hashes)
    fs.writeFileSync(hashJs, content.replace('0x811c9dc5', '0x811c9dc6'));
  } catch {}
}

// ─── Worktree management ──────────────────────────────────────────────────────

function setupWorktree(fullHash) {
  const wtPath = path.join(WORKTREE_DIR, fullHash.slice(0, 12));

  if (fs.existsSync(wtPath)) {
    try {
      execSync(`git worktree remove --force "${wtPath}"`, { cwd: ROOT, stdio: 'ignore' });
    } catch {}
  }

  fs.mkdirSync(WORKTREE_DIR, { recursive: true });
  execSync(`git worktree add "${wtPath}" ${fullHash} --detach`, {
    cwd: ROOT, stdio: 'ignore',
  });

  // Symlink node_modules
  const nmDst = path.join(wtPath, 'node_modules');
  if (!fs.existsSync(nmDst)) {
    fs.symlinkSync(path.join(ROOT, 'node_modules'), nmDst);
  }

  // Workaround: commits 03dceb2..64370df have a Store hash collision triggered
  // by the hex literal in to256 (bin.ill) combined with arr.ill predicates.
  // Shift the FNV hash seed to avoid environment-dependent collisions.
  patchHashSeed(wtPath);

  return wtPath;
}

function cleanupWorktree(fullHash) {
  const wtPath = path.join(WORKTREE_DIR, fullHash.slice(0, 12));
  try {
    if (fs.existsSync(wtPath)) {
      execSync(`git worktree remove --force "${wtPath}"`, { cwd: ROOT, stdio: 'ignore' });
    }
  } catch {}
}

function cleanupAll() {
  try {
    if (fs.existsSync(WORKTREE_DIR)) {
      const entries = fs.readdirSync(WORKTREE_DIR);
      for (const e of entries) {
        const p = path.join(WORKTREE_DIR, e);
        try {
          execSync(`git worktree remove --force "${p}"`, { cwd: ROOT, stdio: 'ignore' });
        } catch {}
      }
      try { fs.rmdirSync(WORKTREE_DIR); } catch {}
    }
  } catch {}
}

// ─── Benchmark runner (inline script written to worktree) ─────────────────────
//
// Two-layer subprocess design:
//   Layer 1 (this bench-history.js main process) spawns a runner script per commit.
//   Layer 2 (runner, below) runs symex in-process and spawns a further child per
//   e2e iteration so each e2e measurement starts from a cold Node process.
//
// Why layer 3 (the e2e child) exists:
//   `{ cache: false }` in mde.load() routes to _loadFresh, which does NOT call
//   Store.clear(). The module-level hash-cons DEDUP map, lazy-built expression
//   parser, module require cache, V8 JIT, and OS page cache all stay hot across
//   iterations in a single process. A warm in-process e2e underestimates true
//   cold-start by ~25x (8ms vs ~200ms on solc_symbolic). A fresh subprocess
//   guarantees every iteration starts truly cold. The cost of fork+startup is
//   NOT included in the reported time — the child times just load+decompose+
//   explore internally and prints the result.

// Source of the innermost e2e child script. Defined as a regular string so
// JSON.stringify can handle escaping (notably the `\s` in the bytecode regex)
// when embedding this into the runner script template.
const E2E_CHILD_SOURCE = `'use strict';
// Runs exactly ONE e2e iteration from a cold Node process:
//   load(sourcePath, { cache: <mode>, onPhase, extraGrade0Facts, scopeGuard })
//   decomposeQuery(symex)
//   explore()
//
// Cache mode is selected by env (all four scenarios reuse the same child):
//   BENCH_CACHE_MODE=nocache     → cache:false             (no compose cache r/w)
//   BENCH_CACHE_MODE=cache-miss  → CALC_COMPOSE_CACHE=1    (cache dir pre-wiped
//                                                           by parent → cold build)
//   BENCH_CACHE_MODE=cache-hit   → CALC_COMPOSE_CACHE=1    (cache dir pre-warmed
//                                                           by parent → hit)
//   BENCH_CACHE_MODE=noopts      → cache:false, fuseBasicBlocks:false,
//                                  skipSpecialize:true    (no post-parse
//                                                          compose optimizations
//                                                          — baseline pipeline
//                                                          cost without fuse
//                                                          and specialize)
// Cache dir (isolated, per-commit): BENCH_CACHE_DIR=<tmp>
//
// Emits one line per top-level metric so the parent can extract without relying
// on phase-ordering contracts (older commits emit no phases; newer commits
// might add more):
//   BENCH_E2E_RESULT=<elapsed ms>         overall t0..end (inside child, no
//                                         node startup / require / loadBytecode)
//   BENCH_E2E_LOAD=<ms>
//   BENCH_E2E_DECOMPOSE=<ms>
//   BENCH_E2E_EXPLORE=<ms>
//   BENCH_E2E_CACHEHIT=<0|1>              1 if load/compose phase was absent
//                                         (snapshot restore path, no compose)
//   BENCH_E2E_REQUIRE=<ms>                require('./lib/engine')
//   BENCH_E2E_BYTECODE=<ms>               loadBytecode(hex)
//   BENCH_E2E_PHASES=<json>               full tree, optional on older commits

const path = require('path');
const fs = require('fs');
const { performance } = require('perf_hooks');

try {
  const cacheMode = process.env.BENCH_CACHE_MODE || 'nocache';

  const tReq0 = performance.now();
  const mde = require('./lib/engine');
  const requireMs = performance.now() - tReq0;

  const codePath = path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
  const sourcePath = path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

  const phases = [];
  const onPhase = (pathName, ms, meta) => phases.push(meta ? [pathName, ms, meta] : [pathName, ms]);

  // Cache option: 'nocache'/'noopts' → false (no r/w); cache-miss/cache-hit
  // both use the env-driven CALC_COMPOSE_CACHE=1 path — we just leave
  // opts.cache undefined so engine respects the env var. Parent sets
  // CALC_COMPOSE_CACHE=1 and CALC_CACHE_DIR before spawning, and wipes/warms
  // the dir appropriately.
  const loadOpts = { onPhase };
  if (cacheMode === 'nocache' || cacheMode === 'noopts') loadOpts.cache = false;
  if (cacheMode === 'noopts') {
    // Disable post-parse compose optimizations. fuseBasicBlocks defaults to
    // true when extraGrade0Facts is present (see mde.load); force false here.
    // skipSpecialize is a new opt that short-circuits the per-pred specialize
    // pipeline. Older commits without skipSpecialize simply ignore it; in
    // that case this scenario effectively measures nofuse only (compose
    // specialize still runs), tagged with cacheHit=false and logged clearly.
    loadOpts.fuseBasicBlocks = false;
    loadOpts.skipSpecialize = true;
  }

  let bytecodeMs = 0;
  try {
    const loaderFile = path.join(__dirname, 'lib/engine/ill/bytecode-loader.js');
    if (fs.existsSync(loaderFile) && fs.existsSync(codePath)) {
      const { loadBytecode, bytecodeArrGetGuard } = require('./lib/engine/ill/bytecode-loader');
      const tBc0 = performance.now();
      const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\\s+0x([0-9a-fA-F]+)/)[1];
      const bc = loadBytecode(hex);
      bytecodeMs = performance.now() - tBc0;
      loadOpts.extraGrade0Facts = bc.facts;
      loadOpts.scopeGuard = bytecodeArrGetGuard;
    }
  } catch (e) { /* older commit without bytecode support — run without */ }

  const EXPLORE_OPTS = { maxDepth: 400, structuralMemo: true, dangerouslyUseFFI: true };

  const t0 = performance.now();

  const tLoad0 = performance.now();
  const calc = mde.load(sourcePath, loadOpts);
  const loadMs = performance.now() - tLoad0;

  const tDec0 = performance.now();
  const state = mde.decomposeQuery(calc.queries.get('symex'));
  const decMs = performance.now() - tDec0;
  const stateSize = (state && state.linear ? state.linear.length : 0) + (state && state.persistent ? state.persistent.length : 0);
  phases.push(['decompose', decMs, { stateSize, linear: state && state.linear ? state.linear.length : 0, persistent: state && state.persistent ? state.persistent.length : 0 }]);

  const tExp0 = performance.now();
  const tree = calc.explore(state, EXPLORE_OPTS);
  const expMs = performance.now() - tExp0;
  const treeUtils = require('./lib/engine/tree-utils');
  const nodes = treeUtils && treeUtils.countNodes ? treeUtils.countNodes(tree) : 0;
  const branches = treeUtils && treeUtils.countLeaves ? treeUtils.countLeaves(tree) : 0;
  phases.push(['explore', expMs, { nodes, branches, maxDepth: EXPLORE_OPTS.maxDepth }]);

  const elapsed = performance.now() - t0;

  // Cache-hit detection: snapshot-restore path skips compose entirely, so no
  // 'load/compose' phase will have been emitted. This is a reliable signal that
  // _loadCSnap returned a cached calc rather than running the cold pipeline.
  const hasComposePhase = phases.some(p => p[0] === 'load/compose' || p[0].startsWith('load/compose/'));
  const cacheHit = !hasComposePhase;

  // Synthetic 'load' bucket (kept for sunburst/flat-log consumers).
  const hasLoadPhases = phases.some(p => p[0].startsWith('load/'));
  if (hasLoadPhases) phases.unshift(['load', loadMs, {
    rules: (calc && calc.compiledRules) ? calc.compiledRules.length : 0,
    clauses: (calc && calc.clauses) ? calc.clauses.size : 0,
    definitions: (calc && calc.definitions) ? calc.definitions.size : 0,
  }]);

  process.stdout.write('BENCH_E2E_RESULT=' + elapsed + '\\n');
  process.stdout.write('BENCH_E2E_LOAD=' + loadMs + '\\n');
  process.stdout.write('BENCH_E2E_DECOMPOSE=' + decMs + '\\n');
  process.stdout.write('BENCH_E2E_EXPLORE=' + expMs + '\\n');
  process.stdout.write('BENCH_E2E_CACHEHIT=' + (cacheHit ? 1 : 0) + '\\n');
  process.stdout.write('BENCH_E2E_REQUIRE=' + requireMs + '\\n');
  process.stdout.write('BENCH_E2E_BYTECODE=' + bytecodeMs + '\\n');
  process.stdout.write('BENCH_E2E_PHASES=' + JSON.stringify(phases) + '\\n');
} catch (err) {
  process.stderr.write('E2E_CHILD_ERROR: ' + (err && err.stack || err && err.message || String(err)) + '\\n');
  process.exit(1);
}
`;

function makeBenchScript(warmup, runs, e2eWarmup, e2eRuns, e2eEnabled) {
  return `
'use strict';
const MARKER = '${MARKER}';
const WARMUP = ${warmup};
const RUNS = ${runs};
const E2E_WARMUP = ${e2eWarmup};
const E2E_RUNS = ${e2eRuns};
const E2E_ENABLED = ${e2eEnabled ? 'true' : 'false'};
const E2E_CHILD_SCRIPT = ${JSON.stringify(E2E_CHILD_SOURCE)};

const EXPLORE_OPTS = {
  maxDepth: 400,
  structuralMemo: true,
  dangerouslyUseFFI: true,
};

const { spawnSync } = require('child_process');
const path = require('path');
const fs = require('fs');

function stats(times) {
  times.sort((a, b) => a - b);
  const mean = times.reduce((a, b) => a + b, 0) / times.length;
  const stddev = Math.sqrt(
    times.reduce((s, t) => s + (t - mean) ** 2, 0) / times.length
  );
  return {
    mean,
    median: times[Math.floor(times.length / 2)],
    min: times[0],
    max: times[times.length - 1],
    p95: times[Math.floor(times.length * 0.95)],
    stddev,
    runs: times.length,
  };
}

function benchSymex(state, calc) {
  const treeUtils = require('./lib/engine/tree-utils');

  // Warmup
  for (let i = 0; i < WARMUP; i++) {
    calc.explore(state, EXPLORE_OPTS);
  }
  if (global.gc) global.gc();

  // Timed runs — capture tree metrics from first run
  let nodes = 0, branches = 0;
  const times = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    const tree = calc.explore(state, EXPLORE_OPTS);
    times.push(performance.now() - t0);
    if (i === 0) {
      nodes = treeUtils.countNodes(tree);
      branches = treeUtils.countLeaves(tree);
    }
  }

  return { ...stats(times), nodes, branches };
}

// Run one e2e iteration in a fresh Node subprocess. Returns
//   { t,           // child-reported elapsed ms (post-require t0)
//     parentWall,  // wall time incl. node startup + require + bytecode + exit
//     loadMs, decMs, expMs,
//     requireMs, bytecodeMs,  // externalities to the reported e2e number
//     cacheHit,    // 1 when _loadCSnap returned early (no compose ran)
//     phases }
// Older commits that only emit BENCH_E2E_RESULT degrade gracefully: unknown
// fields become undefined and aggregation skips them.
function runE2EChild(scriptPath, extraEnv) {
  const env = { ...process.env, NODE_PATH: path.join(__dirname, 'node_modules') };
  if (extraEnv) Object.assign(env, extraEnv);
  const parentT0 = performance.now();
  const r = spawnSync(process.execPath, [scriptPath], {
    cwd: __dirname, env, timeout: 60_000,
  });
  const parentWall = performance.now() - parentT0;
  if (r.error) throw new Error('spawn: ' + r.error.message);
  if (r.status !== 0) {
    const stderr = (r.stderr || Buffer.alloc(0)).toString();
    throw new Error('exit ' + r.status + ': ' + stderr.slice(0, 300).trim());
  }
  const stdout = (r.stdout || Buffer.alloc(0)).toString();
  const numField = (re) => {
    const m = stdout.match(re);
    if (!m) return undefined;
    const v = parseFloat(m[1]);
    return isFinite(v) ? v : undefined;
  };
  const t = numField(/BENCH_E2E_RESULT=([\\d.eE+-]+)/);
  if (t === undefined) throw new Error('no BENCH_E2E_RESULT in stdout: ' + stdout.slice(0, 200));
  const loadMs    = numField(/BENCH_E2E_LOAD=([\\d.eE+-]+)/);
  const decMs     = numField(/BENCH_E2E_DECOMPOSE=([\\d.eE+-]+)/);
  const expMs     = numField(/BENCH_E2E_EXPLORE=([\\d.eE+-]+)/);
  const requireMs = numField(/BENCH_E2E_REQUIRE=([\\d.eE+-]+)/);
  const bytecodeMs= numField(/BENCH_E2E_BYTECODE=([\\d.eE+-]+)/);
  const hitField  = stdout.match(/BENCH_E2E_CACHEHIT=(\\d)/);
  const cacheHit  = hitField ? hitField[1] === '1' : undefined;

  // Phases are optional — older commits won't emit the line.
  let phases = [];
  const pm = stdout.match(/BENCH_E2E_PHASES=(.+)/);
  if (pm) {
    try { phases = JSON.parse(pm[1]); } catch { phases = []; }
  }
  return { t, parentWall, loadMs, decMs, expMs, requireMs, bytecodeMs, cacheHit, phases };
}

// Aggregate per-phase stats across iterations.
//   Input:  [{t, phases: [[path, ms, meta?], ...]}, ...]
//   Output: { "load/parse": { mean, stddev, runs, meta? }, ... }
//
// Meta aggregation: numeric fields averaged across iterations (stable counts
// but floating-point means to cover jitter in nondeterministic phases).
// Boolean/string fields: last-iteration value. Array fields: last-iteration
// copy (e.g. chainLengths — dropping 20 iterations of identical arrays).
function aggregatePhases(iterResults) {
  const byPath = new Map();
  for (const { phases } of iterResults) {
    for (const p of phases) {
      const [name, ms, meta] = p;
      if (!byPath.has(name)) byPath.set(name, { times: [], metas: [] });
      const e = byPath.get(name);
      e.times.push(ms);
      if (meta) e.metas.push(meta);
    }
  }
  const out = {};
  for (const [p, { times, metas }] of byPath) {
    const mean = times.reduce((a, b) => a + b, 0) / times.length;
    const stddev = Math.sqrt(times.reduce((s, t) => s + (t - mean) ** 2, 0) / times.length);
    const entry = { mean, stddev, runs: times.length };
    if (metas.length > 0) entry.meta = _aggregateMeta(metas);
    out[p] = entry;
  }
  return out;
}

function _aggregateMeta(metas) {
  if (metas.length === 0) return undefined;
  const keys = new Set();
  for (const m of metas) for (const k of Object.keys(m)) keys.add(k);
  const out = {};
  for (const k of keys) {
    const vals = metas.map(m => m[k]).filter(v => v !== undefined);
    if (vals.length === 0) continue;
    const first = vals[0];
    if (typeof first === 'number') {
      const sum = vals.reduce((a, b) => a + (typeof b === 'number' ? b : 0), 0);
      out[k] = sum / vals.length;
    } else if (typeof first === 'boolean') {
      // majority (or last)
      out[k] = vals[vals.length - 1];
    } else if (Array.isArray(first)) {
      out[k] = vals[vals.length - 1];  // last-iter snapshot
    } else {
      out[k] = vals[vals.length - 1];
    }
  }
  return out;
}

// Cleanly remove an isolated per-bench cache dir. Only touches paths we own.
function _wipeCacheDir(dir) {
  if (!dir || !fs.existsSync(dir)) return;
  try { fs.rmSync(dir, { recursive: true, force: true }); } catch {}
}

// Run the full e2e child-spawn benchmark under a given cache scenario.
//
// mode = 'nocache'     → cache:false, each iter is a pure cold compose.
// mode = 'cache-miss'  → CALC_COMPOSE_CACHE=1; cache dir wiped BEFORE every
//                        timed iter so each is a first-write (cold build).
// mode = 'cache-hit'   → CALC_COMPOSE_CACHE=1; cache dir wiped ONCE, primed
//                        via warmup spawns, then every timed iter restores
//                        from the warm snapshot.
//
// Older commits: nocache works everywhere; cache modes degrade gracefully —
// unknown env vars are ignored, so cache-miss/cache-hit on a pre-cache commit
// simply re-measure the nocache path (tagged with mode but scenarios collapse).
function benchE2EChildSpawned(mode) {
  mode = mode || 'nocache';
  const scriptPath = path.join(__dirname, '_bench_e2e_iter.js');
  fs.writeFileSync(scriptPath, E2E_CHILD_SCRIPT);

  // Per-commit isolated cache dir — avoids touching the user's ~/.cache/calc.
  const cacheDir = (mode === 'nocache') ? null
    : path.join(require('os').tmpdir(), 'bench-history-cache-' + process.pid + '-' + mode);
  const extraEnv = { BENCH_CACHE_MODE: mode };
  if (mode === 'cache-miss' || mode === 'cache-hit') {
    extraEnv.CALC_COMPOSE_CACHE = '1';
    extraEnv.CALC_CACHE_DIR = cacheDir;
  }

  try {
    if (cacheDir) _wipeCacheDir(cacheDir);

    // Warmup
    //   nocache / cache-miss: primes OS page cache only (JS state is per-child).
    //   cache-hit: first warmup builds the snapshot; subsequent warmup+timed
    //              iters read it back. Results discarded either way.
    for (let i = 0; i < E2E_WARMUP; i++) runE2EChild(scriptPath, extraEnv);

    // For cache-miss we need every TIMED iter to start with an empty cache.
    // For cache-hit the warmup builds the snapshot and we must NOT wipe.
    const iters = [];
    for (let i = 0; i < E2E_RUNS; i++) {
      if (mode === 'cache-miss' && cacheDir) _wipeCacheDir(cacheDir);
      iters.push(runE2EChild(scriptPath, extraEnv));
    }

    const times      = iters.map(x => x.t);
    const parentWall = iters.map(x => x.parentWall).filter(v => typeof v === 'number');
    const loadV      = iters.map(x => x.loadMs).filter(v => typeof v === 'number');
    const decV       = iters.map(x => x.decMs).filter(v => typeof v === 'number');
    const expV       = iters.map(x => x.expMs).filter(v => typeof v === 'number');
    const reqV       = iters.map(x => x.requireMs).filter(v => typeof v === 'number');
    const bcV        = iters.map(x => x.bytecodeMs).filter(v => typeof v === 'number');
    const hitV       = iters.map(x => x.cacheHit).filter(v => typeof v === 'boolean');

    const s = stats(times);
    s.mode = mode;
    if (parentWall.length) s.parentWall = stats(parentWall.slice());
    if (loadV.length)      s.load       = stats(loadV.slice());
    if (decV.length)       s.decompose  = stats(decV.slice());
    if (expV.length)       s.explore    = stats(expV.slice());
    if (reqV.length)       s.require    = stats(reqV.slice());
    if (bcV.length)        s.bytecode   = stats(bcV.slice());
    if (hitV.length)       s.cacheHitRate = hitV.filter(v => v).length / hitV.length;

    // Synthetic composite: load+explore, excluding the trivial decompose step.
    // Useful when evaluating optimization that moves work between phases but
    // ignoring decompose noise (usually <1ms).
    if (loadV.length && expV.length && loadV.length === expV.length) {
      const combined = loadV.map((l, i) => l + expV[i]);
      s.loadPlusExplore = stats(combined);
    }

    const phases = aggregatePhases(iters);
    if (Object.keys(phases).length > 0) s.phases = phases;
    return s;
  } finally {
    try { fs.unlinkSync(scriptPath); } catch {}
    if (cacheDir) _wipeCacheDir(cacheDir);
  }
}

async function main() {
  const result = {};

  try {
    const mde = require('./lib/engine');

    // Load with bytecode if bytecode-loader exists (post-compose era)
    const codePath = path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
    const sourcePath = path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
    let loadOpts = { cache: false };
    try {
      const codeExists = fs.existsSync(codePath);
      const loaderPath = './lib/engine/ill/bytecode-loader';
      const hasLoader = fs.existsSync(path.join(__dirname, 'lib/engine/ill/bytecode-loader.js'));
      if (codeExists && hasLoader) {
        const { loadBytecode, bytecodeArrGetGuard } = require(loaderPath);
        const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\\s+0x([0-9a-fA-F]+)/)[1];
        const bc = loadBytecode(hex);
        loadOpts.extraGrade0Facts = bc.facts;
        loadOpts.scopeGuard = bytecodeArrGetGuard;
      }
    } catch (e) { /* older commit without bytecode support — run without */ }

    // Symex: pre-load once, then time explore() only (hot path)
    const calc = mde.load(sourcePath, loadOpts);
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    const symex = benchSymex(state, calc);
    result.symex = {
      mean: symex.mean, median: symex.median, min: symex.min, max: symex.max,
      p95: symex.p95, stddev: symex.stddev, runs: symex.runs,
    };
    result.nodes = symex.nodes;
    result.branches = symex.branches;

    // E2E: cold subprocess per iteration — measures true first-invocation cost.
    // Three scenarios, each a separate cold bench so a failure in one doesn't
    // contaminate the others. 'e2e' is kept as the nocache alias for
    // backward-compat with existing displays / resume files.
    if (E2E_ENABLED) {
      try {
        const nocache = benchE2EChildSpawned('nocache');
        result.e2e = nocache;
        result.e2eNoCache = nocache;
      } catch (err) {
        result.e2eError = err.message;
      }
      try { result.e2eCacheMiss = benchE2EChildSpawned('cache-miss'); }
      catch (err) { result.e2eCacheMissError = err.message; }
      try { result.e2eCacheHit = benchE2EChildSpawned('cache-hit'); }
      catch (err) { result.e2eCacheHitError = err.message; }
      try { result.e2eNoOpts = benchE2EChildSpawned('noopts'); }
      catch (err) { result.e2eNoOptsError = err.message; }
    }
  } catch (err) {
    result.error = err.message;
  }

  console.log(MARKER);
  console.log(JSON.stringify(result));
  console.log(MARKER);
}

main().catch(err => {
  console.error(err.message);
  process.exit(1);
});
`;
}

// ─── Run benchmark in a directory ─────────────────────────────────────────────

function runBench(cwd, warmup, runs, e2eWarmup, e2eRuns, e2eEnabled) {
  return new Promise((resolve) => {
    const script = makeBenchScript(warmup, runs, e2eWarmup, e2eRuns, e2eEnabled);
    const scriptPath = path.join(cwd, '_bench_history_runner.js');
    fs.writeFileSync(scriptPath, script);

    const child = spawn(process.execPath, ['--expose-gc', scriptPath], {
      cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
      env: { ...process.env, NODE_PATH: path.join(cwd, 'node_modules') },
      // E2E iterations include full load+compose per run, so extend timeout generously.
      timeout: 600_000,
    });

    let stdout = '';
    let stderr = '';
    child.stdout.on('data', d => { stdout += d; });
    child.stderr.on('data', d => { stderr += d; });

    child.on('close', code => {
      // Clean up runner script
      try { fs.unlinkSync(scriptPath); } catch {}

      if (code !== 0) {
        return resolve({ error: `exit ${code}: ${stderr.slice(0, 200)}` });
      }

      const lines = stdout.split('\n');
      const startIdx = lines.indexOf(MARKER);
      const endIdx = lines.lastIndexOf(MARKER);

      if (startIdx === -1 || startIdx === endIdx) {
        return resolve({ error: `no JSON markers: ${stdout.slice(0, 200)}` });
      }

      try {
        const json = lines.slice(startIdx + 1, endIdx).join('\n');
        resolve(JSON.parse(json));
      } catch (err) {
        resolve({ error: `parse: ${err.message}` });
      }
    });

    child.on('error', err => {
      try { fs.unlinkSync(scriptPath); } catch {}
      resolve({ error: err.message });
    });
  });
}

// ─── Display ──────────────────────────────────────────────────────────────────

function fmtMs(ms) {
  if (ms === undefined || ms === null) return '—';
  if (ms < 1) return `${(ms * 1000).toFixed(0)}µs`;
  if (ms < 100) return `${ms.toFixed(2)}ms`;
  return `${ms.toFixed(0)}ms`;
}

function fmtChange(current, baseline) {
  if (!baseline || !current) return '—';
  const pct = ((current - baseline) / baseline) * 100;
  const sign = pct > 0 ? '+' : '';
  return `${sign}${pct.toFixed(1)}%`;
}

function getSymex(data) {
  if (!data || data.error) return null;
  if (data.symex) return data.symex;
  // Legacy flat format (pre-e2e): treat as symex
  if (typeof data.mean === 'number') {
    return { mean: data.mean, stddev: data.stddev, runs: data.runs };
  }
  return null;
}

function getE2E(data) {
  if (!data || data.error) return null;
  return data.e2e || null;
}

function displayTable(results) {
  // Baselines = newest successful result
  let baselineSymex = null;
  let baselineE2E = null;
  for (const r of results) {
    const s = getSymex(r.data);
    if (s && baselineSymex === null) baselineSymex = s.mean;
    const e = getE2E(r.data);
    if (e && baselineE2E === null) baselineE2E = e.mean;
    if (baselineSymex !== null && baselineE2E !== null) break;
  }

  const maxSubj = Math.min(40, Math.max(20, ...results.map(r => r.subject.length)));

  // Column schema:
  //   Explore  = warm in-proc symex (hot path only)
  //   Load     = mde.load() from cold subprocess (no compose cache)
  //   L+E      = load + explore, cold subprocess (composite for nocache mode)
  //   E2E      = total cold child-reported (nocache)
  //   Wall     = parent wall (incl. node startup/require/bytecode/exit)
  //   Miss     = cold subprocess with CALC_COMPOSE_CACHE=1, cache pre-wiped (build cost)
  //   Hit      = cold subprocess with CALC_COMPOSE_CACHE=1, cache warm (hit cost)
  //   NoOpt    = cold subprocess, fuseBasicBlocks=false + skipSpecialize=true
  //              (baseline pipeline cost without fuse and specialize opts)
  const cols = ['#', 'Commit', 'Date', 'Message', 'Nodes', 'Leaves',
    'Explore', 'Load', 'L+E', 'E2E', 'Wall', 'Miss', 'Hit', 'NoOpt', 'vs HEAD'];
  const rows = [];

  for (let i = 0; i < results.length; i++) {
    const r = results[i];
    const row = [
      String(i),
      r.shortHash,
      r.date,
      r.subject.slice(0, maxSubj),
    ];

    const s = getSymex(r.data);
    const e = getE2E(r.data);
    const miss = r.data && r.data.e2eCacheMiss;
    const hit  = r.data && r.data.e2eCacheHit;
    const noopt = r.data && r.data.e2eNoOpts;

    if (r.data && r.data.error) {
      row.push('—', '—', 'ERROR', '—', '—', '—', '—', '—', '—', '—', '—');
    } else if (!r.data) {
      row.push('—', '—', '—', '—', '—', '—', '—', '—', '—', '—', '—');
    } else {
      const nodes = r.data.nodes !== undefined ? String(r.data.nodes) : '—';
      const branches = r.data.branches !== undefined ? String(r.data.branches) : '—';
      const loadMean = e && e.load ? e.load.mean : undefined;
      const lePlus   = e && e.loadPlusExplore ? e.loadPlusExplore.mean : undefined;
      const wallMean = e && e.parentWall ? e.parentWall.mean : undefined;
      row.push(
        nodes,
        branches,
        s ? fmtMs(s.mean) : '—',
        loadMean !== undefined ? fmtMs(loadMean) : '—',
        lePlus   !== undefined ? fmtMs(lePlus)   : '—',
        e ? fmtMs(e.mean) : '—',
        wallMean !== undefined ? fmtMs(wallMean) : '—',
        miss ? fmtMs(miss.mean) : '—',
        hit  ? fmtMs(hit.mean)  : '—',
        noopt ? fmtMs(noopt.mean) : '—',
        s ? fmtChange(s.mean, baselineSymex) : '—',
      );
    }
    rows.push(row);
  }

  // Compute column widths
  const widths = cols.map((c, ci) =>
    Math.max(c.length, ...rows.map(r => (r[ci] || '').length))
  );

  // Render
  console.log();
  console.log(cols.map((c, i) => c.padEnd(widths[i])).join('  '));
  console.log(widths.map(w => '─'.repeat(w)).join('──'));

  for (const row of rows) {
    console.log(row.map((c, i) => {
      // Right-align numeric columns (all after Message, idx >= 4)
      if (i >= 4) return (c || '').padStart(widths[i]);
      return (c || '').padEnd(widths[i]);
    }).join('  '));
  }

  console.log(widths.map(w => '─'.repeat(w)).join('──'));

  // Summary ranges — one line per metric, skipped when no data.
  const summaryLine = (label, vals) => {
    if (vals.length === 0) return;
    const min = Math.min(...vals), max = Math.max(...vals);
    const range = min > 0 ? ((max / min - 1) * 100).toFixed(1) + '%' : '—';
    console.log(`${label.padEnd(8)} min=${fmtMs(min)} max=${fmtMs(max)} range=${range}`);
  };
  summaryLine('symex:',  results.map(r => getSymex(r.data)).filter(Boolean).map(s => s.mean));
  summaryLine('e2e:',    results.map(r => getE2E(r.data)).filter(Boolean).map(e => e.mean));
  summaryLine('load:',   results.map(r => getE2E(r.data)).filter(e => e && e.load).map(e => e.load.mean));
  summaryLine('wall:',   results.map(r => getE2E(r.data)).filter(e => e && e.parentWall).map(e => e.parentWall.mean));
  summaryLine('miss:',   results.map(r => r.data && r.data.e2eCacheMiss).filter(Boolean).map(m => m.mean));
  summaryLine('hit:',    results.map(r => r.data && r.data.e2eCacheHit).filter(Boolean).map(h => h.mean));
  summaryLine('noopt:',  results.map(r => r.data && r.data.e2eNoOpts).filter(Boolean).map(n => n.mean));

  const successful = results.filter(r => getSymex(r.data));
  console.log(`${successful.length}/${results.length} commits benchmarked successfully.`);
  console.log();
}

// ─── Main ─────────────────────────────────────────────────────────────────────

async function main() {
  const opts = parseArgs();

  // Get commit list
  const commits = getCommitList(opts.branch, opts.commits);
  if (commits.length === 0) {
    console.error('No commits found.');
    process.exit(1);
  }

  console.log(`\nBenchmark History: explore solc_symbolic (FFI + all optimizations)`);
  console.log(`  Commits:     ${commits.length} (from ${opts.branch})`);
  console.log(`  Symex:       ${opts.warmup} warmup, ${opts.runs} timed (hot explore-only)`);
  if (opts.e2eEnabled) {
    console.log(`  E2E:         ${opts.e2eWarmup} warmup, ${opts.e2eRuns} timed (cold: fresh Node per iter)`);
    console.log(`               × 4 scenarios: nocache / cache-miss (build) / cache-hit (restore) / noopts (no fuse/specialize)`);
  } else {
    console.log(`  E2E:         disabled (--no-e2e)`);
  }
  console.log(`  Range:       ${commits[commits.length - 1].shortHash}..${commits[0].shortHash}`);
  console.log();

  // Load partial results if resuming
  const priorResults = new Map();
  if (opts.resume && fs.existsSync(opts.resume)) {
    try {
      const saved = JSON.parse(fs.readFileSync(opts.resume, 'utf8'));
      for (const entry of saved.results || []) {
        priorResults.set(entry.fullHash, entry.data);
      }
      console.log(`  Resuming: ${priorResults.size} cached results from ${opts.resume}\n`);
    } catch (e) {
      console.error(`  Warning: could not parse resume file: ${e.message}\n`);
    }
  }

  // Cleanup handler
  let currentHash = null;
  const onExit = () => {
    if (currentHash) cleanupWorktree(currentHash);
    cleanupAll();
  };
  process.on('SIGINT', () => { onExit(); process.exit(130); });
  process.on('SIGTERM', () => { onExit(); process.exit(143); });

  // Process commits newest-first (display order)
  const results = [];

  // Resolve actual HEAD hash to decide if in-place benchmark is valid
  const actualHead = execSync('git rev-parse HEAD', { cwd: ROOT, encoding: 'utf8' }).trim();

  for (let i = 0; i < commits.length; i++) {
    const c = commits[i];
    const isHead = (c.fullHash === actualHead);
    const progress = `[${i + 1}/${commits.length}]`;

    // Check for cached result
    if (priorResults.has(c.fullHash)) {
      process.stdout.write(`${progress} ${c.shortHash} ${c.subject.slice(0, 50)} ... cached\n`);
      results.push({ ...c, data: priorResults.get(c.fullHash) });
      continue;
    }

    process.stdout.write(`${progress} ${c.shortHash} ${c.subject.slice(0, 50)} ... `);
    const t0 = performance.now();

    let data;
    if (isHead) {
      // Run HEAD in-place (no worktree needed)
      data = await runBench(ROOT, opts.warmup, opts.runs, opts.e2eWarmup, opts.e2eRuns, opts.e2eEnabled);
    } else {
      currentHash = c.fullHash;
      let wtPath;
      try {
        wtPath = setupWorktree(c.fullHash);
        data = await runBench(wtPath, opts.warmup, opts.runs, opts.e2eWarmup, opts.e2eRuns, opts.e2eEnabled);
      } catch (err) {
        data = { error: err.message };
      } finally {
        cleanupWorktree(c.fullHash);
        currentHash = null;
      }
    }

    const elapsed = ((performance.now() - t0) / 1000).toFixed(1);

    // Format inline result — show symex, e2e nocache, cache miss, cache hit.
    if (data.error) {
      process.stdout.write(`ERROR (${elapsed}s)\n`);
    } else {
      const s = getSymex(data);
      const e = getE2E(data);
      const miss = data.e2eCacheMiss;
      const hit = data.e2eCacheHit;
      const noopt = data.e2eNoOpts;
      const symexStr = s ? `${fmtMs(s.mean)} ±${fmtMs(s.stddev)}` : 'n/a';
      const loadStr = (e && e.load) ? ` · load ${fmtMs(e.load.mean)}` : '';
      const e2eStr  = e ? ` · e2e ${fmtMs(e.mean)}` : (data.e2eError ? ' · e2e ERROR' : '');
      const missStr = miss ? ` · miss ${fmtMs(miss.mean)}` : '';
      const hitStr  = hit ? ` · hit ${fmtMs(hit.mean)}` : '';
      const noStr   = noopt ? ` · noopt ${fmtMs(noopt.mean)}` : '';
      process.stdout.write(`${symexStr}${loadStr}${e2eStr}${missStr}${hitStr}${noStr} [${data.nodes}n,${data.branches}l] (${elapsed}s)\n`);
    }

    results.push({ ...c, data });

    // Save incremental results
    if (opts.out) {
      const outData = {
        timestamp: new Date().toISOString(),
        config: { runs: opts.runs, warmup: opts.warmup },
        results: results.map(r => ({ fullHash: r.fullHash, shortHash: r.shortHash, date: r.date, subject: r.subject, data: r.data })),
      };
      fs.writeFileSync(opts.out, JSON.stringify(outData, null, 2));
    }
  }

  // Final cleanup
  cleanupAll();

  // Display table
  displayTable(results);

  // Save final results if --out specified
  if (opts.out) {
    const outData = {
      timestamp: new Date().toISOString(),
      config: {
        runs: opts.runs, warmup: opts.warmup,
        e2eRuns: opts.e2eRuns, e2eWarmup: opts.e2eWarmup, e2eEnabled: opts.e2eEnabled,
        commits: opts.commits, branch: opts.branch,
      },
      results: results.map(r => ({ fullHash: r.fullHash, shortHash: r.shortHash, date: r.date, subject: r.subject, data: r.data })),
    };
    fs.writeFileSync(opts.out, JSON.stringify(outData, null, 2));
    console.log(`Results saved to ${opts.out}`);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
