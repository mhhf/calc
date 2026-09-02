// tools/bench-history.runner.mjs — per-commit benchmark runner.
//
// Written by tools/bench-history.js into each worktree (as
// `_bench_history_runner.mjs`) before spawning. Executed with cwd=worktree.
//
// Layered subprocess design:
//   L1 (parent bench-history.js)  — walks commits, manages worktrees
//   L2 (this file)                — in-proc symex bench + spawns L3
//   L3 (bench-history.child.mjs)  — one cold e2e iteration per spawn
//
// Why L3 exists: `{ cache: false }` routes to _loadFresh which does NOT
// clear Store's hash-cons map. Module-level state (DEDUP map, lazy
// expression parser, require cache, JIT, OS page cache) stays warm across
// in-process iterations and underestimates true cold-start by ~25×. Each
// L3 invocation is a fresh Bun process — guaranteed cold.
//
// All knobs come via env vars (no string-interpolation surface area):
//   BENCH_MARKER          delimiter for parent JSON extraction
//   BENCH_WARMUP          symex warmup runs
//   BENCH_RUNS            symex timed runs
//   BENCH_E2E_WARMUP      e2e warmup spawns
//   BENCH_E2E_RUNS        e2e timed spawns
//   BENCH_E2E_ENABLED     "0" disables e2e
//   BENCH_CHILD_PATH      absolute path to the L3 child script

import { spawnSync } from 'node:child_process';
import path from 'node:path';
import os from 'node:os';
import fs from 'node:fs';
import { performance } from 'node:perf_hooks';

const MARKER          = process.env.BENCH_MARKER          || '---BENCH-HISTORY---';
const WARMUP          = +(process.env.BENCH_WARMUP        || 10);
const RUNS            = +(process.env.BENCH_RUNS          || 21);
const E2E_WARMUP      = +(process.env.BENCH_E2E_WARMUP    || 2);
const E2E_RUNS        = +(process.env.BENCH_E2E_RUNS      || 5);
const E2E_ENABLED     = process.env.BENCH_E2E_ENABLED !== '0';
const CHILD_SCRIPT    = process.env.BENCH_CHILD_PATH;
if (!CHILD_SCRIPT) throw new Error('bench-history.runner: BENCH_CHILD_PATH env var is required');

const EXPLORE_OPTS = { maxDepth: 400, structuralMemo: true, dangerouslyUseFFI: true };

// Bun exposes Bun.gc; node uses --expose-gc to wire global.gc. The bench
// only calls gc opportunistically, so polyfill best-effort.
if (typeof globalThis.gc !== 'function' && typeof Bun !== 'undefined') {
  globalThis.gc = () => Bun.gc(true);
}

async function loadDefault(spec) {
  const m = await import(spec);
  return m.default ?? m;
}

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

function benchSymex(state, calc, treeUtils) {
  for (let i = 0; i < WARMUP; i++) calc.explore(state, EXPLORE_OPTS);
  if (globalThis.gc) globalThis.gc();

  let nodes = 0, branches = 0;
  const times = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    const tree = calc.explore(state, EXPLORE_OPTS);
    times.push(performance.now() - t0);
    if (i === 0 && treeUtils) {
      nodes = treeUtils.countNodes(tree);
      branches = treeUtils.countLeaves(tree);
    }
  }
  return { ...stats(times), nodes, branches };
}

// One e2e iteration in a fresh subprocess. Spawns the same runtime that's
// running this file (bun if parent is bun, node if parent is node).
function runE2EChild(scriptPath, extraEnv) {
  const env = { ...process.env, NODE_PATH: path.join(import.meta.dirname, 'node_modules') };
  if (extraEnv) Object.assign(env, extraEnv);
  const parentT0 = performance.now();
  const r = spawnSync(process.execPath, [scriptPath], {
    cwd: import.meta.dirname, env, timeout: 60_000,
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
  const t = numField(/BENCH_E2E_RESULT=([\d.eE+-]+)/);
  if (t === undefined) throw new Error('no BENCH_E2E_RESULT in stdout: ' + stdout.slice(0, 200));
  const loadMs    = numField(/BENCH_E2E_LOAD=([\d.eE+-]+)/);
  const decMs     = numField(/BENCH_E2E_DECOMPOSE=([\d.eE+-]+)/);
  const expMs     = numField(/BENCH_E2E_EXPLORE=([\d.eE+-]+)/);
  const requireMs = numField(/BENCH_E2E_REQUIRE=([\d.eE+-]+)/);
  const bytecodeMs= numField(/BENCH_E2E_BYTECODE=([\d.eE+-]+)/);
  const hitField  = stdout.match(/BENCH_E2E_CACHEHIT=(\d)/);
  const cacheHit  = hitField ? hitField[1] === '1' : undefined;

  let phases = [];
  const pm = stdout.match(/BENCH_E2E_PHASES=(.+)/);
  if (pm) {
    try { phases = JSON.parse(pm[1]); } catch { phases = []; }
  }
  return { t, parentWall, loadMs, decMs, expMs, requireMs, bytecodeMs, cacheHit, phases };
}

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
    } else {
      out[k] = vals[vals.length - 1];
    }
  }
  return out;
}

function _wipeCacheDir(dir) {
  if (!dir || !fs.existsSync(dir)) return;
  try { fs.rmSync(dir, { recursive: true, force: true }); } catch {}
}

function benchE2EChildSpawned(mode) {
  mode = mode || 'nocache';

  const cacheDir = (mode === 'nocache') ? null
    : path.join(os.tmpdir(), 'bench-history-cache-' + process.pid + '-' + mode);
  const extraEnv = { BENCH_CACHE_MODE: mode };
  if (mode === 'cache-miss' || mode === 'cache-hit') {
    extraEnv.CALC_COMPOSE_CACHE = '1';
    extraEnv.CALC_CACHE_DIR = cacheDir;
  }

  try {
    if (cacheDir) _wipeCacheDir(cacheDir);

    for (let i = 0; i < E2E_WARMUP; i++) runE2EChild(CHILD_SCRIPT, extraEnv);

    const iters = [];
    for (let i = 0; i < E2E_RUNS; i++) {
      if (mode === 'cache-miss' && cacheDir) _wipeCacheDir(cacheDir);
      iters.push(runE2EChild(CHILD_SCRIPT, extraEnv));
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

    if (loadV.length && expV.length && loadV.length === expV.length) {
      const combined = loadV.map((l, i) => l + expV[i]);
      s.loadPlusExplore = stats(combined);
    }

    const phases = aggregatePhases(iters);
    if (Object.keys(phases).length > 0) s.phases = phases;
    return s;
  } finally {
    if (cacheDir) _wipeCacheDir(cacheDir);
  }
}

async function main() {
  const result = {};

  try {
    const mde = await loadDefault('./calculus/ill/index.js');

    let treeUtils = null;
    try { treeUtils = await loadDefault('./lib/engine/tree-utils.js'); } catch {}

    const codePath = path.join(import.meta.dirname, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
    const sourcePath = path.join(import.meta.dirname, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

    const loadOpts = { cache: false };
    try {
      const codeExists = fs.existsSync(codePath);
      const loaderJs = path.join(import.meta.dirname, 'calculus/ill/lib/bytecode-loader.js');
      if (codeExists && fs.existsSync(loaderJs)) {
        const { loadBytecode, bytecodeArrGetGuard } = await loadDefault('./calculus/ill/lib/bytecode-loader.js');
        const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
        const bc = loadBytecode(hex);
        loadOpts.extraGrade0Facts = bc.facts;
        loadOpts.scopeGuard = bytecodeArrGetGuard;
      }
    } catch (e) { /* older commit without bytecode support — run without */ }

    const calc = mde.load(sourcePath, loadOpts);
    const state = (mde.normalizeQuery || mde.decomposeQuery)(calc.queries.get('symex'));

    const symex = benchSymex(state, calc, treeUtils);
    result.symex = {
      mean: symex.mean, median: symex.median, min: symex.min, max: symex.max,
      p95: symex.p95, stddev: symex.stddev, runs: symex.runs,
    };
    result.nodes = symex.nodes;
    result.branches = symex.branches;

    if (E2E_ENABLED) {
      try {
        const nocache = benchE2EChildSpawned('nocache');
        result.e2e = nocache;
        result.e2eNoCache = nocache;
      } catch (err) { result.e2eError = err.message; }
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
