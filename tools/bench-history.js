#!/usr/bin/env bun
/**
 * Benchmark History — explore solc_symbolic across N commits.
 *
 * Benchmarks the last N commits (via git worktrees) running two scenarios:
 *   - symex: explore.explore() on a pre-loaded state (hot path only)
 *   - e2e:   load + decomposeQuery + explore, each iteration in a FRESH
 *            subprocess so the Store hash-cons table, lazy-built expression
 *            parser, module require cache, and JIT all start cold. This is
 *            the true "first-invocation" cost users pay — not the warm
 *            re-parse cost you'd get running the load loop in a single
 *            process.
 *
 * Three-layer subprocess design:
 *   L1 (this file)               — walks commits, owns worktrees.
 *   L2 (bench-history.runner.mjs) — per-commit, runs in-process symex bench
 *                                   and spawns L3 per e2e iteration.
 *   L3 (bench-history.child.mjs)  — per-iteration, runs ONE cold e2e and
 *                                   prints metrics on stdout.
 *
 * The runner and child live in real .mjs files (not template-literal source
 * embedded in this one) so codemods don't see source-as-data and rewrite
 * imports inside string contents.
 *
 * Usage (bun is the canonical runtime; node also works on post-bun-migration
 * commits — historical CJS commits are loaded by L2/L3 via dynamic import):
 *   bun tools/bench-history.js [--commits=50] [--runs=21] [--warmup=10]
 *
 * Options:
 *   --commits=N      Number of commits to benchmark (default: 50)
 *   --runs=N         Symex timed runs per benchmark (default: 21)
 *   --warmup=N       Symex warmup runs before timing (default: 10)
 *   --e2e-runs=N     E2E timed runs per benchmark (default: 5, each a fresh process)
 *   --e2e-warmup=N   E2E warmup runs (fresh processes, prime OS page cache) (default: 2)
 *   --no-e2e         Disable end-to-end benchmark (symex only)
 *   --branch=REF     Branch/ref to walk (default: HEAD)
 *   --resume=FILE    Resume from partial results JSON file
 *   --out=FILE       Write results JSON to file
 */

import { execSync, spawn } from 'child_process';
import path from 'path';
import fs from 'fs';
import { performance } from 'perf_hooks';

const ROOT = path.resolve(import.meta.dirname, '..');
const WORKTREE_DIR = path.join(ROOT, '.bench-history');
const MARKER = '---BENCH-HISTORY---';

// L2/L3 sibling sources, copied into each worktree before spawn.
const RUNNER_SRC_PATH = path.join(import.meta.dirname, 'bench-history.runner.mjs');
const CHILD_SRC_PATH  = path.join(import.meta.dirname, 'bench-history.child.mjs');
const RUNNER_DST_NAME = '_bench_history_runner.mjs';
const CHILD_DST_NAME  = '_bench_history_child.mjs';

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
    const date = rest[0];
    const subject = rest.slice(3).join(' ');
    return { fullHash, shortHash, date, subject };
  });
}

// ─── Store hash collision workaround ──────────────────────────────────────────
// Between 03dceb2 and 64370df, a hex literal in to256 (bin.ill) combined with
// arr.ill predicates causes FNV-1a hash collisions that corrupt the symex query.
// Patching .ill content or tag IDs is fragile. Instead we change the FNV offset
// basis in lib/hash.js — this shifts the entire hash landscape without
// altering any tag IDs, term semantics, or code paths.

function patchHashSeed(wtPath) {
  const hashJs = path.join(wtPath, 'lib/hash.js');
  try {
    if (!fs.existsSync(hashJs)) return;
    const content = fs.readFileSync(hashJs, 'utf8');
    if (!content.includes('0x811c9dc5')) return;
    const storeJs = path.join(wtPath, 'lib/kernel/store.js');
    if (fs.existsSync(storeJs)) {
      const storeContent = fs.readFileSync(storeJs, 'utf8');
      if (storeContent.includes("'metavar'")) return;
    }
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

// ─── Bench runner (spawns L2 in worktree) ─────────────────────────────────────

function runBench(cwd, warmup, runs, e2eWarmup, e2eRuns, e2eEnabled) {
  return new Promise((resolve) => {
    // Copy L2 + L3 sources into the worktree. The .mjs extension forces ESM
    // parsing regardless of the worktree's package.json "type" field, which
    // matters for pre-bun-migration commits where "type": "commonjs".
    const runnerPath = path.join(cwd, RUNNER_DST_NAME);
    const childPath  = path.join(cwd, CHILD_DST_NAME);
    fs.copyFileSync(RUNNER_SRC_PATH, runnerPath);
    fs.copyFileSync(CHILD_SRC_PATH, childPath);

    const cleanup = () => {
      try { fs.unlinkSync(runnerPath); } catch {}
      try { fs.unlinkSync(childPath); } catch {}
    };

    const env = {
      ...process.env,
      NODE_PATH: path.join(cwd, 'node_modules'),
      BENCH_MARKER: MARKER,
      BENCH_WARMUP: String(warmup),
      BENCH_RUNS: String(runs),
      BENCH_E2E_WARMUP: String(e2eWarmup),
      BENCH_E2E_RUNS: String(e2eRuns),
      BENCH_E2E_ENABLED: e2eEnabled ? '1' : '0',
      BENCH_CHILD_PATH: childPath,
    };

    // process.execPath = the runtime that started us (bun when invoked via
    // `bun tools/bench-history.js`, node when invoked via node). The child
    // inherits the same runtime — bun's CJS↔ESM dynamic import interop
    // handles both pre- and post-bun-migration commits transparently.
    const child = spawn(process.execPath, [runnerPath], {
      cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
      env,
      timeout: 600_000,
    });

    let stdout = '';
    let stderr = '';
    child.stdout.on('data', d => { stdout += d; });
    child.stderr.on('data', d => { stderr += d; });

    child.on('close', code => {
      cleanup();

      if (code !== 0) {
        return resolve({ error: `exit ${code}: ${stderr.slice(0, 400)}` });
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
      cleanup();
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
  //   Wall     = parent wall (incl. runtime startup/require/bytecode/exit)
  //   Miss     = cold subprocess with CALC_COMPOSE_CACHE=1, cache pre-wiped
  //   Hit      = cold subprocess with CALC_COMPOSE_CACHE=1, cache warm
  //   NoOpt    = cold subprocess, fuseBasicBlocks=false + skipSpecialize=true
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

  const widths = cols.map((c, ci) =>
    Math.max(c.length, ...rows.map(r => (r[ci] || '').length))
  );

  console.log();
  console.log(cols.map((c, i) => c.padEnd(widths[i])).join('  '));
  console.log(widths.map(w => '─'.repeat(w)).join('──'));

  for (const row of rows) {
    console.log(row.map((c, i) => {
      if (i >= 4) return (c || '').padStart(widths[i]);
      return (c || '').padEnd(widths[i]);
    }).join('  '));
  }

  console.log(widths.map(w => '─'.repeat(w)).join('──'));

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

  const commits = getCommitList(opts.branch, opts.commits);
  if (commits.length === 0) {
    console.error('No commits found.');
    process.exit(1);
  }

  console.log(`\nBenchmark History: explore solc_symbolic (FFI + all optimizations)`);
  console.log(`  Commits:     ${commits.length} (from ${opts.branch})`);
  console.log(`  Symex:       ${opts.warmup} warmup, ${opts.runs} timed (hot explore-only)`);
  if (opts.e2eEnabled) {
    console.log(`  E2E:         ${opts.e2eWarmup} warmup, ${opts.e2eRuns} timed (cold: fresh process per iter)`);
    console.log(`               × 4 scenarios: nocache / cache-miss (build) / cache-hit (restore) / noopts (no fuse/specialize)`);
  } else {
    console.log(`  E2E:         disabled (--no-e2e)`);
  }
  console.log(`  Range:       ${commits[commits.length - 1].shortHash}..${commits[0].shortHash}`);
  console.log();

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

  let currentHash = null;
  const onExit = () => {
    if (currentHash) cleanupWorktree(currentHash);
    cleanupAll();
  };
  process.on('SIGINT', () => { onExit(); process.exit(130); });
  process.on('SIGTERM', () => { onExit(); process.exit(143); });

  const results = [];

  const actualHead = execSync('git rev-parse HEAD', { cwd: ROOT, encoding: 'utf8' }).trim();

  for (let i = 0; i < commits.length; i++) {
    const c = commits[i];
    const isHead = (c.fullHash === actualHead);
    const progress = `[${i + 1}/${commits.length}]`;

    if (priorResults.has(c.fullHash)) {
      process.stdout.write(`${progress} ${c.shortHash} ${c.subject.slice(0, 50)} ... cached\n`);
      results.push({ ...c, data: priorResults.get(c.fullHash) });
      continue;
    }

    process.stdout.write(`${progress} ${c.shortHash} ${c.subject.slice(0, 50)} ... `);
    const t0 = performance.now();

    let data;
    if (isHead) {
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

    if (data.error) {
      process.stdout.write(`ERROR (${elapsed}s)\n`);
    } else {
      const s = getSymex(data);
      const e = getE2E(data);
      const miss = data.e2eCacheMiss;
      const hit = data.e2eCacheHit;
      const noopt = data.e2eNoOpts;
      const symexStr = s ? `${fmtMs(s.mean)} ±${fmtMs(s.stddev)}` : 'n/a';
      const real = data.symexReal;
      const realStr = real ? ` · real ${fmtMs(real.mean)} [${real.nodes}n,${real.branches}l]` : '';
      const loadStr = (e && e.load) ? ` · load ${fmtMs(e.load.mean)}` : '';
      const e2eStr  = e ? ` · e2e ${fmtMs(e.mean)}` : (data.e2eError ? ' · e2e ERROR' : '');
      const missStr = miss ? ` · miss ${fmtMs(miss.mean)}` : '';
      const hitStr  = hit ? ` · hit ${fmtMs(hit.mean)}` : '';
      const noStr   = noopt ? ` · noopt ${fmtMs(noopt.mean)}` : '';
      process.stdout.write(`${symexStr}${realStr}${loadStr}${e2eStr}${missStr}${hitStr}${noStr} [${data.nodes}n,${data.branches}l] (${elapsed}s)\n`);
    }

    results.push({ ...c, data });

    if (opts.out) {
      const outData = {
        timestamp: new Date().toISOString(),
        config: { runs: opts.runs, warmup: opts.warmup },
        results: results.map(r => ({ fullHash: r.fullHash, shortHash: r.shortHash, date: r.date, subject: r.subject, data: r.data })),
      };
      fs.writeFileSync(opts.out, JSON.stringify(outData, null, 2));
    }
  }

  cleanupAll();

  displayTable(results);

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
