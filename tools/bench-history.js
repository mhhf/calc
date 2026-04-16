#!/usr/bin/env node
/**
 * Benchmark History — explore solc_symbolic across N commits.
 *
 * Benchmarks the last N commits (via git worktrees) running
 * explore.explore() on solc_symbolic with full optimizations (evm profile).
 *
 * Usage:
 *   node --expose-gc tools/bench-history.js [--commits=50] [--runs=21] [--warmup=10]
 *
 * Options:
 *   --commits=N    Number of commits to benchmark (default: 50)
 *   --runs=N       Timed runs per benchmark (default: 20)
 *   --warmup=N     Warmup runs before timing (default: 5)
 *   --branch=REF   Branch/ref to walk (default: HEAD)
 *   --resume=FILE  Resume from partial results JSON file
 *   --out=FILE     Write results JSON to file
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
  let branch = 'HEAD';
  let resume = null;
  let out = null;

  for (const arg of args) {
    if (arg.startsWith('--commits=')) commits = parseInt(arg.slice(10), 10);
    else if (arg.startsWith('--runs=')) runs = parseInt(arg.slice(7), 10);
    else if (arg.startsWith('--warmup=')) warmup = parseInt(arg.slice(9), 10);
    else if (arg.startsWith('--branch=')) branch = arg.slice(9);
    else if (arg.startsWith('--resume=')) resume = arg.slice(9);
    else if (arg.startsWith('--out=')) out = arg.slice(6);
  }

  return { commits, runs, warmup, branch, resume, out };
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

function makeBenchScript(warmup, runs) {
  return `
'use strict';
const MARKER = '${MARKER}';
const WARMUP = ${warmup};
const RUNS = ${runs};

function benchExplore(state, calc) {
  const treeUtils = require('./lib/engine/tree-utils');
  const opts = {
    maxDepth: 400,
    structuralMemo: true,
    dangerouslyUseFFI: true,
  };

  // Warmup
  for (let i = 0; i < WARMUP; i++) {
    calc.explore(state, opts);
  }
  if (global.gc) global.gc();

  // Timed runs — capture tree metrics from first run
  let nodes = 0, branches = 0;
  const times = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    const tree = calc.explore(state, opts);
    times.push(performance.now() - t0);
    if (i === 0) {
      nodes = treeUtils.countNodes(tree);
      branches = treeUtils.countLeaves(tree);
    }
  }
  times.sort((a, b) => a - b);

  return {
    mean: times.reduce((a, b) => a + b, 0) / times.length,
    median: times[Math.floor(times.length / 2)],
    min: times[0],
    max: times[times.length - 1],
    p95: times[Math.floor(times.length * 0.95)],
    stddev: Math.sqrt(times.reduce((s, t) => s + (t - times.reduce((a, b) => a + b, 0) / times.length) ** 2, 0) / times.length),
    runs: times.length,
    nodes,
    branches,
  };
}

async function main() {
  const path = require('path');
  const fs = require('fs');
  const result = {};

  try {
    const mde = require('./lib/engine');

    // Load with bytecode if bytecode-loader exists (post-compose era)
    const codePath = path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
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

    const calc = mde.load(
      path.join(__dirname, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill'),
      loadOpts
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    Object.assign(result, benchExplore(state, calc));
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

function runBench(cwd, warmup, runs) {
  return new Promise((resolve) => {
    const script = makeBenchScript(warmup, runs);
    const scriptPath = path.join(cwd, '_bench_history_runner.js');
    fs.writeFileSync(scriptPath, script);

    const child = spawn(process.execPath, ['--expose-gc', scriptPath], {
      cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
      env: { ...process.env, NODE_PATH: path.join(cwd, 'node_modules') },
      timeout: 120_000, // 2 min timeout per commit
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

function displayTable(results) {
  // Baseline = newest successful result
  let baselineMean = null;
  for (const r of results) {
    if (r.data && !r.data.error) {
      baselineMean = r.data.mean;
      break;
    }
  }

  const maxSubj = Math.min(40, Math.max(20, ...results.map(r => r.subject.length)));

  const cols = ['#', 'Commit', 'Date', 'Message', 'Nodes', 'Leaves', 'Mean', 'StdDev', 'vs HEAD'];
  const rows = [];

  for (let i = 0; i < results.length; i++) {
    const r = results[i];
    const row = [
      String(i),
      r.shortHash,
      r.date,
      r.subject.slice(0, maxSubj),
    ];

    if (r.data && r.data.error) {
      row.push('—', '—', 'ERROR', '—', '—');
    } else if (!r.data) {
      row.push('—', '—', '—', '—', '—');
    } else {
      row.push(
        String(r.data.nodes),
        String(r.data.branches),
        fmtMs(r.data.mean),
        fmtMs(r.data.stddev),
        fmtChange(r.data.mean, baselineMean),
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
      // Right-align numeric columns
      if (i >= 4) return (c || '').padStart(widths[i]);
      return (c || '').padEnd(widths[i]);
    }).join('  '));
  }

  console.log(widths.map(w => '─'.repeat(w)).join('──'));

  // Summary stats
  const successful = results.filter(r => r.data && !r.data.error);
  const vals = successful.map(r => r.data.mean);
  if (vals.length > 0) {
    console.log(`min=${fmtMs(Math.min(...vals))} max=${fmtMs(Math.max(...vals))} range=${((Math.max(...vals)/Math.min(...vals) - 1)*100).toFixed(1)}%`);
  }
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
  console.log(`  Commits:  ${commits.length} (from ${opts.branch})`);
  console.log(`  Warmup:   ${opts.warmup} runs`);
  console.log(`  Timed:    ${opts.runs} runs`);
  console.log(`  Range:    ${commits[commits.length - 1].shortHash}..${commits[0].shortHash}`);
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
      data = await runBench(ROOT, opts.warmup, opts.runs);
    } else {
      currentHash = c.fullHash;
      let wtPath;
      try {
        wtPath = setupWorktree(c.fullHash);
        data = await runBench(wtPath, opts.warmup, opts.runs);
      } catch (err) {
        data = { error: err.message };
      } finally {
        cleanupWorktree(c.fullHash);
        currentHash = null;
      }
    }

    const elapsed = ((performance.now() - t0) / 1000).toFixed(1);

    // Format inline result
    if (data.error) {
      process.stdout.write(`ERROR (${elapsed}s)\n`);
    } else {
      process.stdout.write(`${fmtMs(data.mean)} ±${fmtMs(data.stddev)} [${data.nodes} nodes, ${data.branches} leaves] (${elapsed}s)\n`);
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
      config: { runs: opts.runs, warmup: opts.warmup, commits: opts.commits, branch: opts.branch },
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
