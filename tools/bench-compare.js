#!/usr/bin/env node
/**
 * Benchmark Comparison Tool
 *
 * Compares benchmark performance between HEAD and a previous commit
 * using git worktrees for isolation.
 *
 * Usage:
 *   node --expose-gc tools/bench-compare.js [commit] [--suite=proof|engine|explore] [--iterations=N]
 *
 * Defaults: commit=HEAD~1, suite=proof, iterations=20
 *
 * Examples:
 *   node --expose-gc tools/bench-compare.js HEAD~1 --suite=proof
 *   node --expose-gc tools/bench-compare.js abc123 --suite=engine --iterations=10
 */

const { execSync, spawn } = require('child_process');
const path = require('path');
const fs = require('fs');

const ROOT = path.resolve(__dirname, '..');
const WORKTREE_DIR = path.join(ROOT, '.bench-compare');
const ADAPTER = path.join(ROOT, 'benchmarks/lib/json-adapter.js');
const START_MARKER = '---BENCH-JSON---';

// ─── Arg parsing ─────────────────────────────────────────────────────────────

function parseArgs() {
  const args = process.argv.slice(2);
  let commit = 'HEAD~1';
  let suite = 'proof';
  let iterations = 20;

  for (const arg of args) {
    if (arg.startsWith('--suite=')) suite = arg.slice(8);
    else if (arg.startsWith('--iterations=')) iterations = parseInt(arg.slice(13), 10);
    else if (!arg.startsWith('--')) commit = arg;
  }

  return { commit, suite, iterations };
}

// ─── Git helpers ─────────────────────────────────────────────────────────────

function resolveCommit(ref) {
  return execSync(`git rev-parse --short ${ref}`, { cwd: ROOT, encoding: 'utf8' }).trim();
}

function resolveFullCommit(ref) {
  return execSync(`git rev-parse "${ref}"`, { cwd: ROOT, encoding: 'utf8' }).trim();
}

function commitSubject(ref) {
  return execSync(`git log -1 --format=%s "${ref}" --`, { cwd: ROOT, encoding: 'utf8' }).trim();
}

// ─── Run adapter in a directory ──────────────────────────────────────────────

function runAdapter(cwd, suite, iterations) {
  return new Promise((resolve, reject) => {
    const args = [
      '--expose-gc',
      path.join(cwd, 'benchmarks/lib/json-adapter.js'),
      `--suite=${suite}`,
      `--iterations=${iterations}`,
    ];

    const child = spawn(process.execPath, args, {
      cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
      env: { ...process.env, NODE_PATH: path.join(cwd, 'node_modules') },
    });

    let stdout = '';
    let stderr = '';
    child.stdout.on('data', d => { stdout += d; });
    child.stderr.on('data', d => { stderr += d; });

    child.on('close', code => {
      if (code !== 0) {
        return reject(new Error(`Adapter exited ${code}: ${stderr.slice(0, 500)}`));
      }

      // Extract JSON between markers
      const lines = stdout.split('\n');
      const startIdx = lines.indexOf(START_MARKER);
      const endIdx = lines.lastIndexOf(START_MARKER);

      if (startIdx === -1 || startIdx === endIdx) {
        return reject(new Error(`No JSON markers found in output.\nstdout: ${stdout.slice(0, 500)}`));
      }

      try {
        const json = lines.slice(startIdx + 1, endIdx).join('\n');
        resolve(JSON.parse(json));
      } catch (err) {
        reject(new Error(`Failed to parse JSON: ${err.message}\nRaw: ${stdout.slice(0, 500)}`));
      }
    });
  });
}

// ─── Worktree management ─────────────────────────────────────────────────────

function setupWorktree(commitHash) {
  const wtPath = path.join(WORKTREE_DIR, commitHash);

  // Remove stale worktree if it exists
  if (fs.existsSync(wtPath)) {
    console.log(`  Removing stale worktree...`);
    execSync(`git worktree remove --force "${wtPath}"`, { cwd: ROOT, stdio: 'ignore' });
  }

  fs.mkdirSync(WORKTREE_DIR, { recursive: true });

  // Create worktree
  execSync(`git worktree add "${wtPath}" ${commitHash} --detach`, {
    cwd: ROOT,
    stdio: 'ignore',
  });

  // Symlink node_modules
  const nmSrc = path.join(ROOT, 'node_modules');
  const nmDst = path.join(wtPath, 'node_modules');
  if (!fs.existsSync(nmDst)) {
    fs.symlinkSync(nmSrc, nmDst);
  }

  // Copy json-adapter.js into worktree (may not exist at old commit)
  const adapterDst = path.join(wtPath, 'benchmarks/lib/json-adapter.js');
  if (!fs.existsSync(adapterDst)) {
    fs.mkdirSync(path.dirname(adapterDst), { recursive: true });
    fs.copyFileSync(ADAPTER, adapterDst);
  }

  // Copy runner.js if missing (json-adapter depends on it)
  const runnerSrc = path.join(ROOT, 'benchmarks/lib/runner.js');
  const runnerDst = path.join(wtPath, 'benchmarks/lib/runner.js');
  if (!fs.existsSync(runnerDst)) {
    fs.copyFileSync(runnerSrc, runnerDst);
  }

  return wtPath;
}

function cleanupWorktree(commitHash) {
  const wtPath = path.join(WORKTREE_DIR, commitHash);
  try {
    if (fs.existsSync(wtPath)) {
      execSync(`git worktree remove --force "${wtPath}"`, { cwd: ROOT, stdio: 'ignore' });
    }
    // Remove parent dir if empty
    if (fs.existsSync(WORKTREE_DIR) && fs.readdirSync(WORKTREE_DIR).length === 0) {
      fs.rmdirSync(WORKTREE_DIR);
    }
  } catch (e) {
    console.error(`Warning: cleanup failed: ${e.message}`);
  }
}

// ─── Display ─────────────────────────────────────────────────────────────────

function fmtMs(ms) {
  if (ms < 0.01) return `${(ms * 1000).toFixed(1)}µs`;
  if (ms < 1) return `${(ms * 1000).toFixed(0)}µs`;
  return `${ms.toFixed(3)}ms`;
}

function displayComparison(headResults, baseResults, headLabel, baseLabel) {
  const allKeys = new Set([...Object.keys(headResults), ...Object.keys(baseResults)]);
  const keys = [...allKeys].sort();

  if (keys.length === 0) {
    console.log('No benchmarks to compare.');
    return;
  }

  const maxNameLen = Math.max(20, ...keys.map(k => k.length));
  const hdr = [
    'Benchmark'.padEnd(maxNameLen),
    `${headLabel} mean`.padStart(14),
    `${baseLabel} mean`.padStart(14),
    'Change'.padStart(10),
    'Status'.padStart(8),
  ].join('  ');

  console.log();
  console.log(hdr);
  console.log('─'.repeat(hdr.length));

  let logRatioSum = 0;
  let logRatioCount = 0;

  for (const key of keys) {
    const head = headResults[key];
    const base = baseResults[key];

    if (!head || !base) {
      const label = head ? 'NEW' : 'REMOVED';
      const mean = head ? fmtMs(head.mean) : fmtMs(base.mean);
      console.log(`${key.padEnd(maxNameLen)}  ${mean.padStart(14)}  ${'—'.padStart(14)}  ${'—'.padStart(10)}  ${label.padStart(8)}`);
      continue;
    }

    const change = ((head.mean - base.mean) / base.mean) * 100;
    const sign = change > 0 ? '+' : '';
    const status = Math.abs(change) < 5 ? '~' : change > 0 ? 'SLOWER' : 'FASTER';

    console.log([
      key.padEnd(maxNameLen),
      fmtMs(head.mean).padStart(14),
      fmtMs(base.mean).padStart(14),
      `${sign}${change.toFixed(1)}%`.padStart(10),
      status.padStart(8),
    ].join('  '));

    if (head.mean > 0 && base.mean > 0) {
      logRatioSum += Math.log(head.mean / base.mean);
      logRatioCount++;
    }
  }

  console.log('─'.repeat(hdr.length));

  if (logRatioCount > 0) {
    const geoMean = (Math.exp(logRatioSum / logRatioCount) - 1) * 100;
    const sign = geoMean > 0 ? '+' : '';
    console.log(`Geometric mean change: ${sign}${geoMean.toFixed(1)}%`);
  }

  console.log();
}

// ─── Main ────────────────────────────────────────────────────────────────────

async function main() {
  const { commit, suite, iterations } = parseArgs();

  const headHash = resolveCommit('HEAD');
  const baseHash = resolveCommit(commit);
  const baseFullHash = resolveFullCommit(commit);

  console.log(`\nBenchmark Comparison: ${suite}`);
  console.log(`  HEAD:     ${headHash} (${commitSubject('HEAD')})`);
  console.log(`  Compare:  ${baseHash} (${commitSubject(baseFullHash)})`);
  console.log(`  Iterations: ${iterations}`);
  console.log();

  // Cleanup handler
  let needsCleanup = true;
  const cleanup = () => {
    if (needsCleanup) {
      needsCleanup = false;
      console.log('\nCleaning up worktree...');
      cleanupWorktree(baseFullHash);
    }
  };
  process.on('SIGINT', () => { cleanup(); process.exit(130); });
  process.on('SIGTERM', () => { cleanup(); process.exit(143); });

  // Step 1: Run at HEAD
  console.log(`Running ${suite} benchmarks at HEAD (${headHash})...`);
  let headResults;
  try {
    headResults = await runAdapter(ROOT, suite, iterations);
  } catch (err) {
    console.error(`HEAD benchmark failed: ${err.message}`);
    process.exit(1);
  }
  console.log(`  ${Object.keys(headResults).length} benchmarks collected.`);

  // Step 2: Setup worktree at comparison commit
  console.log(`\nSetting up worktree at ${baseHash}...`);
  let wtPath;
  try {
    wtPath = setupWorktree(baseFullHash);
  } catch (err) {
    console.error(`Worktree setup failed: ${err.message}`);
    process.exit(1);
  }
  console.log(`  Worktree ready at ${wtPath}`);

  // Step 3: Run at comparison commit
  console.log(`\nRunning ${suite} benchmarks at ${baseHash}...`);
  let baseResults;
  try {
    baseResults = await runAdapter(wtPath, suite, iterations);
  } catch (err) {
    console.error(`Benchmark at ${baseHash} failed: ${err.message}`);
    cleanup();
    process.exit(1);
  }
  console.log(`  ${Object.keys(baseResults).length} benchmarks collected.`);

  // Step 4: Cleanup
  cleanup();

  // Step 5: Display
  displayComparison(headResults, baseResults, headHash, baseHash);
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
