#!/usr/bin/env node
/**
 * TODO_0216 Phase 0 H9 — baseline snapshot
 *
 * Measures the fuse-pipeline hot spot (mde.load() of the solc-symbolic
 * multisig fixture) along with explore runtime and a few sibling loads.
 *
 * Writes JSON to doc/_scratch/0216-baseline.json.
 *
 * Usage:
 *   node --expose-gc tools/0216-baseline.js [--iterations=N]
 */

const path = require('path');
const fs = require('fs');
const { execSync } = require('child_process');
const { performance } = require('perf_hooks');

const ROOT = path.resolve(__dirname, '..');
const OUT = path.join(ROOT, 'doc/_scratch/0216-baseline.json');

function parseArgs() {
  let iterations = 3;
  for (const a of process.argv.slice(2)) {
    if (a.startsWith('--iterations=')) iterations = parseInt(a.slice(13), 10);
  }
  return { iterations };
}

function stats(times) {
  times.sort((a, b) => a - b);
  return {
    mean: times.reduce((a, b) => a + b, 0) / times.length,
    p50: times[Math.floor(times.length * 0.5)],
    p95: times[Math.floor(Math.max(0, times.length * 0.95 - 1))],
    min: times[0],
    max: times[times.length - 1],
    n: times.length,
  };
}

// Warmup + time a thunk.
function timeOne(fn, iterations, warmup = 1) {
  for (let i = 0; i < warmup; i++) fn();
  if (global.gc) global.gc();
  const times = [];
  for (let i = 0; i < iterations; i++) {
    const t0 = performance.now();
    fn();
    times.push(performance.now() - t0);
  }
  return stats(times);
}

async function main() {
  const { iterations } = parseArgs();

  const commit = execSync('git rev-parse HEAD', { cwd: ROOT, encoding: 'utf8' }).trim();
  const shortSha = commit.slice(0, 7);
  const subject = execSync(`git log -1 --format=%s`, { cwd: ROOT, encoding: 'utf8' }).trim();

  const mde = require('../lib/engine');
  const Store = require('../lib/kernel/store');

  const results = {};

  // 1. mde.load() of multisig_nocall_solc_symbolic.ill — fuse-pipeline hot spot
  {
    const fixture = path.join(ROOT, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
    results['load.multisig_nocall_solc_symbolic'] = timeOne(() => {
      Store.clear();
      mde.load(fixture);
    }, iterations);
  }

  // 2. mde.load() of multisig_nocall_solc.ill — forward-only load
  {
    const fixture = path.join(ROOT, 'calculus/ill/programs/multisig_nocall_solc.ill');
    results['load.multisig_nocall_solc'] = timeOne(() => {
      Store.clear();
      mde.load(fixture);
    }, iterations);
  }

  // 3. mde.load() of multisig.ill — smaller chain fusion
  {
    const fixture = path.join(ROOT, 'calculus/ill/programs/multisig.ill');
    results['load.multisig'] = timeOne(() => {
      Store.clear();
      mde.load(fixture);
    }, iterations);
  }

  // 4. Explore runtime — symex of the symbolic multisig
  {
    Store.clear();
    const { loadBytecode, bytecodeArrGetGuard } = require('../lib/engine/ill/bytecode-loader');
    const codePath = path.join(ROOT, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
    const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
    const bc = loadBytecode(hex);
    const calc = mde.load(
      path.join(ROOT, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill'),
      { extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard }
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    results['explore.solc_symbolic'] = timeOne(
      () => { calc.explore(state, { maxDepth: 400, structuralMemo: true, dangerouslyUseFFI: true }); },
      iterations
    );
  }

  const payload = {
    schema: '0216-baseline/v1',
    commit,
    shortSha,
    subject,
    iterations,
    recorded: new Date().toISOString(),
    node: process.version,
    results,
  };

  fs.mkdirSync(path.dirname(OUT), { recursive: true });
  fs.writeFileSync(OUT, JSON.stringify(payload, null, 2));
  console.log(`Wrote ${OUT}`);
  console.log(JSON.stringify(payload, null, 2));
}

main().catch(err => { console.error(err); process.exit(1); });
