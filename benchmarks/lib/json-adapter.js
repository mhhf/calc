#!/usr/bin/env node
/**
 * JSON Benchmark Adapter
 *
 * Runs a benchmark suite and outputs structured JSON between markers
 * for machine-readable extraction by bench-compare.js.
 *
 * Usage:
 *   node --expose-gc benchmarks/lib/json-adapter.js --suite=proof [--iterations=20]
 *   node --expose-gc benchmarks/lib/json-adapter.js --suite=engine [--iterations=20]
 *   node --expose-gc benchmarks/lib/json-adapter.js --suite=explore [--iterations=10]
 */

const START_MARKER = '---BENCH-JSON---';
const END_MARKER = '---BENCH-JSON---';

function parseArgs() {
  const args = process.argv.slice(2);
  let suite = 'proof';
  let iterations = 20;

  for (const arg of args) {
    if (arg.startsWith('--suite=')) suite = arg.slice(8);
    if (arg.startsWith('--iterations=')) iterations = parseInt(arg.slice(13), 10);
  }

  return { suite, iterations };
}

function emitJSON(data) {
  console.log(START_MARKER);
  console.log(JSON.stringify(data));
  console.log(END_MARKER);
}

// ─── Suite: proof ────────────────────────────────────────────────────────────

async function runProof(iterations) {
  const { BenchmarkRunner } = require('./runner');
  const { runV2ProofBenchmarks } = require('../proof/proofs-v2.bench.js');

  const runner = new BenchmarkRunner({ iterations, warmup: 3 });
  await runV2ProofBenchmarks(runner, 'all');

  const results = {};
  for (const [name, stats] of Object.entries(runner.getResults())) {
    results[name] = {
      mean: stats.mean,
      p50: stats.p50,
      p95: stats.p95,
      min: stats.min,
      max: stats.max,
    };
  }
  return results;
}

// ─── Suite: engine ───────────────────────────────────────────────────────────

async function runEngine(iterations) {
  const { runBenchmarks } = require('../mde/backward.bench.js');

  const raw = await runBenchmarks({
    categories: ['easy', 'medium', 'complex'],
    iterations,
    warmup: 3,
  });

  const results = {};
  for (const [cat, benches] of Object.entries(raw)) {
    for (const b of benches) {
      const key = `engine.${cat}.${b.desc.replace(/\s+/g, '_')}`;
      results[key] = {
        mean: b.mean,
        p50: b.p50,
        p95: b.p95,
        min: b.min,
        max: b.max,
      };
    }
  }
  return results;
}

// ─── Suite: explore ──────────────────────────────────────────────────────────

function benchOne(label, state, forwardRules, calcCtx, exploreOpts, iterations) {
  const { performance } = require('perf_hooks');
  const explore = require('../../lib/engine/explore');
  const WARMUP = 3;

  for (let i = 0; i < WARMUP; i++) {
    explore.explore(state, forwardRules, exploreOpts);
  }
  if (global.gc) global.gc();

  const times = [];
  for (let i = 0; i < iterations; i++) {
    const t0 = performance.now();
    explore.explore(state, forwardRules, exploreOpts);
    times.push(performance.now() - t0);
  }
  times.sort((a, b) => a - b);
  return {
    mean: times.reduce((a, b) => a + b, 0) / times.length,
    p50: times[Math.floor(times.length * 0.5)],
    p95: times[Math.floor(times.length * 0.95)],
    min: times[0],
    max: times[times.length - 1],
  };
}

async function runExplore(iterations) {
  const path = require('path');
  const mde = require('../../lib/engine');

  const results = {};

  // 1. Small multisig (committed-choice baseline)
  {
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    const calcCtx = { clauses: calc.clauses, definitions: calc.definitions };
    results['explore.multisig'] = benchOne('multisig', state, calc.forwardRules, calcCtx,
      { maxDepth: 200, calc: calcCtx }, iterations);
  }

  // 2. Solc symbolic multisig with bytecode (realistic E2E)
  {
    const fs = require('fs');
    const { loadBytecode, bytecodeArrGetGuard } = require('../../lib/engine/ill/bytecode-loader');
    const codePath = path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');
    const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
    const bc = loadBytecode(hex);
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill'),
      { extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard }
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    const calcCtx = { clauses: calc.clauses, definitions: calc.definitions };
    results['explore.solc_symbolic'] = benchOne('solc_symbolic', state, calc.forwardRules, calcCtx,
      { maxDepth: 400, calc: calcCtx, structuralMemo: true, dangerouslyUseFFI: true }, iterations);
  }

  return results;
}

// ─── Main ────────────────────────────────────────────────────────────────────

async function main() {
  const { suite, iterations } = parseArgs();

  const suites = { proof: runProof, engine: runEngine, explore: runExplore };

  if (!suites[suite]) {
    console.error(`Unknown suite: ${suite}. Available: ${Object.keys(suites).join(', ')}`);
    process.exit(1);
  }

  try {
    const results = await suites[suite](iterations);
    emitJSON(results);
  } catch (err) {
    console.error(`Suite "${suite}" failed: ${err.message}`);
    process.exit(1);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
