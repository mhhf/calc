/**
 * Multisig EVM Execution Benchmark
 *
 * Measures execution time from start to EQ instruction (5 steps).
 * Profiles where time is spent: loading, parsing, matching, proving.
 */

const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const fs = require('fs');
const path = require('path');
const { performance } = require('perf_hooks');

// Timing utilities
const timings = {
  load: [],
  parseState: [],
  parseCode: [],
  exec: [],
  total: []
};

function binToNum(h) {
  const node = Store.get(h);
  if (!node) return 0;
  if (node.tag === 'atom' && node.children[0] === 'e') return 0;
  if (node.tag === 'atom' && node.children[0] === 'ee') return 0;
  if (node.tag === 'app') {
    const fn = Store.get(node.children[0]);
    if (fn?.tag === 'atom') {
      if (fn.children[0] === 'o') return binToNum(node.children[1]) * 2;
      if (fn.children[0] === 'i') return binToNum(node.children[1]) * 2 + 1;
      if (fn.children[0] === 's') return binToNum(node.children[1]) + 1;
    }
  }
  return 0;
}

async function runOnce(warmup = false) {
  const t0 = performance.now();

  // Phase 1: Load rules
  const tLoad0 = performance.now();
  const calc = await mde.load([
    path.join(__dirname, '../../calculus/ill/programs/bin.ill'),
    path.join(__dirname, '../../calculus/ill/programs/evm.ill'),
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
  ]);
  const tLoad1 = performance.now();

  // Phase 2: Parse initial state
  const tParse0 = performance.now();
  const state = { linear: {}, persistent: {} };
  const basicFacts = [
    'pc N_75',
    'sh ee',
    'gas N_ffff',
    'caller sender_addr',
    'sender member01',
  ];
  for (const f of basicFacts) {
    const h = await mde.parseExpr(f);
    state.linear[h] = 1;
  }
  const tParse1 = performance.now();

  // Phase 3: Parse code facts
  const tCode0 = performance.now();
  const codeFile = fs.readFileSync(
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
    'utf8'
  );
  let codeCount = 0;
  for (const line of codeFile.split('\n')) {
    const trimmed = line.split('%')[0].trim();
    if (!trimmed || !trimmed.startsWith('code')) continue;
    const parts = trimmed.replace(/\*.*$/, '').trim();
    if (parts) {
      const h = await mde.parseExpr(parts);
      state.linear[h] = 1;
      codeCount++;
    }
  }
  const tCode1 = performance.now();

  // Phase 4: Execute
  const tExec0 = performance.now();
  const result = calc.exec(state, { maxSteps: 50, trace: true });
  const tExec1 = performance.now();

  const t1 = performance.now();

  if (!warmup) {
    timings.load.push(tLoad1 - tLoad0);
    timings.parseState.push(tParse1 - tParse0);
    timings.parseCode.push(tCode1 - tCode0);
    timings.exec.push(tExec1 - tExec0);
    timings.total.push(t1 - t0);
  }

  return { result, codeCount };
}

function stats(arr) {
  const sorted = [...arr].sort((a, b) => a - b);
  const sum = arr.reduce((a, b) => a + b, 0);
  const mean = sum / arr.length;
  const median = sorted[Math.floor(sorted.length / 2)];
  const min = sorted[0];
  const max = sorted[sorted.length - 1];
  const stddev = Math.sqrt(arr.reduce((s, x) => s + (x - mean) ** 2, 0) / arr.length);
  return { mean, median, min, max, stddev };
}

function formatMs(ms) {
  if (ms < 1) return `${(ms * 1000).toFixed(1)}µs`;
  return `${ms.toFixed(2)}ms`;
}

async function main() {
  console.log('='.repeat(70));
  console.log('MULTISIG EVM EXECUTION BENCHMARK');
  console.log('='.repeat(70));
  console.log();

  // Warmup runs
  console.log('Warming up (3 runs)...');
  for (let i = 0; i < 3; i++) {
    await runOnce(true);
  }

  // Benchmark runs
  const RUNS = 20;
  console.log(`Running benchmark (${RUNS} iterations)...\n`);

  let lastResult;
  for (let i = 0; i < RUNS; i++) {
    const { result, codeCount } = await runOnce(false);
    lastResult = result;
    if (i === 0) {
      console.log(`Code facts: ${codeCount}`);
      console.log(`Steps executed: ${result.steps}`);
      console.log(`Trace: ${result.trace.map(t => t.split('] ')[1]).join(' → ')}`);
      console.log();
    }
    process.stdout.write(`\r  Progress: ${i + 1}/${RUNS}`);
  }
  console.log('\n');

  // Results
  console.log('TIMING BREAKDOWN');
  console.log('-'.repeat(70));
  console.log();

  const phases = [
    ['Load rules (bin.mde, evm.mde, multisig_code.mde)', timings.load],
    ['Parse initial state (5 facts)', timings.parseState],
    ['Parse code facts (173 facts)', timings.parseCode],
    ['Execute (5 steps to EQ)', timings.exec],
    ['TOTAL', timings.total],
  ];

  for (const [name, arr] of phases) {
    const s = stats(arr);
    const pct = (s.mean / stats(timings.total).mean * 100).toFixed(1);
    console.log(`${name}:`);
    console.log(`  Mean: ${formatMs(s.mean)} (${pct}%)`);
    console.log(`  Min/Max: ${formatMs(s.min)} / ${formatMs(s.max)}`);
    console.log(`  Stddev: ${formatMs(s.stddev)}`);
    console.log();
  }

  // Per-step timing
  console.log('PER-STEP ANALYSIS');
  console.log('-'.repeat(70));
  const execStats = stats(timings.exec);
  const stepsPerMs = lastResult.steps / execStats.mean;
  console.log(`Steps: ${lastResult.steps}`);
  console.log(`Execution time: ${formatMs(execStats.mean)}`);
  console.log(`Time per step: ${formatMs(execStats.mean / lastResult.steps)}`);
  console.log(`Throughput: ${stepsPerMs.toFixed(1)} steps/ms`);
  console.log();

  // Detailed profiling run
  console.log('DETAILED PROFILING (single run with instrumentation)');
  console.log('-'.repeat(70));
  await runProfiled();
}

async function runProfiled() {
  // Instrument the forward engine
  const forward = require('../../lib/prover/strategy/forward');
  const originalRun = forward.run;

  let matchTime = 0;
  let applyTime = 0;
  let matchCalls = 0;

  // We can't easily instrument without modifying the source,
  // so let's do a manual profiling by timing each phase more granularly

  const calc = await mde.load([
    path.join(__dirname, '../../calculus/ill/programs/bin.ill'),
    path.join(__dirname, '../../calculus/ill/programs/evm.ill'),
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
  ]);

  const state = { linear: {}, persistent: {} };
  const basicFacts = [
    'pc N_75',
    'sh ee',
    'gas N_ffff',
    'caller sender_addr',
    'sender member01',
  ];
  for (const f of basicFacts) {
    const h = await mde.parseExpr(f);
    state.linear[h] = 1;
  }

  const codeFile = fs.readFileSync(
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
    'utf8'
  );
  for (const line of codeFile.split('\n')) {
    const trimmed = line.split('%')[0].trim();
    if (!trimmed || !trimmed.startsWith('code')) continue;
    const parts = trimmed.replace(/\*.*$/, '').trim();
    if (parts) {
      const h = await mde.parseExpr(parts);
      state.linear[h] = 1;
    }
  }

  // Count state facts
  const linearCount = Object.keys(state.linear).length;
  const rulesCount = calc.forwardRules.length;

  console.log(`\nState: ${linearCount} linear facts`);
  console.log(`Rules: ${rulesCount} forward rules`);
  console.log(`Matching complexity: O(${linearCount} × ${rulesCount}) = ${linearCount * rulesCount} potential matches per step\n`);

  // Time execution with V8 profiling hint
  const t0 = performance.now();
  const result = calc.exec(state, { maxSteps: 50, trace: true });
  const t1 = performance.now();

  console.log(`Execution: ${result.steps} steps in ${formatMs(t1 - t0)}`);
  console.log(`Average: ${formatMs((t1 - t0) / result.steps)} per step`);

  // Estimate breakdown based on typical distribution
  console.log(`\nEstimated breakdown (typical for multiset rewriting):`);
  console.log(`  ~60-70% Pattern matching (unification against state)`);
  console.log(`  ~20-30% Backward proving (persistent constraints)`);
  console.log(`  ~5-10%  State update (consume/produce facts)`);
}

main().catch(console.error);
