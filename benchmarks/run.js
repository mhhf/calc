#!/usr/bin/env node
/**
 * Main Benchmark Runner
 *
 * Usage:
 *   node benchmarks/run.js                    # Run all benchmarks
 *   node benchmarks/run.js --category=proof   # Run proof benchmarks only
 *   node benchmarks/run.js --category=micro   # Run micro benchmarks only
 *   node benchmarks/run.js --save             # Save results to baseline.json
 *   node benchmarks/run.js --compare          # Compare with baseline
 */

const { BenchmarkRunner } = require('./lib/runner');
const { runProofBenchmarks, runWithProfiling } = require('./proof/proofs.bench');
const { runMguBenchmarks } = require('./micro/mgu.bench');
const fs = require('fs');
const path = require('path');

// Parse CLI arguments
const args = process.argv.slice(2);
const category = args.find(a => a.startsWith('--category='))?.split('=')[1] || 'all';
const shouldSave = args.includes('--save');
const shouldCompare = args.includes('--compare');
const iterations = parseInt(args.find(a => a.startsWith('--iterations='))?.split('=')[1] || '20');

// Create runner
const runner = new BenchmarkRunner({
  iterations,
  warmup: Math.max(3, Math.floor(iterations / 4)),
});

console.log('='.repeat(60));
console.log('CALC Benchmark Suite');
console.log('='.repeat(60));
console.log(`Category: ${category}`);
console.log(`Iterations: ${iterations}`);
console.log(`GC available: ${!!global.gc}`);
console.log('');

// Run appropriate benchmarks
if (category === 'all' || category === 'proof') {
  console.log('--- Proof Search Benchmarks ---\n');
  runProofBenchmarks(runner, 'all');
}

if (category === 'all' || category === 'micro') {
  console.log('--- Micro Benchmarks ---\n');
  runMguBenchmarks(runner);
}

// Report results
console.log('');
console.log(runner.report());

// Save if requested
const baselineFile = path.join(__dirname, 'baseline.json');
if (shouldSave) {
  console.log(`\nSaving results to ${baselineFile}...`);
  runner.save(baselineFile);
  console.log('Done.');
}

// Compare if requested
if (shouldCompare) {
  if (fs.existsSync(baselineFile)) {
    const baseline = JSON.parse(fs.readFileSync(baselineFile, 'utf8'));
    console.log('\n');
    console.log(runner.compare(baseline));
  } else {
    console.log('\nNo baseline found. Run with --save first.');
  }
}

// Always show profiling summary for proof benchmarks
if (category === 'all' || category === 'proof') {
  console.log('\n--- Operation Counts (single run per proof) ---\n');
  const profilingResults = runWithProfiling(runner, 'all');

  // Find max name length
  const names = Object.keys(profilingResults);
  const maxName = Math.max(...names.map(n => n.length));

  for (const [name, stats] of Object.entries(profilingResults)) {
    const pad = ' '.repeat(maxName - name.length);
    const mgu = stats.counters['mgu.call'] || 0;
    const sub = stats.counters['substitute.call'] || 0;
    const copy = stats.counters['sequent.copy'] || 0;
    console.log(`${name}${pad}  mgu: ${mgu}, sub: ${sub}, copy: ${copy}`);
  }
}

console.log('\n' + '='.repeat(60));
console.log('Benchmark complete');
console.log('='.repeat(60));
