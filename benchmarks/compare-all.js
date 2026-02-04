#!/usr/bin/env node
/**
 * Compare v1 (base), v1 (with store), and v2.1 provers
 *
 * Versions:
 *   v1-base:  Original v1 prover
 *   v1-store: v1 with content-addressed store
 *   v2.1:     Focused prover with content-addressed AST + optimized conversions
 *
 * Usage:
 *   node --expose-gc benchmarks/compare-all.js
 *   node --expose-gc benchmarks/compare-all.js --category=simple
 *   node --expose-gc benchmarks/compare-all.js --iterations=50
 */

const { BenchmarkRunner } = require('./lib/runner');
const { runProofBenchmarks, runProofBenchmarksWithStore } = require('./proof/proofs.bench');
const { runV2ProofBenchmarks, runV2WithProfiling, getProver } = require('./proof/proofs-v2.bench');
const fs = require('fs');
const path = require('path');

// Parse CLI arguments
const args = process.argv.slice(2);
const category = args.find(a => a.startsWith('--category='))?.split('=')[1] || 'all';
const iterations = parseInt(args.find(a => a.startsWith('--iterations='))?.split('=')[1] || '20');
const shouldSave = args.includes('--save');

async function main() {
  console.log('='.repeat(70));
  console.log('CALC Prover Comparison: v1 (base) vs v1 (store) vs v2.1 (focused)');
  console.log('='.repeat(70));
  console.log(`Category: ${category}`);
  console.log(`Iterations: ${iterations}`);
  console.log(`GC available: ${!!global.gc}`);
  console.log('');

  // Initialize v2.1 prover before benchmarks (one-time cost)
  console.log('Initializing v2.1 prover...');
  await getProver();
  console.log('');

  // Create runners for each variant
  const runnerV1Base = new BenchmarkRunner({ iterations, warmup: Math.max(3, Math.floor(iterations / 4)) });
  const runnerV1Store = new BenchmarkRunner({ iterations, warmup: Math.max(3, Math.floor(iterations / 4)) });
  const runnerV2 = new BenchmarkRunner({ iterations, warmup: Math.max(3, Math.floor(iterations / 4)) });

  // Run v1 base
  console.log('--- v1 (base) ---');
  runProofBenchmarks(runnerV1Base, category);
  console.log('');

  // Run v1 with store
  console.log('--- v1 (content-addressed store) ---');
  runProofBenchmarksWithStore(runnerV1Store, category);
  console.log('');

  // Run v2.1
  console.log('--- v2.1 (focused prover) ---');
  await runV2ProofBenchmarks(runnerV2, category);
  console.log('');

  // Collect results
  const v1BaseResults = runnerV1Base.getResults();
  const v1StoreResults = runnerV1Store.getResults();
  const v2Results = runnerV2.getResults();

  // Print comparison table
  console.log('='.repeat(70));
  console.log('COMPARISON (mean time in ms)');
  console.log('='.repeat(70));
  console.log('');

  // Get all test names
  const testNames = Object.keys(v1BaseResults).map(n => n.replace('proof.', ''));

  // Find max name length
  const maxName = Math.max(...testNames.map(n => n.length), 15);

  // Header
  const header = [
    'Test'.padEnd(maxName),
    'v1-base'.padStart(10),
    'v1-store'.padStart(10),
    'v2.1'.padStart(10),
    'v2.1/v1-base'.padStart(13),
    'v2.1/v1-store'.padStart(14),
  ].join('  ');
  console.log(header);
  console.log('-'.repeat(header.length));

  const speedups = { vsBase: [], vsStore: [] };

  for (const name of testNames) {
    const v1Base = v1BaseResults[`proof.${name}`];
    const v1Store = v1StoreResults[`proof.store.${name}`];
    const v2 = v2Results[`v2.proof.${name}`];

    if (!v1Base || !v2) continue;

    const v2VsBase = v2.mean / v1Base.mean;
    const v2VsStore = v1Store ? v2.mean / v1Store.mean : null;

    speedups.vsBase.push(v2VsBase);
    if (v2VsStore) speedups.vsStore.push(v2VsStore);

    // Format speedup
    const formatSpeedup = (ratio) => {
      if (ratio === null) return 'N/A'.padStart(12);
      if (ratio < 1) {
        return `${(1/ratio).toFixed(2)}x faster`.padStart(12);
      } else if (ratio > 1) {
        return `${ratio.toFixed(2)}x slower`.padStart(12);
      } else {
        return '~same'.padStart(12);
      }
    };

    const row = [
      name.padEnd(maxName),
      v1Base.mean.toFixed(3).padStart(10),
      v1Store ? v1Store.mean.toFixed(3).padStart(10) : 'N/A'.padStart(10),
      v2.mean.toFixed(3).padStart(10),
      formatSpeedup(v2VsBase),
      formatSpeedup(v2VsStore),
    ].join('  ');
    console.log(row);
  }

  // Summary
  console.log('-'.repeat(header.length));

  const avgVsBase = speedups.vsBase.reduce((a, b) => a + b, 0) / speedups.vsBase.length;
  const avgVsStore = speedups.vsStore.reduce((a, b) => a + b, 0) / speedups.vsStore.length;

  const geoMeanVsBase = Math.pow(speedups.vsBase.reduce((a, b) => a * b, 1), 1 / speedups.vsBase.length);
  const geoMeanVsStore = Math.pow(speedups.vsStore.reduce((a, b) => a * b, 1), 1 / speedups.vsStore.length);

  console.log('');
  console.log('Summary:');
  console.log(`  v2.1 vs v1-base:  geometric mean ${geoMeanVsBase.toFixed(3)}x (${geoMeanVsBase < 1 ? 'faster' : 'slower'})`);
  console.log(`  v2.1 vs v1-store: geometric mean ${geoMeanVsStore.toFixed(3)}x (${geoMeanVsStore < 1 ? 'faster' : 'slower'})`);
  console.log('');

  // Detailed stats
  console.log('='.repeat(70));
  console.log('DETAILED RESULTS');
  console.log('='.repeat(70));
  console.log('');
  console.log('--- v1 (base) ---');
  console.log(runnerV1Base.report());
  console.log('');
  console.log('--- v1 (store) ---');
  console.log(runnerV1Store.report());
  console.log('');
  console.log('--- v2.1 (focused) ---');
  console.log(runnerV2.report());

  // v2.1 proof tree stats
  console.log('');
  console.log('='.repeat(70));
  console.log('v2.1 PROOF TREE STATS');
  console.log('='.repeat(70));
  const v2Stats = await runV2WithProfiling(category);
  console.log('');
  for (const [name, s] of Object.entries(v2Stats)) {
    console.log(`${name.padEnd(maxName)}  size: ${String(s.treeSize).padStart(3)}, depth: ${s.treeDepth}`);
  }

  // Save combined results if requested
  if (shouldSave) {
    const outputFile = path.join(__dirname, 'comparison-results.json');
    const output = {
      timestamp: new Date().toISOString(),
      category,
      iterations,
      v1_base: runnerV1Base.getResults(),
      v1_store: runnerV1Store.getResults(),
      v2: runnerV2.getResults(),
      summary: {
        geoMeanVsBase,
        geoMeanVsStore,
        avgVsBase,
        avgVsStore,
      },
    };
    fs.writeFileSync(outputFile, JSON.stringify(output, null, 2));
    console.log(`\nResults saved to ${outputFile}`);
  }

  console.log('\n' + '='.repeat(70));
  console.log('Benchmark complete');
  console.log('='.repeat(70));
}

main().catch(console.error);
