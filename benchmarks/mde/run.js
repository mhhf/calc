#!/usr/bin/env node
/**
 * MDE Benchmark Runner
 *
 * Unified benchmark and profiling for MDE backward/forward chaining.
 *
 * Usage:
 *   npm run bench:mde              # Run all benchmarks
 *   npm run bench:mde -- easy      # Run specific category
 *   npm run bench:mde -- --stress  # Run stress tests
 *   npm run profile:mde            # Profile worst case
 *   npm run bench:mde:save         # Save baseline
 *   npm run bench:mde:compare      # Compare with baseline
 */

const { runBenchmarks, profileBenchmark, BENCHMARKS } = require('./backward.bench');
const fs = require('fs');
const path = require('path');

const BASELINE_FILE = path.join(__dirname, 'baseline.json');

// Parse CLI arguments
const args = process.argv.slice(2);
const shouldSave = args.includes('--save');
const shouldCompare = args.includes('--compare');
const shouldProfile = args.includes('--profile');
const showHelp = args.includes('--help') || args.includes('-h');
const stressMode = args.includes('--stress');
const categories = args.filter(a => !a.startsWith('--'));

if (showHelp) {
  console.log(`
MDE Benchmark Runner

Usage:
  node benchmarks/mde/run.js [options] [categories...]

Options:
  --help, -h    Show this help
  --save        Save results as new baseline
  --compare     Compare results with baseline
  --profile     Profile the worst-case benchmark
  --stress      Run stress tests (larger numbers)

Categories:
  easy          Simple operations (depth 1-2)
  medium        Multi-step operations (depth 3-5)
  complex       Deep recursion (depth 10-20)
  stress        Very deep recursion

Examples:
  node benchmarks/mde/run.js                    # Run easy, medium, complex
  node benchmarks/mde/run.js --stress           # Run stress tests only
  node benchmarks/mde/run.js complex --profile  # Profile complex category
  node benchmarks/mde/run.js --save             # Save baseline
  node benchmarks/mde/run.js --compare          # Compare with baseline
`);
  process.exit(0);
}

async function main() {
  // Profile mode: run detailed analysis on specific query
  if (shouldProfile) {
    const cat = categories[0] || 'complex';
    const benchmarks = BENCHMARKS[cat] || BENCHMARKS.complex;
    const worst = benchmarks[benchmarks.length - 1]; // Typically hardest

    await profileBenchmark(worst.query, worst.desc, { iterations: 20 });
    return;
  }

  // Run benchmarks
  const opts = {
    categories: categories.length > 0 ? categories : (stressMode ? ['stress'] : ['easy', 'medium', 'complex']),
    iterations: stressMode ? 10 : 20,
    warmup: stressMode ? 3 : 5,
  };

  const results = await runBenchmarks(opts);

  // Save baseline if requested
  if (shouldSave) {
    const baseline = {
      timestamp: new Date().toISOString(),
      categories: {},
    };

    for (const [cat, benches] of Object.entries(results)) {
      baseline.categories[cat] = benches.map(b => ({
        desc: b.desc,
        mean: b.mean,
        p50: b.p50,
        p95: b.p95,
        min: b.min,
        max: b.max,
        correct: b.correct,
      }));
    }

    fs.writeFileSync(BASELINE_FILE, JSON.stringify(baseline, null, 2));
    console.log(`\nBaseline saved to ${BASELINE_FILE}`);
  }

  // Compare with baseline if requested
  if (shouldCompare) {
    if (!fs.existsSync(BASELINE_FILE)) {
      console.log('\nNo baseline found. Run with --save first.');
      return;
    }

    const baseline = JSON.parse(fs.readFileSync(BASELINE_FILE, 'utf8'));
    console.log('\n' + '='.repeat(70));
    console.log('COMPARISON WITH BASELINE');
    console.log(`Baseline from: ${baseline.timestamp}`);
    console.log('='.repeat(70));

    for (const [cat, benches] of Object.entries(results)) {
      const baseCat = baseline.categories[cat];
      if (!baseCat) {
        console.log(`\n${cat}: NEW (no baseline)`);
        continue;
      }

      console.log(`\n${cat}:`);
      for (const bench of benches) {
        const baseBench = baseCat.find(b => b.desc === bench.desc);
        if (!baseBench) {
          console.log(`  ${bench.desc}: NEW`);
          continue;
        }

        const change = ((bench.mean - baseBench.mean) / baseBench.mean) * 100;
        const sign = change > 0 ? '+' : '';
        let status = '~';
        if (Math.abs(change) >= 10) {
          status = change > 0 ? 'SLOWER' : 'FASTER';
        }

        console.log(`  ${bench.desc.padEnd(15)} ${bench.mean.toFixed(3)}ms vs ${baseBench.mean.toFixed(3)}ms (${sign}${change.toFixed(1)}%) ${status}`);
      }
    }
  }
}

main().catch(e => { console.error(e); process.exit(1); });
