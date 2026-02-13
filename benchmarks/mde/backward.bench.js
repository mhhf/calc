/**
 * MDE Backward Chaining Benchmarks
 *
 * Tests arithmetic proofs of varying complexity using optimism-mde's bin.mde
 * These are the most demanding proofs and represent real EVM verification workloads.
 *
 * Run: npm run bench:mde
 * Profile: npm run profile:mde
 */

const mde = require('../../lib/engine');
const prove = require('../../lib/engine/prove');
const Store = require('../../lib/kernel/store');
const { performance } = require('perf_hooks');
const path = require('path');

// Binary representation helpers
function decToBin(n) {
  function inner(n) {
    if (n === 0) return 'e';
    if (n % 2 === 1) return `i (${inner((n - 1) / 2)})`;
    return `o (${inner(n / 2)})`;
  }
  return `(${inner(n)})`;
}

function hashToDec(hash) {
  const node = Store.get(hash);
  if (!node) return null;
  if (node.tag === 'atom' && node.children[0] === 'e') return 0;
  if (node.tag === 'app' && node.children.length === 2) {
    const [func, arg] = node.children;
    const funcNode = Store.get(func);
    if (funcNode && funcNode.tag === 'atom') {
      const name = funcNode.children[0];
      const inner = hashToDec(arg);
      if (inner !== null) {
        if (name === 'i') return 2 * inner + 1;
        if (name === 'o') return 2 * inner;
      }
    }
  }
  return null;
}

// Extract solution from substitution
function extractSolution(theta, varName = '_X') {
  for (const [varHash, valHash] of theta) {
    const varNode = Store.get(varHash);
    if (varNode && varNode.tag === 'freevar' && varNode.children[0] === varName) {
      let resolved = valHash;
      for (let i = 0; i < 50; i++) {
        const prev = resolved;
        resolved = require('../../lib/kernel/substitute').apply(resolved, theta);
        if (resolved === prev) break;
      }
      return hashToDec(resolved);
    }
  }
  return null;
}

// Benchmark suite definition
const BENCHMARKS = {
  // Easy: Simple operations, depth 1-2
  easy: [
    { query: 'inc e X', expected: 1, desc: 'inc 0' },
    { query: 'plus e e X', expected: 0, desc: '0 + 0' },
    { query: 'plus (i e) e X', expected: 1, desc: '1 + 0' },
    { query: 'plus e (i e) X', expected: 1, desc: '0 + 1' },
  ],

  // Medium: Multi-step recursion, depth 3-5
  medium: [
    { query: 'plus (i e) (i e) X', expected: 2, desc: '1 + 1' },
    { query: 'plus (i (i e)) (o (i e)) X', expected: 5, desc: '3 + 2' },
    { query: 'mul (o (i e)) (i (i e)) X', expected: 6, desc: '2 * 3' },
    { query: 'mul (i (i e)) (o (i e)) X', expected: 6, desc: '3 * 2' },
  ],

  // Complex: Deep recursion, depth 10-20
  complex: [
    { query: `plus ${decToBin(15)} ${decToBin(17)} X`, expected: 32, desc: '15 + 17' },
    { query: `plus ${decToBin(63)} ${decToBin(64)} X`, expected: 127, desc: '63 + 64' },
    { query: `mul ${decToBin(7)} ${decToBin(7)} X`, expected: 49, desc: '7 * 7' },
    { query: `mul ${decToBin(12)} ${decToBin(11)} X`, expected: 132, desc: '12 * 11' },
  ],

  // Stress: Very deep recursion for bottleneck analysis
  stress: [
    { query: `plus ${decToBin(127)} ${decToBin(128)} X`, expected: 255, desc: '127 + 128' },
    { query: `plus ${decToBin(255)} ${decToBin(1)} X`, expected: 256, desc: '255 + 1' },
    { query: `mul ${decToBin(15)} ${decToBin(15)} X`, expected: 225, desc: '15 * 15' },
    { query: `mul ${decToBin(16)} ${decToBin(16)} X`, expected: 256, desc: '16 * 16' },
  ],
};

// Run benchmarks
async function runBenchmarks(opts = {}) {
  const {
    categories = Object.keys(BENCHMARKS),
    iterations = 20,
    warmup = 5,
    profile = false,
  } = opts;

  // Load calculus
  const calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/bin.ill'));
  const idx = prove.buildIndex(calc.clauses, calc.types);

  console.log('='.repeat(70));
  console.log('MDE BACKWARD CHAINING BENCHMARK');
  console.log('='.repeat(70));
  console.log(`Clauses: ${calc.clauses.size}, Types: ${calc.types.size}`);
  console.log(`Iterations: ${iterations}, Warmup: ${warmup}`);
  console.log(`Categories: ${categories.join(', ')}\n`);

  const results = {};

  for (const cat of categories) {
    if (!BENCHMARKS[cat]) continue;

    console.log(`\n${'─'.repeat(70)}`);
    console.log(`${cat.toUpperCase()}`);
    console.log('─'.repeat(70));

    results[cat] = [];

    for (const bench of BENCHMARKS[cat]) {
      const goal = await mde.parseExpr(bench.query);

      // Warmup
      for (let i = 0; i < warmup; i++) {
        prove.prove(goal, calc.clauses, calc.types, { maxDepth: 200, index: idx });
      }

      // Force GC if available
      if (global.gc) global.gc();

      // Benchmark
      const times = [];
      let lastResult = null;

      for (let i = 0; i < iterations; i++) {
        const start = performance.now();
        lastResult = prove.prove(goal, calc.clauses, calc.types, { maxDepth: 200, index: idx });
        times.push(performance.now() - start);
      }

      // Compute stats
      times.sort((a, b) => a - b);
      const stats = {
        mean: times.reduce((a, b) => a + b, 0) / times.length,
        min: times[0],
        max: times[times.length - 1],
        p50: times[Math.floor(times.length * 0.5)],
        p95: times[Math.floor(times.length * 0.95)],
      };

      // Verify result
      const solution = lastResult.success ? extractSolution(lastResult.theta) : null;
      const correct = solution === bench.expected;

      // Report
      const status = correct ? '✓' : '✗';
      console.log(`${status} ${bench.desc.padEnd(15)} ${stats.mean.toFixed(3).padStart(8)}ms (p50: ${stats.p50.toFixed(3)}ms, p95: ${stats.p95.toFixed(3)}ms)`);

      if (!correct) {
        console.log(`  EXPECTED: ${bench.expected}, GOT: ${solution}`);
      }

      results[cat].push({
        ...bench,
        ...stats,
        correct,
        solution,
      });
    }
  }

  // Summary
  console.log('\n' + '='.repeat(70));
  console.log('SUMMARY');
  console.log('='.repeat(70));

  for (const [cat, benches] of Object.entries(results)) {
    const total = benches.reduce((s, b) => s + b.mean, 0);
    const allCorrect = benches.every(b => b.correct);
    const status = allCorrect ? '✓' : '✗';
    console.log(`${status} ${cat.padEnd(10)} total: ${total.toFixed(3)}ms, avg: ${(total / benches.length).toFixed(3)}ms`);
  }

  return results;
}

// Profile single benchmark
async function profileBenchmark(query, desc, opts = {}) {
  const { iterations = 10 } = opts;

  const calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/bin.ill'));
  const idx = prove.buildIndex(calc.clauses, calc.types);
  const goal = await mde.parseExpr(query);

  console.log('='.repeat(70));
  console.log(`PROFILING: ${desc}`);
  console.log(`Query: ${query}`);
  console.log('='.repeat(70));

  // Detailed metrics collection
  const metrics = {
    searchCalls: 0,
    maxDepth: 0,
    unifyAttempts: 0,
    unifySuccesses: 0,
    candidatesTotal: 0,
  };

  // Run with trace to count operations
  const traceResult = prove.prove(goal, calc.clauses, calc.types, {
    maxDepth: 200,
    index: idx,
    trace: true,
  });

  if (traceResult.trace) {
    for (const line of traceResult.trace) {
      if (line.includes('Goal:')) {
        metrics.searchCalls++;
        const depthMatch = line.match(/^(\s*)/);
        const depth = depthMatch ? depthMatch[1].length / 2 : 0;
        metrics.maxDepth = Math.max(metrics.maxDepth, depth);

        // Extract candidate counts from trace
        const candMatch = line.match(/\[(\d+)t\/(\d+)c\]/);
        if (candMatch) {
          metrics.candidatesTotal += parseInt(candMatch[1]) + parseInt(candMatch[2]);
        }
      }
    }
  }

  // Timing breakdown
  const times = [];
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    prove.prove(goal, calc.clauses, calc.types, { maxDepth: 200, index: idx });
    times.push(performance.now() - start);
  }

  times.sort((a, b) => a - b);
  const mean = times.reduce((a, b) => a + b, 0) / times.length;

  console.log(`\nResult: ${traceResult.success ? 'SUCCESS' : 'FAILED'}`);
  if (traceResult.success) {
    const solution = extractSolution(traceResult.theta);
    console.log(`Solution: X = ${solution}`);
  }

  console.log(`\nMetrics:`);
  console.log(`  Search calls:    ${metrics.searchCalls}`);
  console.log(`  Max depth:       ${metrics.maxDepth}`);
  console.log(`  Candidates/call: ${(metrics.candidatesTotal / metrics.searchCalls).toFixed(1)}`);

  console.log(`\nTiming (${iterations} iterations):`);
  console.log(`  Mean:  ${mean.toFixed(3)} ms`);
  console.log(`  Min:   ${times[0].toFixed(3)} ms`);
  console.log(`  Max:   ${times[times.length - 1].toFixed(3)} ms`);
  console.log(`  p50:   ${times[Math.floor(times.length * 0.5)].toFixed(3)} ms`);
  console.log(`  p95:   ${times[Math.floor(times.length * 0.95)].toFixed(3)} ms`);

  // Estimate time per operation
  console.log(`\nEstimated cost per operation:`);
  console.log(`  Per search call: ${(mean / metrics.searchCalls * 1000).toFixed(1)} μs`);

  return { metrics, times, mean };
}

module.exports = { runBenchmarks, profileBenchmark, BENCHMARKS };

// CLI entry point
if (require.main === module) {
  const args = process.argv.slice(2);
  const categories = args.filter(a => !a.startsWith('--'));
  const profile = args.includes('--profile');
  const stress = args.includes('--stress');

  const opts = {
    categories: categories.length > 0 ? categories : (stress ? ['stress'] : ['easy', 'medium', 'complex']),
    iterations: stress ? 10 : 20,
    warmup: stress ? 3 : 5,
    profile,
  };

  runBenchmarks(opts)
    .then(() => process.exit(0))
    .catch(e => { console.error(e); process.exit(1); });
}
