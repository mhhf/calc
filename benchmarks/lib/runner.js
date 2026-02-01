/**
 * Benchmark Runner
 *
 * Usage: node benchmarks/run.js [--category=<category>] [--iterations=<n>]
 */

const { performance } = require('perf_hooks');
const fs = require('fs');
const path = require('path');

class BenchmarkRunner {
  constructor(opts = {}) {
    this.warmupIterations = opts.warmup ?? 3;
    this.iterations = opts.iterations ?? 10;
    this.results = {};
  }

  // Run a single benchmark
  run(name, fn, opts = {}) {
    const iterations = opts.iterations ?? this.iterations;
    const warmup = opts.warmup ?? this.warmupIterations;

    // Warmup
    for (let i = 0; i < warmup; i++) {
      fn();
    }

    // Force GC if available
    if (global.gc) global.gc();

    // Measure
    const times = [];
    for (let i = 0; i < iterations; i++) {
      const start = performance.now();
      fn();
      const elapsed = performance.now() - start;
      times.push(elapsed);
    }

    // Compute stats
    times.sort((a, b) => a - b);
    const stats = {
      name,
      iterations,
      mean: times.reduce((a, b) => a + b, 0) / times.length,
      min: times[0],
      max: times[times.length - 1],
      p50: times[Math.floor(times.length * 0.5)],
      p95: times[Math.floor(times.length * 0.95)],
      p99: times[Math.floor(times.length * 0.99)],
      raw: times,
    };

    this.results[name] = stats;
    return stats;
  }

  // Run a benchmark with setup/teardown
  runWithSetup(name, setup, fn, teardown, opts = {}) {
    const iterations = opts.iterations ?? this.iterations;
    const warmup = opts.warmup ?? this.warmupIterations;

    // Warmup
    for (let i = 0; i < warmup; i++) {
      const ctx = setup();
      fn(ctx);
      if (teardown) teardown(ctx);
    }

    // Force GC if available
    if (global.gc) global.gc();

    // Measure
    const times = [];
    for (let i = 0; i < iterations; i++) {
      const ctx = setup();
      const start = performance.now();
      fn(ctx);
      const elapsed = performance.now() - start;
      times.push(elapsed);
      if (teardown) teardown(ctx);
    }

    // Compute stats
    times.sort((a, b) => a - b);
    const stats = {
      name,
      iterations,
      mean: times.reduce((a, b) => a + b, 0) / times.length,
      min: times[0],
      max: times[times.length - 1],
      p50: times[Math.floor(times.length * 0.5)],
      p95: times[Math.floor(times.length * 0.95)],
      p99: times[Math.floor(times.length * 0.99)],
      raw: times,
    };

    this.results[name] = stats;
    return stats;
  }

  // Get all results
  getResults() {
    return this.results;
  }

  // Print results
  report() {
    const lines = ['=== Benchmark Results ===', ''];

    const entries = Object.entries(this.results);
    if (entries.length === 0) {
      lines.push('No benchmarks run');
      return lines.join('\n');
    }

    // Find max name length for alignment
    const maxName = Math.max(...entries.map(([name]) => name.length));

    for (const [name, stats] of entries) {
      const pad = ' '.repeat(maxName - name.length);
      lines.push(
        `${name}${pad}  mean: ${stats.mean.toFixed(3)}ms  p50: ${stats.p50.toFixed(3)}ms  p95: ${stats.p95.toFixed(3)}ms  (${stats.iterations} iterations)`
      );
    }

    return lines.join('\n');
  }

  // Save results to JSON
  save(filename) {
    const output = {
      timestamp: new Date().toISOString(),
      results: {},
    };

    for (const [name, stats] of Object.entries(this.results)) {
      output.results[name] = {
        mean: stats.mean,
        min: stats.min,
        max: stats.max,
        p50: stats.p50,
        p95: stats.p95,
        p99: stats.p99,
        iterations: stats.iterations,
      };
    }

    fs.writeFileSync(filename, JSON.stringify(output, null, 2));
    return output;
  }

  // Compare with baseline
  compare(baseline) {
    const lines = ['=== Comparison with Baseline ===', ''];

    for (const [name, current] of Object.entries(this.results)) {
      const base = baseline.results?.[name];
      if (!base) {
        lines.push(`${name}: NEW (no baseline)`);
        continue;
      }

      const change = ((current.mean - base.mean) / base.mean) * 100;
      const sign = change > 0 ? '+' : '';
      const status = Math.abs(change) < 5 ? '~' : change > 0 ? 'SLOWER' : 'FASTER';

      lines.push(
        `${name}: ${current.mean.toFixed(3)}ms vs ${base.mean.toFixed(3)}ms (${sign}${change.toFixed(1)}%) ${status}`
      );
    }

    return lines.join('\n');
  }
}

module.exports = { BenchmarkRunner };
