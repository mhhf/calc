/**
 * Proof Search Benchmarks
 *
 * Supports benchmarking with and without content-addressed store
 */

const { BenchmarkRunner } = require('../lib/runner');
const fixtures = require('../lib/fixtures');
const { profiler } = require('../../lib/profiler');
const { Store } = require('../../lib/store');

// Setup
const calc = require('../../ll.json');
const calcParser = require('../../lib/v1/parser.js');
const Sequent = require('../../lib/v1/sequent.js');
const Proofstate = require('../../lib/v1/proofstate.js');
const Ruleset = require('../../lib/ruleset.js');
const PT = require('../../lib/v1/pt.js');
const Calc = require('../../lib/v1/calc.js');

const parser = calcParser(calc).parser;
const { rules, bwd, getRule } = Ruleset.init();

/**
 * Prove a formula
 * @param {string} str - Formula string to prove
 * @param {Store} store - Optional content-addressed store for O(1) equality
 */
function proveFormula(str, store = null) {
  const node = parser.parse(str);
  const seq = Sequent.fromTree(node, store);
  const pt = new PT({ conclusion: seq });
  const atoms = Sequent.getAtoms(seq, { rules: Calc.db.rules });

  return Proofstate.auto(pt, {
    positive: atoms,
    negative: [],
    debug: false,
    mode: 'proof',
    rules,
    bwd,
    getRule,
    calc,
    store,
  });
}

/**
 * Run proof benchmarks without content-addressed store
 */
function runProofBenchmarks(runner, category = 'all') {
  const formulas = category === 'all' ? fixtures.all : fixtures[category];

  if (!formulas) {
    console.error(`Unknown category: ${category}`);
    return;
  }

  for (const [name, formula] of Object.entries(formulas)) {
    runner.run(`proof.${name}`, () => {
      const result = proveFormula(formula);
      if (!result.success) {
        throw new Error(`Failed to prove: ${name}`);
      }
    });
  }
}

/**
 * Run proof benchmarks with content-addressed store
 */
function runProofBenchmarksWithStore(runner, category = 'all') {
  const formulas = category === 'all' ? fixtures.all : fixtures[category];

  if (!formulas) {
    console.error(`Unknown category: ${category}`);
    return;
  }

  for (const [name, formula] of Object.entries(formulas)) {
    runner.run(`proof.store.${name}`, () => {
      // Create fresh store for each proof
      const store = new Store();
      const result = proveFormula(formula, store);
      if (!result.success) {
        throw new Error(`Failed to prove: ${name}`);
      }
    });
  }
}

// Run benchmarks with profiling
function runWithProfiling(runner, category = 'all', useStore = false) {
  const formulas = category === 'all' ? fixtures.all : fixtures[category];

  if (!formulas) {
    console.error(`Unknown category: ${category}`);
    return {};
  }

  profiler.enable();
  const profilingResults = {};

  for (const [name, formula] of Object.entries(formulas)) {
    profiler.reset();

    // Run once with profiling
    const store = useStore ? new Store() : null;
    const result = proveFormula(formula, store);
    if (!result.success) {
      console.error(`Failed to prove: ${name}`);
      continue;
    }

    profilingResults[name] = profiler.stats();
  }

  return profilingResults;
}

module.exports = { runProofBenchmarks, runProofBenchmarksWithStore, runWithProfiling, proveFormula };

// CLI entry point
if (require.main === module) {
  const category = process.argv[2] || 'all';
  const useStore = process.argv.includes('--store');
  const compareMode = process.argv.includes('--compare');

  if (compareMode) {
    // Run both with and without store and compare
    console.log('=== Comparing with and without content-addressed store ===\n');

    const runnerNoStore = new BenchmarkRunner({ iterations: 20, warmup: 5 });
    const runnerWithStore = new BenchmarkRunner({ iterations: 20, warmup: 5 });

    console.log('--- Without Store ---');
    runProofBenchmarks(runnerNoStore, category);
    console.log(runnerNoStore.report());

    console.log('\n--- With Store ---');
    runProofBenchmarksWithStore(runnerWithStore, category);
    console.log(runnerWithStore.report());

    // Compare profiling
    console.log('\n--- Profiling Comparison ---\n');
    const profileNoStore = runWithProfiling(null, category, false);
    const profileWithStore = runWithProfiling(null, category, true);

    const formulas = category === 'all' ? fixtures.all : fixtures[category];
    for (const name of Object.keys(formulas)) {
      const ns = profileNoStore[name];
      const ws = profileWithStore[name];
      if (ns && ws) {
        console.log(`${name}:`);
        console.log(`  mgu calls: ${ns.counters['mgu.call'] || 0} (no store) vs ${ws.counters['mgu.call'] || 0} (with store)`);
        console.log(`  hash comparisons: ${ns.counters['mgu.eq.hash'] || 0} (no store) vs ${ws.counters['mgu.eq.hash'] || 0} (with store)`);
        console.log(`  string comparisons: ${ns.counters['mgu.eq.string'] || 0} (no store) vs ${ws.counters['mgu.eq.string'] || 0} (with store)`);
        console.log('');
      }
    }
  } else {
    const runner = new BenchmarkRunner({ iterations: 20, warmup: 5 });
    const runFn = useStore ? runProofBenchmarksWithStore : runProofBenchmarks;

    console.log(`Running proof benchmarks (category: ${category}${useStore ? ', with store' : ''})...\n`);
    runFn(runner, category);
    console.log(runner.report());

    // Also run with profiling for the first iteration
    console.log('\n--- Profiling Results (single run) ---\n');
    const profilingResults = runWithProfiling(runner, category, useStore);

    for (const [name, stats] of Object.entries(profilingResults)) {
      console.log(`${name}:`);
      console.log(`  mgu calls: ${stats.counters['mgu.call'] || 0}`);
      console.log(`  hash comparisons: ${stats.counters['mgu.eq.hash'] || 0}`);
      console.log(`  string comparisons: ${stats.counters['mgu.eq.string'] || 0}`);
      console.log(`  substitutions: ${stats.counters['substitute.call'] || 0}`);
      console.log(`  sequent copies: ${stats.counters['sequent.copy'] || 0}`);
      console.log('');
    }
  }
}
