/**
 * Deep Benchmarking and Profiling for MDE Backward Chaining
 *
 * Tests easy, medium, and complex queries to understand performance
 * characteristics and identify optimization opportunities.
 *
 * Run: node tests/mde/backward-benchmark.js
 */

const mde = require('../../lib/mde');
const Store = require('../../lib/v2/kernel/store');
const { unify, match } = require('../../lib/v2/kernel/unify');
const { apply: subApply } = require('../../lib/v2/kernel/substitute');
const prove = require('../../lib/mde/prove');
const path = require('path');

// Binary representation helpers
// Returns binary with outer parens, e.g. decToBin(3) = "(i (i e))"
function decToBin(n) {
  function inner(n) {
    if (n === 0) return 'e';
    if (n % 2 === 1) return `i (${inner((n - 1) / 2)})`;
    return `o (${inner(n / 2)})`;
  }
  // Wrap in outer parens for proper parsing as argument
  return `(${inner(n)})`;
}

function binToDec(s) {
  s = s.trim();
  if (s === 'e') return 0;
  if (s.startsWith('(') && s.endsWith(')')) s = s.slice(1, -1).trim();
  const m = s.match(/^([io])\s*\((.+)\)$/);
  if (m) {
    const [, bit, inner] = m;
    const v = binToDec(inner);
    return bit === 'i' ? 2 * v + 1 : 2 * v;
  }
  if (s.startsWith('i ')) return 2 * binToDec(s.slice(2)) + 1;
  if (s.startsWith('o ')) return 2 * binToDec(s.slice(2));
  return NaN;
}

// Convert hash to decimal (directly from Store)
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

// Fully apply substitution (handles transitive bindings)
function fullyApply(hash, theta) {
  let h = hash;
  for (let i = 0; i < 50; i++) {
    const prev = h;
    h = subApply(h, theta);
    if (h === prev) break;
  }
  return h;
}

// Instrumented prove function that collects detailed metrics
function instrumentedProve(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const metrics = {
    totalCalls: 0,
    maxRecursionDepth: 0,
    clausesTriedTotal: 0,
    unifyAttempts: 0,
    unifySuccesses: 0,
    freshenCalls: 0,
    subApplyCalls: 0,
    timeBreakdown: {
      unify: 0,
      freshen: 0,
      subApply: 0,
      clauseIteration: 0,
    }
  };

  // Wrap unify to count
  const originalUnify = unify;
  let unifyTime = 0;

  function search(g, theta, depth) {
    metrics.totalCalls++;
    metrics.maxRecursionDepth = Math.max(metrics.maxRecursionDepth, depth);

    if (depth > maxDepth) return null;

    // Apply current substitution
    const subStart = performance.now();
    const goalInst = subApply(g, theta);
    metrics.subApplyCalls++;
    metrics.timeBreakdown.subApply += performance.now() - subStart;

    // Try types (axioms)
    const iterStart = performance.now();
    for (const [name, typeHash] of types) {
      // Freshen
      const freshStart = performance.now();
      const freshType = freshenTerm(typeHash, depth, 'a');
      metrics.freshenCalls++;
      metrics.timeBreakdown.freshen += performance.now() - freshStart;

      // Unify
      const unifyStart = performance.now();
      metrics.unifyAttempts++;
      const newTheta = unify(freshType, goalInst);
      metrics.timeBreakdown.unify += performance.now() - unifyStart;

      if (newTheta !== null) {
        metrics.unifySuccesses++;
        return [...theta, ...newTheta];
      }
    }
    metrics.timeBreakdown.clauseIteration += performance.now() - iterStart;

    // Try clauses
    const clauseIterStart = performance.now();
    for (const [name, clause] of clauses) {
      metrics.clausesTriedTotal++;

      // Freshen clause
      const freshStart = performance.now();
      const { head, premises } = freshenClause(clause, depth);
      metrics.freshenCalls++;
      metrics.timeBreakdown.freshen += performance.now() - freshStart;

      // Unify head with goal
      const unifyStart = performance.now();
      metrics.unifyAttempts++;
      const newTheta = unify(head, goalInst);
      metrics.timeBreakdown.unify += performance.now() - unifyStart;

      if (newTheta === null) continue;
      metrics.unifySuccesses++;

      // Merge theta
      let currentTheta = [...theta, ...newTheta];
      let allPremisesProved = true;

      // Prove premises
      for (const premise of premises) {
        const premStart = performance.now();
        const premiseInst = subApply(premise, currentTheta);
        metrics.subApplyCalls++;
        metrics.timeBreakdown.subApply += performance.now() - premStart;

        const result = search(premiseInst, currentTheta, depth + 1);
        if (result === null) {
          allPremisesProved = false;
          break;
        }
        currentTheta = result;
      }

      if (allPremisesProved) {
        metrics.timeBreakdown.clauseIteration += performance.now() - clauseIterStart;
        return currentTheta;
      }
    }
    metrics.timeBreakdown.clauseIteration += performance.now() - clauseIterStart;

    return null;
  }

  // Freshen functions (copied from prove.js for instrumentation)
  function freshenTerm(h, depth, prefix = '') {
    const suffix = `_${prefix}d${depth}`;
    const renamed = new Map();

    function freshen(hash) {
      const node = Store.get(hash);
      if (!node) return hash;

      if (node.tag === 'freevar') {
        const name = node.children[0];
        if (typeof name === 'string' && name.startsWith('_')) {
          if (!renamed.has(hash)) {
            renamed.set(hash, Store.intern('freevar', [name + suffix]));
          }
          return renamed.get(hash);
        }
        return hash;
      }

      let changed = false;
      const newChildren = node.children.map(c => {
        if (typeof c === 'number') {
          const newC = freshen(c);
          if (newC !== c) changed = true;
          return newC;
        }
        return c;
      });

      if (!changed) return hash;
      return Store.intern(node.tag, newChildren);
    }

    return freshen(h);
  }

  function freshenClause(clause, depth) {
    const suffix = `_d${depth}`;
    const renamed = new Map();

    function freshen(h) {
      const node = Store.get(h);
      if (!node) return h;

      if (node.tag === 'freevar') {
        const name = node.children[0];
        if (typeof name === 'string' && name.startsWith('_')) {
          if (!renamed.has(h)) {
            renamed.set(h, Store.intern('freevar', [name + suffix]));
          }
          return renamed.get(h);
        }
        return h;
      }

      let changed = false;
      const newChildren = node.children.map(c => {
        if (typeof c === 'number') {
          const newC = freshen(c);
          if (newC !== c) changed = true;
          return newC;
        }
        return c;
      });

      if (!changed) return h;
      return Store.intern(node.tag, newChildren);
    }

    return {
      head: freshen(clause.hash),
      premises: clause.premises.map(p => freshen(p))
    };
  }

  const totalStart = performance.now();
  const result = search(goal, [], 0);
  const totalTime = performance.now() - totalStart;

  return {
    success: result !== null,
    theta: result,
    metrics,
    totalTime
  };
}

// Run benchmarks
(async () => {
  console.log('='.repeat(70));
  console.log('MDE BACKWARD CHAINING - DEEP BENCHMARK AND PROFILING');
  console.log('='.repeat(70));
  console.log();

  // Load calculus
  const calc = await mde.load([
    path.join(__dirname, 'fixtures/bin.mde'),
    path.join(__dirname, 'fixtures/evm.mde')
  ]);

  console.log(`Loaded: ${calc.clauses.size} clauses, ${calc.types.size} types\n`);

  // Test cases - uppercase = free variable (X parses to freevar)
  const testCases = {
    easy: [
      { query: 'inc e X', desc: '0 + 1 = 1' },
      { query: 'plus e e X', desc: '0 + 0 = 0' },
      { query: 'plus (i e) e X', desc: '1 + 0 = 1' },
      { query: 'plus e (i e) X', desc: '0 + 1 = 1' },
    ],
    medium: [
      { query: 'plus (i e) (i e) X', desc: '1 + 1 = 2' },
      { query: 'plus (i (i e)) (o (i e)) X', desc: '3 + 2 = 5' },
      { query: 'plus (o (o (i e))) (o (o (i e))) X', desc: '4 + 4 = 8' },
      { query: 'mul (o (i e)) (i (i e)) X', desc: '2 * 3 = 6' },
    ],
    complex: [
      { query: `plus ${decToBin(15)} ${decToBin(17)} X`, desc: '15 + 17 = 32' },
      { query: `plus ${decToBin(127)} ${decToBin(1)} X`, desc: '127 + 1 = 128' },
      { query: `plus ${decToBin(63)} ${decToBin(64)} X`, desc: '63 + 64 = 127' },
      { query: `mul ${decToBin(7)} ${decToBin(7)} X`, desc: '7 * 7 = 49' },
    ]
  };

  const iterations = 20;
  const results = {};

  for (const [difficulty, cases] of Object.entries(testCases)) {
    console.log(`\n${'─'.repeat(70)}`);
    console.log(`${difficulty.toUpperCase()} QUERIES`);
    console.log('─'.repeat(70));

    results[difficulty] = [];

    for (const { query, desc } of cases) {
      const goal = await mde.parseExpr(query);

      // Warm up
      for (let i = 0; i < 3; i++) {
        prove.prove(goal, calc.clauses, calc.types, { maxDepth: 100 });
      }

      // Benchmark standard prove
      let stdTotal = 0;
      for (let i = 0; i < iterations; i++) {
        const start = performance.now();
        prove.prove(goal, calc.clauses, calc.types, { maxDepth: 100 });
        stdTotal += performance.now() - start;
      }
      const stdTime = stdTotal / iterations;

      // Get detailed metrics with instrumented version (once)
      const detailed = instrumentedProve(goal, calc.clauses, calc.types, { maxDepth: 100 });

      // Extract solution from theta (find X binding and fully resolve)
      let solution = '?';
      if (detailed.success) {
        for (const [varHash, valHash] of detailed.theta) {
          const varNode = Store.get(varHash);
          if (varNode && varNode.tag === 'freevar' && varNode.children[0] === '_X') {
            const resolved = fullyApply(valHash, detailed.theta);
            const dec = hashToDec(resolved);
            solution = dec !== null ? dec : '?';
            break;
          }
        }
      }

      const m = detailed.metrics;
      const tb = m.timeBreakdown;

      console.log(`\n${desc.padEnd(20)} (${query.slice(0, 35)}...)`);
      console.log(`  Result: X = ${solution}`);
      console.log(`  Time: ${stdTime.toFixed(3)} ms (avg over ${iterations})`);
      console.log(`  Recursion depth: ${m.maxRecursionDepth}`);
      console.log(`  Total search calls: ${m.totalCalls}`);
      console.log(`  Clauses tried: ${m.clausesTriedTotal}`);
      console.log(`  Unify attempts: ${m.unifyAttempts} (${m.unifySuccesses} success, ${(100 * m.unifySuccesses / m.unifyAttempts).toFixed(1)}%)`);
      console.log(`  Freshen calls: ${m.freshenCalls}`);
      console.log(`  SubApply calls: ${m.subApplyCalls}`);
      console.log(`  Time breakdown:`);
      console.log(`    Unify:      ${tb.unify.toFixed(3)} ms (${(100 * tb.unify / detailed.totalTime).toFixed(1)}%)`);
      console.log(`    Freshen:    ${tb.freshen.toFixed(3)} ms (${(100 * tb.freshen / detailed.totalTime).toFixed(1)}%)`);
      console.log(`    SubApply:   ${tb.subApply.toFixed(3)} ms (${(100 * tb.subApply / detailed.totalTime).toFixed(1)}%)`);
      console.log(`    Iteration:  ${tb.clauseIteration.toFixed(3)} ms (${(100 * tb.clauseIteration / detailed.totalTime).toFixed(1)}%)`);

      results[difficulty].push({
        desc, query, stdTime, solution,
        metrics: m,
        timeBreakdown: tb,
        totalTime: detailed.totalTime
      });
    }
  }

  // Summary analysis
  console.log('\n' + '='.repeat(70));
  console.log('ANALYSIS SUMMARY');
  console.log('='.repeat(70));

  // Aggregate by difficulty
  for (const [difficulty, cases] of Object.entries(results)) {
    const avgTime = cases.reduce((s, c) => s + c.stdTime, 0) / cases.length;
    const avgClauses = cases.reduce((s, c) => s + c.metrics.clausesTriedTotal, 0) / cases.length;
    const avgUnify = cases.reduce((s, c) => s + c.metrics.unifyAttempts, 0) / cases.length;
    const avgDepth = cases.reduce((s, c) => s + c.metrics.maxRecursionDepth, 0) / cases.length;

    console.log(`\n${difficulty.toUpperCase()}:`);
    console.log(`  Avg time:       ${avgTime.toFixed(3)} ms`);
    console.log(`  Avg depth:      ${avgDepth.toFixed(1)}`);
    console.log(`  Avg clauses:    ${avgClauses.toFixed(0)}`);
    console.log(`  Avg unify:      ${avgUnify.toFixed(0)}`);
  }

  // Find bottlenecks
  console.log('\n' + '─'.repeat(70));
  console.log('BOTTLENECK ANALYSIS');
  console.log('─'.repeat(70));

  // Aggregate time breakdown across all complex cases
  const complexCases = results.complex;
  const totalBreakdown = { unify: 0, freshen: 0, subApply: 0, iteration: 0 };
  let totalMeasuredTime = 0;

  for (const c of complexCases) {
    totalBreakdown.unify += c.timeBreakdown.unify;
    totalBreakdown.freshen += c.timeBreakdown.freshen;
    totalBreakdown.subApply += c.timeBreakdown.subApply;
    totalBreakdown.iteration += c.timeBreakdown.clauseIteration;
    totalMeasuredTime += c.totalTime;
  }

  const breakdown = [
    ['Unification', totalBreakdown.unify, totalBreakdown.unify / totalMeasuredTime * 100],
    ['Freshening', totalBreakdown.freshen, totalBreakdown.freshen / totalMeasuredTime * 100],
    ['Substitution', totalBreakdown.subApply, totalBreakdown.subApply / totalMeasuredTime * 100],
    ['Clause Iteration', totalBreakdown.iteration, totalBreakdown.iteration / totalMeasuredTime * 100],
  ].sort((a, b) => b[2] - a[2]);

  console.log('\nComplex queries time breakdown (sorted by impact):');
  for (const [name, time, pct] of breakdown) {
    const bar = '█'.repeat(Math.round(pct / 2));
    console.log(`  ${name.padEnd(18)} ${time.toFixed(3).padStart(8)} ms  ${pct.toFixed(1).padStart(5)}%  ${bar}`);
  }

  // Efficiency metrics
  console.log('\n' + '─'.repeat(70));
  console.log('EFFICIENCY METRICS');
  console.log('─'.repeat(70));

  const worstCase = complexCases.reduce((w, c) => c.stdTime > w.stdTime ? c : w);
  const bestCase = complexCases.reduce((b, c) => c.stdTime < b.stdTime ? c : b);

  console.log(`\nWorst case: ${worstCase.desc} (${worstCase.stdTime.toFixed(3)} ms)`);
  console.log(`  Clauses tried: ${worstCase.metrics.clausesTriedTotal}`);
  console.log(`  Unify success rate: ${(100 * worstCase.metrics.unifySuccesses / worstCase.metrics.unifyAttempts).toFixed(1)}%`);

  console.log(`\nBest case: ${bestCase.desc} (${bestCase.stdTime.toFixed(3)} ms)`);
  console.log(`  Clauses tried: ${bestCase.metrics.clausesTriedTotal}`);
  console.log(`  Unify success rate: ${(100 * bestCase.metrics.unifySuccesses / bestCase.metrics.unifyAttempts).toFixed(1)}%`);

  // Unify efficiency
  const totalUnifyAttempts = complexCases.reduce((s, c) => s + c.metrics.unifyAttempts, 0);
  const totalUnifySuccesses = complexCases.reduce((s, c) => s + c.metrics.unifySuccesses, 0);
  const unifySuccessRate = 100 * totalUnifySuccesses / totalUnifyAttempts;

  console.log(`\nOverall unify success rate: ${unifySuccessRate.toFixed(1)}%`);
  console.log(`  (${totalUnifySuccesses} successes / ${totalUnifyAttempts} attempts)`);
  console.log(`  Wasted unify attempts: ${totalUnifyAttempts - totalUnifySuccesses} (${(100 - unifySuccessRate).toFixed(1)}%)`);

  // Optimization recommendations
  console.log('\n' + '='.repeat(70));
  console.log('OPTIMIZATION RECOMMENDATIONS');
  console.log('='.repeat(70));

  const topBottleneck = breakdown[0];
  console.log(`\n1. PRIMARY BOTTLENECK: ${topBottleneck[0]} (${topBottleneck[2].toFixed(1)}% of time)`);

  if (topBottleneck[0] === 'Unification') {
    console.log('   → Implement first-argument indexing to reduce failed unifications');
    console.log('   → Consider near-linear unification algorithm');
  } else if (topBottleneck[0] === 'Freshening') {
    console.log('   → Cache freshened clauses per depth level');
    console.log('   → Use explicit substitutions to delay freshening');
  } else if (topBottleneck[0] === 'Clause Iteration') {
    console.log('   → Implement clause indexing by head functor');
    console.log('   → Currently iterating all ' + calc.clauses.size + ' clauses');
  } else if (topBottleneck[0] === 'Substitution') {
    console.log('   → Use lazy/explicit substitutions');
    console.log('   → Avoid redundant subApply calls');
  }

  console.log(`\n2. LOW UNIFY SUCCESS RATE: ${unifySuccessRate.toFixed(1)}%`);
  console.log('   → First-argument indexing could eliminate ~' +
    Math.round((100 - unifySuccessRate) * totalUnifyAttempts / 100) + ' failed attempts');

  console.log('\n3. MEMOIZATION OPPORTUNITY');
  console.log('   → Repeated subgoals in recursion');
  console.log('   → Content-addressed goals make caching trivial');

  console.log('\n');
})().catch(e => console.error(e));
