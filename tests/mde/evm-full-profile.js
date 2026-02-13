/**
 * Full EVM Profiler - Correct variable syntax
 *
 * Run: CALC_PROFILE=1 node tests/mde/evm-full-profile.js
 */

const mde = require('../../lib/mde');
const forward = require('../../lib/v2/prover/strategy/forward');
const Store = require('../../lib/v2/kernel/store');
const path = require('path');
const prove = require('../../lib/mde/prove');
const { match } = require('../../lib/v2/kernel/unify');
const { apply: subApply } = require('../../lib/v2/kernel/substitute');

function formatMs(ms) {
  if (ms < 0.001) return `${(ms * 1000000).toFixed(0)}ns`;
  if (ms < 1) return `${(ms * 1000).toFixed(1)}µs`;
  return `${ms.toFixed(2)}ms`;
}

async function main() {
  console.log('='.repeat(70));
  console.log('EVM FULL PROFILER');
  console.log('='.repeat(70));
  console.log();

  const calc = await mde.load([
    path.join(__dirname, 'fixtures/bin.mde'),
    path.join(__dirname, 'fixtures/evm.mde')
  ]);

  console.log(`Loaded: ${calc.forwardRules.length} forward rules, ${calc.clauses.size} clauses`);
  console.log();

  // Convert decimal to binary representation
  function decToBin(n) {
    if (n === 0) return 'e';
    const bit = n % 2 === 1 ? 'i' : 'o';
    return `(${bit} ${decToBin(Math.floor(n / 2))})`;
  }

  // Build backward index once
  const backwardIndex = prove.buildIndex(calc.clauses, calc.types);

  const testCases = [
    { name: 'plus 3 2', a: 3, b: 2, expected: 5 },
    { name: 'plus 15 1', a: 15, b: 1, expected: 16 },
    { name: 'plus 255 1', a: 255, b: 1, expected: 256 },
    { name: 'plus 1023 1', a: 1023, b: 1, expected: 1024 },
  ];

  console.log('BACKWARD PROVER BENCHMARK (with correct syntax):');
  console.log('-'.repeat(70));

  for (const tc of testCases) {
    // Use uppercase C for variable!
    const goalStr = `plus ${decToBin(tc.a)} ${decToBin(tc.b)} C`;
    const goal = await mde.parseExpr(goalStr);

    // Warmup
    for (let i = 0; i < 10; i++) {
      prove.prove(goal, calc.clauses, calc.types, { maxDepth: 100, index: backwardIndex });
    }

    // Benchmark
    const iterations = 100;
    let totalTime = 0;
    let storeGets = 0;
    const origGet = Store.get;

    for (let i = 0; i < iterations; i++) {
      Store.get = function(h) {
        storeGets++;
        return origGet.call(Store, h);
      };

      const t0 = performance.now();
      const result = prove.prove(goal, calc.clauses, calc.types, {
        maxDepth: 100,
        index: backwardIndex
      });
      totalTime += performance.now() - t0;

      if (i === 0 && !result.success) {
        console.log(`  ${tc.name}: FAILED`);
        break;
      }
    }
    Store.get = origGet;

    const avgTime = totalTime / iterations;
    const avgGets = storeGets / iterations;
    console.log(`  ${tc.name.padEnd(15)} ${formatMs(avgTime).padStart(10)}, ${avgGets.toFixed(0).padStart(5)} gets`);
  }

  console.log();
  console.log('='.repeat(70));
  console.log('FORWARD EXECUTION BENCHMARK (EVM ADD):');
  console.log('='.repeat(70));
  console.log();

  const testAddCases = [
    { name: 'ADD 3+2=5', a: 3, b: 2 },
    { name: 'ADD 15+1=16', a: 15, b: 1 },
    { name: 'ADD 255+1=256', a: 255, b: 1 },
  ];

  for (const tc of testAddCases) {
    // Build initial state for ADD
    const linearState = {};
    const resources = [
      'pc e',
      'code e (i e)',  // ADD opcode
      'sh (s (s ee))',
      `stack (s ee) ${decToBin(tc.a)}`,
      `stack ee ${decToBin(tc.b)}`,
    ];
    for (const r of resources) {
      const h = await mde.parseExpr(r);
      linearState[h] = 1;
    }

    // Warmup
    for (let i = 0; i < 10; i++) {
      const state = forward.createState({ ...linearState }, {});
      forward.run(state, calc.forwardRules, {
        maxSteps: 1,
        calc: { clauses: calc.clauses, types: calc.types, backwardIndex }
      });
    }

    // Benchmark with profiling
    forward.resetProfile();
    const iterations = 100;
    let totalTime = 0;

    for (let i = 0; i < iterations; i++) {
      const state = forward.createState({ ...linearState }, {});
      const t0 = performance.now();
      forward.run(state, calc.forwardRules, {
        maxSteps: 1,
        calc: { clauses: calc.clauses, types: calc.types, backwardIndex }
      });
      totalTime += performance.now() - t0;
    }

    const prof = forward.getProfile();
    const avgTime = totalTime / iterations;

    console.log(`${tc.name}:`);
    console.log(`  Total:     ${formatMs(avgTime)}`);
    console.log(`  Match:     ${formatMs(prof.matchTime / iterations)} (${prof.matchCalls} calls)`);
    console.log(`  Prove:     ${formatMs(prof.proveTime / iterations)} (${prof.proveCalls} calls) - ${(prof.proveTime / totalTime * 100).toFixed(1)}%`);
    console.log(`  Sub:       ${formatMs(prof.subTime / iterations)} (${prof.subCalls} calls)`);
    const overhead = avgTime - (prof.matchTime + prof.proveTime + prof.subTime) / iterations;
    console.log(`  Overhead:  ${formatMs(overhead)} - ${(overhead / avgTime * 100).toFixed(1)}%`);
    console.log();
  }

  console.log('='.repeat(70));
  console.log('DETAILED BREAKDOWN: plus 255 1');
  console.log('='.repeat(70));
  console.log();

  const goalStr = `plus ${decToBin(255)} ${decToBin(1)} C`;
  const goal = await mde.parseExpr(goalStr);

  // Profile with trace
  const result = prove.prove(goal, calc.clauses, calc.types, {
    maxDepth: 100,
    index: backwardIndex,
    trace: true
  });

  // Count trace elements
  const clauseApps = result.trace.filter(l => l.includes('→')).length;
  const typeApps = result.trace.filter(l => l.includes('✓') && !l.includes('→')).length;
  const goals = result.trace.filter(l => l.includes('Goal:')).length;
  const fails = result.trace.filter(l => l.includes('✗')).length;

  console.log('Trace analysis:');
  console.log(`  Total lines:      ${result.trace.length}`);
  console.log(`  Goals explored:   ${goals}`);
  console.log(`  Clause apps:      ${clauseApps}`);
  console.log(`  Type/axiom apps:  ${typeApps}`);
  console.log(`  Failures:         ${fails}`);
  console.log(`  Theta bindings:   ${result.theta?.length || 0}`);
  console.log();

  // Depth analysis
  const depths = result.trace.map(l => l.match(/^(\s*)/)[1].length / 2);
  const maxDepth = Math.max(...depths);
  console.log(`Max recursion depth: ${maxDepth}`);
  console.log();

  // Full trace (first 30 lines)
  console.log('Trace (first 30 lines):');
  for (let i = 0; i < Math.min(30, result.trace.length); i++) {
    console.log(result.trace[i]);
  }
  if (result.trace.length > 30) {
    console.log(`... (${result.trace.length - 30} more lines)`);
  }
}

main().catch(console.error);
