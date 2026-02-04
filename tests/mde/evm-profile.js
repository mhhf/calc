/**
 * Profile the EVM ADD demo
 *
 * Run: node tests/mde/evm-profile.js
 */

const mde = require('../../lib/mde');
const forward = require('../../lib/v2/prover/forward');
const Store = require('../../lib/v2/kernel/store');
const { match } = require('../../lib/v2/kernel/unify');
const { apply: subApply } = require('../../lib/v2/kernel/substitute');
const prove = require('../../lib/mde/prove');
const path = require('path');

(async () => {
  console.log("=== EVM ADD Profiling ===\n");

  // Load
  const loadStart = performance.now();
  const calc = await mde.load([
    path.join(__dirname, "fixtures/bin.mde"),
    path.join(__dirname, "fixtures/evm.mde")
  ]);
  const loadTime = performance.now() - loadStart;

  // Parse state
  const resources = [
    'pc e', 'code e (i e)', 'sh (s (s ee))',
    'stack (s ee) (i (i e))', 'stack ee (o (i e))',
  ];
  const linearState = {};
  for (const r of resources) {
    const h = await mde.parseExpr(r);
    linearState[h] = (linearState[h] || 0) + 1;
  }

  const addRule = calc.forwardRules.find(r => r.name === 'evm/add');

  // Warm up
  for (let i = 0; i < 10; i++) {
    const state = forward.createState({ ...linearState }, {});
    forward.run(state, calc.forwardRules, {
      maxSteps: 1,
      calc: { clauses: calc.clauses, types: calc.types }
    });
  }

  const iterations = 100;

  // Full forward.run timing
  let fullTotal = 0;
  for (let i = 0; i < iterations; i++) {
    const state = forward.createState({ ...linearState }, {});
    const start = performance.now();
    forward.run(state, calc.forwardRules, {
      maxSteps: 1,
      calc: { clauses: calc.clauses, types: calc.types }
    });
    fullTotal += performance.now() - start;
  }
  const fullTime = fullTotal / iterations;

  // Component timings
  // Linear matching
  let linearTotal = 0;
  for (let i = 0; i < iterations; i++) {
    let theta = [];
    const consumed = {};
    const start = performance.now();
    for (const pattern of addRule.antecedent.linear) {
      for (const h of Object.keys(linearState)) {
        const hash = Number(h);
        const available = (linearState[hash] || 0) - (consumed[hash] || 0);
        if (available <= 0) continue;
        const newTheta = match(pattern, hash, [...theta]);
        if (newTheta !== null) {
          consumed[hash] = (consumed[hash] || 0) + 1;
          theta = newTheta;
          break;
        }
      }
    }
    linearTotal += performance.now() - start;
  }
  const linearTime = linearTotal / iterations;

  // Get actual goals after linear matching
  let theta = [];
  const consumed = {};
  for (const pattern of addRule.antecedent.linear) {
    for (const h of Object.keys(linearState)) {
      const hash = Number(h);
      const available = (linearState[hash] || 0) - (consumed[hash] || 0);
      if (available <= 0) continue;
      const newTheta = match(pattern, hash, [...theta]);
      if (newTheta !== null) {
        consumed[hash] = (consumed[hash] || 0) + 1;
        theta = newTheta;
        break;
      }
    }
  }

  // Backward proving (with actual goals)
  const incGoal = subApply(addRule.antecedent.persistent[0], theta);
  const plusGoal = subApply(addRule.antecedent.persistent[1], theta);

  let incTotal = 0;
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    prove.prove(incGoal, calc.clauses, calc.types, { maxDepth: 50 });
    incTotal += performance.now() - start;
  }
  const incTime = incTotal / iterations;

  let plusTotal = 0;
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    prove.prove(plusGoal, calc.clauses, calc.types, { maxDepth: 50 });
    plusTotal += performance.now() - start;
  }
  const plusTime = plusTotal / iterations;

  // Print results
  console.log("TIMING BREAKDOWN:");
  console.log("=".repeat(55));
  console.log(`  Load files:              ${loadTime.toFixed(1)} ms (one-time)`);
  console.log();
  console.log(`  Full forward.run:        ${fullTime.toFixed(3)} ms`);
  console.log();
  console.log("  Components:");
  console.log(`    Linear matching:       ${linearTime.toFixed(4)} ms (${(100*linearTime/fullTime).toFixed(1)}%)`);
  console.log(`    Backward: inc 0 X:     ${incTime.toFixed(4)} ms (${(100*incTime/fullTime).toFixed(1)}%)`);
  console.log(`    Backward: plus 3 2 X:  ${plusTime.toFixed(4)} ms (${(100*plusTime/fullTime).toFixed(1)}%)`);
  const overhead = fullTime - linearTime - incTime - plusTime;
  console.log(`    Other overhead:        ${overhead.toFixed(4)} ms (${(100*overhead/fullTime).toFixed(1)}%)`);
  console.log();
  console.log(`  Throughput:              ${Math.floor(1000/fullTime)} ADD ops/sec`);
  console.log();

  // Memoization test
  console.log("MEMOIZATION TEST:");
  console.log("=".repeat(55));

  const cache = new Map();
  function memoizedProve(goal, clauses, types, opts) {
    if (cache.has(goal)) return cache.get(goal);
    const result = prove.prove(goal, clauses, types, opts);
    cache.set(goal, result);
    return result;
  }

  let memoTotal = 0;
  cache.clear();
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    memoizedProve(plusGoal, calc.clauses, calc.types, { maxDepth: 50 });
    memoTotal += performance.now() - start;
  }
  const memoTime = memoTotal / iterations;

  console.log(`  Without memoization:     ${plusTime.toFixed(4)} ms`);
  console.log(`  With memoization:        ${memoTime.toFixed(4)} ms`);
  console.log(`  Speedup:                 ${(plusTime/memoTime).toFixed(0)}x`);
  console.log();

  const memoFullTime = linearTime + incTime + memoTime + overhead;
  console.log(`  Estimated with memo:     ${memoFullTime.toFixed(4)} ms`);
  console.log(`  Estimated throughput:    ${Math.floor(1000/memoFullTime)} ADD ops/sec`);

})().catch(e => console.error(e));
