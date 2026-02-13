/**
 * Multisig EVM Execution Profiler
 *
 * Uses Node.js built-in profiling to measure where time is spent.
 */

const mde = require('../../lib/mde');
const Store = require('../../lib/v2/kernel/store');
const fs = require('fs');
const path = require('path');
const { performance, PerformanceObserver } = require('perf_hooks');

function formatMs(ms) {
  if (ms < 0.001) return `${(ms * 1000000).toFixed(0)}ns`;
  if (ms < 1) return `${(ms * 1000).toFixed(1)}µs`;
  return `${ms.toFixed(2)}ms`;
}

async function main() {
  console.log('='.repeat(70));
  console.log('MULTISIG EVM EXECUTION PROFILER');
  console.log('='.repeat(70));
  console.log();

  // Phase timings
  const phases = {};

  // Load
  let t0 = performance.now();
  const calc = await mde.load([
    path.join(__dirname, 'fixtures/bin.mde'),
    path.join(__dirname, 'fixtures/evm.mde'),
    path.join(__dirname, 'fixtures/multisig_code.mde'),
  ]);
  phases.load = performance.now() - t0;

  // Setup state
  t0 = performance.now();
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
  phases.parseState = performance.now() - t0;

  // Load code
  t0 = performance.now();
  const codeFile = fs.readFileSync(
    path.join(__dirname, 'fixtures/multisig_code.mde'),
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
  phases.parseCode = performance.now() - t0;

  console.log(`State: ${Object.keys(state.linear).length} facts`);
  console.log(`Rules: ${calc.forwardRules.length} forward rules\n`);

  // Detailed step-by-step execution
  console.log('STEP-BY-STEP EXECUTION');
  console.log('-'.repeat(70));

  const forward = require('../../lib/v2/prover/strategy/forward');
  let currentState = state;
  const stepTimes = [];
  const stepDetails = [];
  const maxSteps = 50;

  for (let step = 0; step < maxSteps; step++) {
    const t1 = performance.now();

    // Find matching rule
    const match = forward.findMatch(currentState, calc.forwardRules, {
      clauses: calc.clauses,
      types: calc.types
    });

    const t2 = performance.now();

    if (!match) {
      console.log(`\nStep ${step}: No match (quiescent)`);
      break;
    }

    // Apply match
    const t3 = performance.now();
    currentState = forward.applyMatch(currentState, match);
    const t4 = performance.now();

    const findTime = t2 - t1;
    const applyTime = t4 - t3;
    const totalStep = t4 - t1;

    stepTimes.push(totalStep);
    stepDetails.push({
      rule: match.rule.name,
      findTime,
      applyTime,
      totalStep
    });

    console.log(`Step ${step}: ${match.rule.name}`);
    console.log(`  findMatch: ${formatMs(findTime)}`);
    console.log(`  applyMatch: ${formatMs(applyTime)}`);
    console.log(`  total: ${formatMs(totalStep)}`);
  }

  console.log();
  console.log('SUMMARY');
  console.log('-'.repeat(70));
  console.log();

  const totalExec = stepTimes.reduce((a, b) => a + b, 0);
  const totalFindTime = stepDetails.reduce((a, d) => a + d.findTime, 0);
  const totalApplyTime = stepDetails.reduce((a, d) => a + d.applyTime, 0);

  console.log('Phase Breakdown:');
  console.log(`  Load rules:      ${formatMs(phases.load)}`);
  console.log(`  Parse state:     ${formatMs(phases.parseState)}`);
  console.log(`  Parse code:      ${formatMs(phases.parseCode)}`);
  console.log(`  Execute:         ${formatMs(totalExec)}`);
  console.log(`  TOTAL:           ${formatMs(phases.load + phases.parseState + phases.parseCode + totalExec)}`);
  console.log();

  console.log('Execution Breakdown:');
  console.log(`  findMatch total: ${formatMs(totalFindTime)} (${(totalFindTime/totalExec*100).toFixed(1)}%)`);
  console.log(`  applyMatch total: ${formatMs(totalApplyTime)} (${(totalApplyTime/totalExec*100).toFixed(1)}%)`);
  console.log();

  console.log('Per-Step Analysis:');
  console.log(`  Steps: ${stepTimes.length}`);
  console.log(`  Avg step time: ${formatMs(totalExec / stepTimes.length)}`);
  console.log(`  Avg findMatch: ${formatMs(totalFindTime / stepTimes.length)}`);
  console.log(`  Avg applyMatch: ${formatMs(totalApplyTime / stepTimes.length)}`);
  console.log();

  // Find slowest steps
  const sorted = [...stepDetails].sort((a, b) => b.totalStep - a.totalStep);
  console.log('Slowest Steps:');
  for (let i = 0; i < Math.min(3, sorted.length); i++) {
    const s = sorted[i];
    console.log(`  ${s.rule}: ${formatMs(s.totalStep)} (find: ${formatMs(s.findTime)})`);
  }
}

main().catch(console.error);
