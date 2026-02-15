/**
 * Deep Profiler - Uses built-in profiling in forward.js
 *
 * Run with: CALC_PROFILE=1 node tests/mde/multisig-profile-deep.js
 */

const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const fs = require('fs');
const path = require('path');
const { performance } = require('perf_hooks');

const forward = require('../../lib/engine/forward');

function formatMs(ms) {
  if (ms < 0.001) return `${(ms * 1000000).toFixed(0)}ns`;
  if (ms < 1) return `${(ms * 1000).toFixed(1)}µs`;
  return `${ms.toFixed(2)}ms`;
}

async function main() {
  if (process.env.CALC_PROFILE !== '1') {
    console.log('Run with CALC_PROFILE=1 to enable profiling');
    console.log('  CALC_PROFILE=1 node tests/mde/multisig-profile-deep.js');
    process.exit(1);
  }

  console.log('='.repeat(70));
  console.log('DEEP PROFILER - Forward Engine Internals');
  console.log('='.repeat(70));
  console.log();

  // Load
  const calc = await mde.load([
    path.join(__dirname, '../../calculus/ill/programs/bin.ill'),
    path.join(__dirname, '../../calculus/ill/programs/evm.ill'),
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
  ]);

  // Setup state
  const state = { linear: {}, persistent: {} };
  const basicFacts = ['pc N_75', 'sh ee', 'gas N_ffff', 'caller sender_addr', 'sender member01'];
  for (const f of basicFacts) {
    const h = await mde.parseExpr(f);
    state.linear[h] = 1;
  }

  // Load code
  const codeFile = fs.readFileSync(path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'), 'utf8');
  for (const line of codeFile.split('\n')) {
    const trimmed = line.split('%')[0].trim();
    if (!trimmed || !trimmed.startsWith('code')) continue;
    const parts = trimmed.replace(/\*.*$/, '').trim();
    if (parts) {
      const h = await mde.parseExpr(parts);
      state.linear[h] = 1;
    }
  }

  console.log(`State: ${Object.keys(state.linear).length} facts`);
  console.log(`Rules: ${calc.forwardRules.length} forward rules`);
  console.log();

  // Execute step by step with profiling
  let currentState = state;
  const stepStats = [];

  // Build indices once (like run() does)
  const opcodeIndex = forward.buildOpcodeIndex(calc.forwardRules);
  const indexedRules = { rules: calc.forwardRules, opcodeIndex };

  // Build backward prover index once
  const { buildIndex: buildBackwardIndex } = require('../../lib/engine/prove');
  const backwardIndex = buildBackwardIndex(calc.clauses, calc.types);
  const calcWithIndex = {
    clauses: calc.clauses,
    types: calc.types,
    backwardIndex
  };

  for (let step = 0; step < 10; step++) {
    forward.resetProfile();

    const t0 = performance.now();
    const match = forward.findMatch(currentState, indexedRules, calcWithIndex);
    const findTime = performance.now() - t0;

    const prof = forward.getProfile();

    if (!match) {
      console.log(`Step ${step}: No match (quiescent)\n`);
      break;
    }

    const t1 = performance.now();
    currentState = forward.applyMatch(currentState, match);
    const applyTime = performance.now() - t1;

    stepStats.push({
      rule: match.rule.name,
      findTime,
      applyTime,
      ...prof
    });

    const accounted = prof.matchTime + prof.proveTime + prof.subTime;
    const overhead = findTime - accounted;

    console.log(`Step ${step}: ${match.rule.name} (${formatMs(findTime)})`);
    console.log(`  unify.match:  ${formatMs(prof.matchTime)} (${prof.matchCalls} calls) - ${(prof.matchTime/findTime*100).toFixed(1)}%`);
    console.log(`  prove:        ${formatMs(prof.proveTime)} (${prof.proveCalls} calls) - ${(prof.proveTime/findTime*100).toFixed(1)}%`);
    console.log(`  substitute:   ${formatMs(prof.subTime)} (${prof.subCalls} calls) - ${(prof.subTime/findTime*100).toFixed(1)}%`);
    console.log(`  overhead:     ${formatMs(overhead)} - ${(overhead/findTime*100).toFixed(1)}%`);
    console.log();
  }

  // Summary
  console.log('TOTALS');
  console.log('-'.repeat(70));
  const totalFind = stepStats.reduce((a, s) => a + s.findTime, 0);
  const totalApply = stepStats.reduce((a, s) => a + s.applyTime, 0);
  const totalMatch = stepStats.reduce((a, s) => a + s.matchTime, 0);
  const totalProve = stepStats.reduce((a, s) => a + s.proveTime, 0);
  const totalSub = stepStats.reduce((a, s) => a + s.subTime, 0);
  const totalMatchCalls = stepStats.reduce((a, s) => a + s.matchCalls, 0);
  const totalProveCalls = stepStats.reduce((a, s) => a + s.proveCalls, 0);
  const totalSubCalls = stepStats.reduce((a, s) => a + s.subCalls, 0);
  const overhead = totalFind - totalMatch - totalProve - totalSub;

  console.log(`Total execution: ${formatMs(totalFind + totalApply)}`);
  console.log(`  findMatch:    ${formatMs(totalFind)} (${(totalFind/(totalFind+totalApply)*100).toFixed(1)}%)`);
  console.log(`  applyMatch:   ${formatMs(totalApply)} (${(totalApply/(totalFind+totalApply)*100).toFixed(1)}%)`);
  console.log();

  console.log('findMatch breakdown:');
  console.log(`  unify.match:  ${formatMs(totalMatch)} (${(totalMatch/totalFind*100).toFixed(1)}%) - ${totalMatchCalls} calls, ${formatMs(totalMatch/totalMatchCalls)}/call`);
  console.log(`  prove:        ${formatMs(totalProve)} (${(totalProve/totalFind*100).toFixed(1)}%) - ${totalProveCalls} calls, ${formatMs(totalProve/totalProveCalls)}/call`);
  console.log(`  substitute:   ${formatMs(totalSub)} (${(totalSub/totalFind*100).toFixed(1)}%) - ${totalSubCalls} calls`);
  console.log(`  overhead:     ${formatMs(overhead)} (${(overhead/totalFind*100).toFixed(1)}%)`);
  console.log();

  console.log('Per-step averages:');
  console.log(`  Match calls/step: ${(totalMatchCalls / stepStats.length).toFixed(0)}`);
  console.log(`  Prove calls/step: ${(totalProveCalls / stepStats.length).toFixed(1)}`);
  console.log(`  Time/step:        ${formatMs(totalFind / stepStats.length)}`);
}

main().catch(console.error);
