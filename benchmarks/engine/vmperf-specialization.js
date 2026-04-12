#!/usr/bin/env node
/**
 * VMPerformance Specialization Benchmark
 *
 * Compares generic vs per-contract-specialized execution (with basic block
 * fusion + JUMPDEST barriers) on actual vmPerformance loop test bytecodes.
 *
 * Usage: node benchmarks/engine/vmperf-specialization.js [--steps=N] [--test=name]
 */

'use strict';

const path = require('path');
const fs = require('fs');
const { performance } = require('perf_hooks');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const { loadBytecode, bytecodeArrGetGuard } = require('../../lib/engine/ill/bytecode-loader');
const { intToBin } = require('../../lib/engine/ill/ffi/convert');
const { fixtureToState, hexToBigInt } = require('../../tests/engine/vmtest/translate');

const EVM_PATH = path.join(__dirname, '../../calculus/ill/programs/evm.ill');
const FIXTURES_DIR = path.join(__dirname, '../../tests/fixtures/VMTests/vmPerformance');

function entryPointsToBarriers(entryPoints) {
  const barriers = new Set();
  for (const pc of entryPoints) {
    barriers.add(intToBin(BigInt(pc)));
  }
  return barriers;
}

function patchBytecodeHash(state, arrayHash) {
  const bcTagId = Store.TAG['bytecode'];
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tagId(hNum) === bcTagId) {
      delete state.linear[h];
      state.linear[Store.put('bytecode', [arrayHash])] = 1;
      return;
    }
  }
}

function main() {
  const args = process.argv.slice(2);
  let MAX_STEPS = 5000;
  let testName = 'loop-add-10M';
  for (const a of args) {
    if (a.startsWith('--steps=')) MAX_STEPS = parseInt(a.slice(8), 10);
    if (a.startsWith('--test=')) testName = a.slice(7);
  }

  const fixturePath = path.join(FIXTURES_DIR, testName + '.json');
  if (!fs.existsSync(fixturePath)) {
    console.error(`Fixture not found: ${fixturePath}`);
    process.exit(1);
  }

  const data = JSON.parse(fs.readFileSync(fixturePath, 'utf8'));
  const fixture = Object.values(data)[0];
  const hex = fixture.exec.code.startsWith('0x') ? fixture.exec.code.slice(2) : fixture.exec.code;
  const totalGas = hexToBigInt(fixture.exec.gas);

  console.log('='.repeat(72));
  console.log(`VMPerformance Specialization Benchmark: ${testName}`);
  console.log('='.repeat(72));
  console.log(`  Bytecode: ${hex.length / 2} bytes`);
  console.log(`  Total gas: ${totalGas}`);
  console.log(`  Measuring: ${MAX_STEPS} steps`);
  console.log();

  // Single Store session — no Store.clear() between loads
  Store.clear();

  // Load bytecode and compute barriers (must be in same Store session as mde.load)
  const bc = loadBytecode(hex);
  const barriers = entryPointsToBarriers(bc.entryPoints);
  console.log(`  Entry points: ${bc.entryPoints.size} (JUMPDESTs + PC=0)`);
  console.log(`  Grade-0 facts: ${bc.facts.get('arr_get').length}`);
  console.log();

  // ── 1. Load generic calc ──
  console.log('Loading generic calc...');
  const t0g = performance.now();
  const calcGeneric = mde.load(EVM_PATH, { cache: false });
  const loadGenericMs = performance.now() - t0g;
  console.log(`  Generic: ${calcGeneric.forwardRules.length} rules (${loadGenericMs.toFixed(0)}ms)`);

  // ── 2. Load specialized + fused with JUMPDEST barriers ──
  console.log('Loading specialized (fusion + barriers)...');
  const t0f = performance.now();
  const calcFused = mde.load(EVM_PATH, {
    cache: false,
    extraGrade0Facts: bc.facts,
    scopeGuard: bytecodeArrGetGuard,
    fusionBarriers: barriers,
  });
  const loadFusedMs = performance.now() - t0f;
  console.log(`  Fused: ${calcFused.forwardRules.length} rules (${loadFusedMs.toFixed(0)}ms)`);
  console.log();

  // ── Build states ──
  const stateGeneric = fixtureToState(fixture, calcGeneric);
  const stateFused = fixtureToState(fixture, calcFused);
  patchBytecodeHash(stateFused, bc.arrayHash);

  // ── Run generic ──
  console.log(`Running generic (${MAX_STEPS} steps)...`);
  const t1g = performance.now();
  const resGeneric = calcGeneric.exec(stateGeneric, { maxSteps: MAX_STEPS });
  const runGenericMs = performance.now() - t1g;
  const genericSps = (resGeneric.steps / runGenericMs) * 1000;
  console.log(`  Steps: ${resGeneric.steps}, Time: ${runGenericMs.toFixed(1)}ms, ${genericSps.toFixed(0)} sps, quiescent: ${resGeneric.quiescent}`);

  // ── Run fused ──
  console.log(`Running fused (${MAX_STEPS} steps)...`);
  const t1f = performance.now();
  const resFused = calcFused.exec(stateFused, { maxSteps: MAX_STEPS });
  const runFusedMs = performance.now() - t1f;
  const fusedSps = (resFused.steps / runFusedMs) * 1000;
  console.log(`  Steps: ${resFused.steps}, Time: ${runFusedMs.toFixed(1)}ms, ${fusedSps.toFixed(0)} sps, quiescent: ${resFused.quiescent}`);
  console.log();

  // ── Trace fused to verify correctness ──
  if (resFused.quiescent && resFused.steps < MAX_STEPS) {
    console.log('─── Fused trace (stuck?) ───');
    const stateFused2 = fixtureToState(fixture, calcFused);
    patchBytecodeHash(stateFused2, bc.arrayHash);
    const traceResult = calcFused.exec(stateFused2, { maxSteps: 50, trace: true });
    console.log(`  Steps: ${traceResult.steps}, quiescent: ${traceResult.quiescent}`);
    for (const t of traceResult.trace.slice(0, 15)) console.log(`  ${t}`);
    console.log();
  }

  // ── Results ──
  console.log('─── Results ───');
  const speedup = fusedSps / (genericSps || 1);
  console.log(`  Generic: ${genericSps.toFixed(0)} steps/sec`);
  console.log(`  Fused:   ${fusedSps.toFixed(0)} steps/sec`);
  console.log(`  Speedup: ${speedup.toFixed(2)}x`);
  console.log();

  // ── Extrapolation ──
  console.log('─── Extrapolation (10M iterations × ~16 steps/iter = 160M steps) ───');
  const totalSteps = 160_000_000;
  if (!resGeneric.quiescent) {
    console.log(`  Generic: ~${formatDuration(totalSteps / genericSps)}`);
  } else {
    console.log(`  Generic: quiesced at ${resGeneric.steps} steps`);
  }
  if (!resFused.quiescent) {
    console.log(`  Fused:   ~${formatDuration(totalSteps / fusedSps)}`);
  } else {
    console.log(`  Fused:   quiesced at ${resFused.steps} steps`);
  }
}

function formatDuration(seconds) {
  if (seconds < 60) return `${seconds.toFixed(1)}s`;
  if (seconds < 3600) return `${(seconds / 60).toFixed(1)} min`;
  if (seconds < 86400) return `${(seconds / 3600).toFixed(1)} hours`;
  return `${(seconds / 86400).toFixed(1)} days`;
}

main();
