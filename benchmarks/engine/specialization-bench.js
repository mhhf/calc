#!/usr/bin/env node
/**
 * Specialization Benchmark — Runtime validation of TODO 160.
 *
 * Compares forward execution speed with and without compile-time
 * bytecode specialization (arr_get cut elimination).
 *
 * Three comparisons:
 *   1. exec (noFFI)  — adversarial mode, clause-based backward chaining
 *   2. exec (FFI)    — production mode, FFI-accelerated backward chaining
 *   3. explore       — exhaustive DFS (where per-step overhead compounds)
 *
 * Usage: node benchmarks/engine/specialization-bench.js [--runs=N]
 */

'use strict';

const path = require('path');
const { performance } = require('perf_hooks');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const { loadBytecode, bytecodeArrGetGuard } = require('../../lib/engine/ill/bytecode-loader');
const { intToBin } = require('../../lib/engine/ill/ffi/convert');

const EVM_PATH = path.join(__dirname, '../../calculus/ill/programs/evm.ill');

// ── Benchmark bytecodes ─────────────────────────────────────────────────────

// 20-step straight-line: 10× PUSH1 + 9× ADD + STOP
const SMALL_HEX = '6001600201600301600401600501600601600701600801600901600a0100';

// ── State construction ──────────────────────────────────────────────────────

function buildState(bytecodeArrHash) {
  const ae = Store.put('atom', ['ae']);
  return {
    linear: {
      [Store.put('bytecode', [bytecodeArrHash])]: 1,
      [Store.put('pc', [intToBin(0n)])]: 1,
      [Store.put('gas', [intToBin(0xffffffn)])]: 1,
      [Store.put('stack', [ae])]: 1,
    },
    persistent: {},
  };
}

// ── Statistics ──────────────────────────────────────────────────────────────

function stats(arr) {
  if (arr.length === 0) return { mean: 0, median: 0, min: 0, max: 0, p95: 0 };
  const sorted = [...arr].sort((a, b) => a - b);
  const sum = arr.reduce((a, b) => a + b, 0);
  return {
    mean: sum / arr.length,
    median: sorted[Math.floor(sorted.length / 2)],
    min: sorted[0],
    max: sorted[sorted.length - 1],
    p95: sorted[Math.floor(sorted.length * 0.95)],
  };
}

function fmtMs(ms) {
  if (ms < 0.01) return `${(ms * 1000).toFixed(1)}µs`;
  if (ms < 1) return `${(ms * 1000).toFixed(0)}µs`;
  return `${ms.toFixed(2)}ms`;
}

function reportPair(label, baseTimes, specTimes, baseSteps, specSteps) {
  const b = stats(baseTimes);
  const s = stats(specTimes);
  console.log(`  ${label}:`);
  console.log(`    Baseline:    median=${fmtMs(b.median)}  (${fmtMs(b.median / (baseSteps || 1))}/step)`);
  console.log(`    Specialized: median=${fmtMs(s.median)}  (${fmtMs(s.median / (specSteps || 1))}/step)`);
  const speedup = b.median / (s.median || 1);
  console.log(`    Speedup:     ${speedup.toFixed(2)}x`);
  console.log();
  return speedup;
}

// ── Tree utilities ──────────────────────────────────────────────────────────

function countNodes(tree) {
  if (!tree) return 0;
  if (tree.type === 'branch') {
    let n = 1;
    for (const c of tree.children) n += countNodes(c.child);
    return n;
  }
  return 1;
}

function countLeaves(tree) {
  if (!tree) return 0;
  if (tree.type === 'branch') {
    let n = 0;
    for (const c of tree.children) n += countLeaves(c.child);
    return n;
  }
  return 1;
}

function maxDepth(tree, d = 0) {
  if (!tree) return d;
  if (tree.type === 'branch') {
    let m = d;
    for (const c of tree.children) m = Math.max(m, maxDepth(c.child, d + 1));
    return m;
  }
  return d;
}

// ── Main benchmark ──────────────────────────────────────────────────────────

function main() {
  const args = process.argv.slice(2);
  let RUNS = 20;
  for (const a of args) {
    if (a.startsWith('--runs=')) RUNS = parseInt(a.slice(7), 10);
  }

  const hex = SMALL_HEX;

  console.log('='.repeat(72));
  console.log('SPECIALIZATION BENCHMARK — Runtime validation (TODO 160)');
  console.log('='.repeat(72));
  console.log(`  Bytecode: ${hex.length / 2} bytes, ${RUNS} runs per measurement`);
  console.log();

  // ── Load both calcs in same Store ──
  Store.clear();
  const calcBase = mde.load(EVM_PATH, { cache: false });
  const bc = loadBytecode(hex);
  const calcSpec = mde.load(EVM_PATH, {
    cache: false,
    extraGrade0Facts: bc.facts,
    scopeGuard: bytecodeArrGetGuard,
  });
  const state = buildState(bc.arrayHash);

  console.log(`  Rules: baseline=${calcBase.forwardRules.length}, specialized=${calcSpec.forwardRules.length}`);

  // Verify both produce same result
  const checkBase = calcBase.exec(state, { maxSteps: 100, trace: true });
  const checkSpec = calcSpec.exec(state, { maxSteps: 100, trace: true });
  console.log(`  Steps: baseline=${checkBase.steps}, specialized=${checkSpec.steps}`);
  console.log(`  Trace (base): ${checkBase.trace.slice(0, 3).map(t => t.replace(/^\[\d+\]\s*/, '')).join(' → ')} ...`);
  console.log(`  Trace (spec): ${checkSpec.trace.slice(0, 3).map(t => t.replace(/^\[\d+\]\s*/, '')).join(' → ')} ...`);
  console.log();

  // ── 1. exec (noFFI) — adversarial mode ──
  console.log('─── exec (noFFI mode) — clause-based backward chaining ───');
  console.log();

  // warmup
  for (let i = 0; i < 3; i++) {
    calcBase.exec(state, { maxSteps: 100 });
    calcSpec.exec(state, { maxSteps: 100 });
  }

  const noFFIBase = [], noFFISpec = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    calcBase.exec(state, { maxSteps: 100 });
    noFFIBase.push(performance.now() - t0);
  }
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    calcSpec.exec(state, { maxSteps: 100 });
    noFFISpec.push(performance.now() - t0);
  }
  reportPair('noFFI', noFFIBase, noFFISpec, checkBase.steps, checkSpec.steps);

  // ── 2. exec (FFI) — production mode ──
  console.log('─── exec (FFI mode) — production path ───');
  console.log();

  // warmup
  for (let i = 0; i < 3; i++) {
    calcBase.exec(state, { maxSteps: 100, dangerouslyUseFFI: true });
    calcSpec.exec(state, { maxSteps: 100, dangerouslyUseFFI: true });
  }

  const ffiBase = [], ffiSpec = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    calcBase.exec(state, { maxSteps: 100, dangerouslyUseFFI: true });
    ffiBase.push(performance.now() - t0);
  }
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    calcSpec.exec(state, { maxSteps: 100, dangerouslyUseFFI: true });
    ffiSpec.push(performance.now() - t0);
  }
  reportPair('FFI', ffiBase, ffiSpec, checkBase.steps, checkSpec.steps);

  // ── 3. explore — exhaustive DFS ──
  console.log('─── explore (noFFI) — exhaustive DFS ───');
  console.log();

  // warmup
  for (let i = 0; i < 2; i++) {
    calcBase.explore(state, { maxDepth: 25 });
    calcSpec.explore(state, { maxDepth: 25 });
  }

  const exploreBase = [], exploreSpec = [];
  let baseTree, specTree;
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    const tree = calcBase.explore(state, { maxDepth: 25 });
    exploreBase.push(performance.now() - t0);
    if (!baseTree) baseTree = tree;
  }
  for (let i = 0; i < RUNS; i++) {
    const t0 = performance.now();
    const tree = calcSpec.explore(state, { maxDepth: 25 });
    exploreSpec.push(performance.now() - t0);
    if (!specTree) specTree = tree;
  }

  const baseNodes = countNodes(baseTree);
  const specNodes = countNodes(specTree);
  const baseLeaves = countLeaves(baseTree);
  const specLeaves = countLeaves(specTree);
  console.log(`  Tree: baseline=${baseNodes} nodes/${baseLeaves} leaves, specialized=${specNodes} nodes/${specLeaves} leaves`);
  const bE = stats(exploreBase);
  const sE = stats(exploreSpec);
  console.log(`  Baseline:    median=${fmtMs(bE.median)}`);
  console.log(`  Specialized: median=${fmtMs(sE.median)}`);
  console.log(`  Speedup:     ${(bE.median / (sE.median || 1)).toFixed(2)}x`);
  console.log();
}

main();
