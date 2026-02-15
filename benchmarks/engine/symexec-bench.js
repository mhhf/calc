#!/usr/bin/env node
/**
 * Symexec Tree Benchmark — Multisig EVM
 *
 * Measures full symbolic execution tree exploration for the multisig contract.
 * Records baseline JSON for comparison across optimizations.
 *
 * Usage:
 *   node benchmarks/engine/symexec-bench.js              # run benchmark
 *   node benchmarks/engine/symexec-bench.js --save       # save baseline
 *   node benchmarks/engine/symexec-bench.js --compare    # compare to baseline
 *   node benchmarks/engine/symexec-bench.js --profile    # detailed function breakdown
 *   CALC_PROFILE=1 node benchmarks/engine/symexec-bench.js --profile  # with forward internals
 */

const path = require('path');
const fs = require('fs');
const { performance } = require('perf_hooks');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const forward = require('../../lib/engine/forward');
const symexec = require('../../lib/engine/symexec');

const BASELINE_PATH = path.join(__dirname, 'symexec-baseline.json');
const WARMUP = 3;
const RUNS = 10;

// ─── Formatting helpers ─────────────────────────────────────────────────────

function fmt(ms) {
  if (ms < 0.001) return `${(ms * 1e6).toFixed(0)}ns`;
  if (ms < 1) return `${(ms * 1e3).toFixed(1)}µs`;
  if (ms < 1000) return `${ms.toFixed(2)}ms`;
  return `${(ms / 1000).toFixed(2)}s`;
}

function pct(part, whole) { return whole > 0 ? (part / whole * 100).toFixed(1) : '0.0'; }

function stats(arr) {
  const sorted = [...arr].sort((a, b) => a - b);
  const sum = arr.reduce((a, b) => a + b, 0);
  const mean = sum / arr.length;
  const median = sorted[Math.floor(sorted.length / 2)];
  const p95 = sorted[Math.floor(sorted.length * 0.95)];
  const min = sorted[0];
  const max = sorted[sorted.length - 1];
  const stddev = Math.sqrt(arr.reduce((s, x) => s + (x - mean) ** 2, 0) / arr.length);
  return { mean, median, p95, min, max, stddev };
}

// ─── State setup ─────────────────────────────────────────────────────────────

async function setupState() {
  const calc = await mde.load([
    path.join(__dirname, '../../calculus/ill/programs/bin.ill'),
    path.join(__dirname, '../../calculus/ill/programs/evm.ill'),
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
  ]);

  const state = { linear: {}, persistent: {} };
  for (const f of ['pc N_75', 'sh ee', 'gas N_ffff', 'caller sender_addr', 'sender member01']) {
    state.linear[await mde.parseExpr(f)] = 1;
  }

  const codeFile = fs.readFileSync(
    path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'), 'utf8'
  );
  for (const line of codeFile.split('\n')) {
    const trimmed = line.split('%')[0].trim();
    if (!trimmed || !trimmed.startsWith('code')) continue;
    const parts = trimmed.replace(/\*.*$/, '').trim();
    if (parts) state.linear[await mde.parseExpr(parts)] = 1;
  }

  return { calc, state };
}

// ─── Instrumented explore ────────────────────────────────────────────────────

function instrumentedExplore(initialState, rules, calcCtx, maxDepth) {
  const timers = {
    findAllMatches: { time: 0, calls: 0 },
    hashState:      { time: 0, calls: 0 },
    expandChoices:  { time: 0, calls: 0 },
    mutateState:    { time: 0, calls: 0 },
    undoMutate:     { time: 0, calls: 0 },
    setClone:       { time: 0, calls: 0 },
    makeChildCtx:   { time: 0, calls: 0 },
    undoIndex:      { time: 0, calls: 0 },
    snapshot:       { time: 0, calls: 0 },
  };

  // Mutable copy
  const state = {
    linear: { ...initialState.linear },
    persistent: { ...initialState.persistent }
  };

  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = Array.isArray(rules) ? { rules } : rules;
  const strategy = symexec.detectStrategy(ruleList);

  // Mutable pathVisited: add before recursion, delete after (no Set copies)
  const pathVisited = new Set();

  function go(depth, ctx) {
    let t0;

    // Cycle detection uses numeric hash from context (incremental)
    t0 = performance.now();
    const sh = ctx.stateHash;
    timers.hashState.time += performance.now() - t0;
    timers.hashState.calls++;

    if (pathVisited.has(sh)) {
      t0 = performance.now();
      const snap = symexec.snapshotState(state);
      timers.snapshot.time += performance.now() - t0;
      timers.snapshot.calls++;
      return { type: 'cycle', state: snap };
    }
    if (depth >= maxDepth) {
      t0 = performance.now();
      const snap = symexec.snapshotState(state);
      timers.snapshot.time += performance.now() - t0;
      timers.snapshot.calls++;
      return { type: 'bound', state: snap };
    }

    t0 = performance.now();
    const matches = symexec.findAllMatches(state, indexedRules, calcCtx, strategy, ctx.stateIndex);
    timers.findAllMatches.time += performance.now() - t0;
    timers.findAllMatches.calls++;

    if (matches.length === 0) {
      t0 = performance.now();
      const snap = symexec.snapshotState(state);
      timers.snapshot.time += performance.now() - t0;
      timers.snapshot.calls++;
      return { type: 'leaf', state: snap };
    }

    pathVisited.add(sh);

    const children = [];
    for (let mi = 0; mi < matches.length; mi++) {
      const m = matches[mi];
      t0 = performance.now();
      const alts = m.rule.consequentAlts;
      timers.expandChoices.time += performance.now() - t0;
      timers.expandChoices.calls++;

      if (alts.length <= 1) {
        t0 = performance.now();
        const undo = symexec.mutateState(state, m.consumed, m.theta,
          m.rule.consequent.linear || [], m.rule.consequent.persistent || [],
          m.slots, m.optimized ? m.rule : null);
        timers.mutateState.time += performance.now() - t0;
        timers.mutateState.calls++;

        t0 = performance.now();
        const { ctx: childCtx, indexUndo } = symexec.makeChildCtx(ctx, state, undo);
        timers.makeChildCtx.time += performance.now() - t0;
        timers.makeChildCtx.calls++;

        const child = go(depth + 1, childCtx);

        t0 = performance.now();
        symexec.undoIndexChanges(ctx.stateIndex, indexUndo);
        timers.undoIndex.time += performance.now() - t0;
        timers.undoIndex.calls++;

        t0 = performance.now();
        symexec.undoMutate(state, undo);
        timers.undoMutate.time += performance.now() - t0;
        timers.undoMutate.calls++;

        children.push({ rule: m.rule.name, child });
      } else {
        for (let i = 0; i < alts.length; i++) {
          t0 = performance.now();
          const undo = symexec.mutateState(state, m.consumed, m.theta,
            alts[i].linear, alts[i].persistent, m.slots, null);
          timers.mutateState.time += performance.now() - t0;
          timers.mutateState.calls++;

          t0 = performance.now();
          const { ctx: childCtx, indexUndo } = symexec.makeChildCtx(ctx, state, undo);
          timers.makeChildCtx.time += performance.now() - t0;
          timers.makeChildCtx.calls++;

          const child = go(depth + 1, childCtx);

          t0 = performance.now();
          symexec.undoIndexChanges(ctx.stateIndex, indexUndo);
          timers.undoIndex.time += performance.now() - t0;
          timers.undoIndex.calls++;

          t0 = performance.now();
          symexec.undoMutate(state, undo);
          timers.undoMutate.time += performance.now() - t0;
          timers.undoMutate.calls++;

          children.push({ rule: m.rule.name, choice: i, child });
        }
      }
    }

    pathVisited.delete(sh);

    return { type: 'branch', state: null, children };
  }

  const fpConfig = strategy.fpConfig || null;
  const rootCtx = symexec.ExploreContext.fromState(state, fpConfig);
  const tree = go(0, rootCtx);
  return { tree, timers };
}

// ─── Benchmark run ───────────────────────────────────────────────────────────

async function runBenchmark(doProfile) {
  const { calc, state } = await setupState();
  const calcCtx = {
    clauses: calc.clauses,
    types: calc.types,
  };

  const linearCount = Object.keys(state.linear).length;
  const ruleCount = calc.forwardRules.length;

  console.log(`State: ${linearCount} facts | Rules: ${ruleCount}`);
  console.log();

  // ── Profile run ──
  if (doProfile) {
    forward.resetProfile();

    const { tree, timers } = instrumentedExplore(state, calc.forwardRules, calcCtx, 200);
    const totalTime = Object.values(timers).reduce((s, t) => s + t.time, 0);
    const prof = forward.getProfile();

    const nodes = symexec.countNodes(tree);
    const leaves = symexec.countLeaves(tree);
    const depth = symexec.maxDepth(tree);

    console.log(`Tree: ${nodes} nodes, ${leaves} leaves, depth ${depth}`);
    console.log();

    console.log('FUNCTION BREAKDOWN');
    console.log('─'.repeat(75));
    const rows = [
      ['findAllMatches',       timers.findAllMatches],
      ['hashState',            timers.hashState],
      ['expandConsequentChoices', timers.expandChoices],
      ['mutateState',          timers.mutateState],
      ['undoMutate',           timers.undoMutate],
      ['makeChildCtx',         timers.makeChildCtx],
      ['undoIndexChanges',     timers.undoIndex],
      ['snapshotState',        timers.snapshot],
    ];
    for (const [name, t] of rows) {
      if (t.calls === 0) continue;
      const perCall = t.time / t.calls * 1000;
      console.log(`  ${name.padEnd(30)} ${fmt(t.time).padStart(10)} (${pct(t.time, totalTime).padStart(5)}%) ${String(t.calls).padStart(6)} calls ${fmt(perCall / 1000).padStart(10)}/call`);
    }
    console.log();

    if (prof.matchCalls > 0) {
      const famTime = timers.findAllMatches.time;
      const accounted = prof.matchTime + prof.proveTime + prof.subTime;
      console.log('INSIDE findAllMatches (CALC_PROFILE):');
      console.log(`  unify.match:  ${fmt(prof.matchTime).padStart(10)} (${pct(prof.matchTime, famTime).padStart(5)}%) ${String(prof.matchCalls).padStart(8)} calls ${fmt(prof.matchTime / prof.matchCalls).padStart(10)}/call`);
      console.log(`  prove:        ${fmt(prof.proveTime).padStart(10)} (${pct(prof.proveTime, famTime).padStart(5)}%) ${String(prof.proveCalls).padStart(8)} calls ${fmt(prof.proveTime / prof.proveCalls).padStart(10)}/call`);
      console.log(`  substitute:   ${fmt(prof.subTime).padStart(10)} (${pct(prof.subTime, famTime).padStart(5)}%) ${String(prof.subCalls).padStart(8)} calls`);
      console.log(`  overhead:     ${fmt(famTime - accounted).padStart(10)} (${pct(famTime - accounted, famTime).padStart(5)}%)`);
      console.log();
      console.log('KEY METRICS:');
      console.log(`  match calls / node:  ${(prof.matchCalls / nodes).toFixed(0)}`);
      console.log(`  prove calls / node:  ${(prof.proveCalls / nodes).toFixed(1)}`);
      console.log(`  time / node:         ${fmt(totalTime / nodes)}`);
    }

    return;
  }

  // ── Statistical benchmark ──
  console.log(`Warmup: ${WARMUP} runs, Benchmark: ${RUNS} runs`);
  console.log();

  const timings = [];

  for (let i = 0; i < WARMUP + RUNS; i++) {
    const t0 = performance.now();
    const tree = symexec.explore(state, calc.forwardRules, {
      maxDepth: 200,
      calc: calcCtx
    });
    const elapsed = performance.now() - t0;

    if (i >= WARMUP) {
      timings.push(elapsed);

      // Record tree metrics on first measured run
      if (i === WARMUP) {
        const nodes = symexec.countNodes(tree);
        const leaves = symexec.countLeaves(tree);
        const depth = symexec.maxDepth(tree);
        const leafTypes = {};
        for (const l of symexec.getAllLeaves(tree)) {
          leafTypes[l.type] = (leafTypes[l.type] || 0) + 1;
        }
        console.log(`Tree: ${nodes} nodes, ${leaves} leaves, depth ${depth}`);
        console.log(`Leaf types: ${JSON.stringify(leafTypes)}`);
        console.log();
      }
    }

    process.stdout.write(`\r  ${i < WARMUP ? 'warmup' : 'run'} ${i + 1}/${WARMUP + RUNS}: ${fmt(elapsed)}`);
  }
  console.log('\n');

  const s = stats(timings);
  console.log('RESULTS');
  console.log('─'.repeat(50));
  console.log(`  Mean:    ${fmt(s.mean)}`);
  console.log(`  Median:  ${fmt(s.median)}`);
  console.log(`  P95:     ${fmt(s.p95)}`);
  console.log(`  Min:     ${fmt(s.min)}`);
  console.log(`  Max:     ${fmt(s.max)}`);
  console.log(`  Stddev:  ${fmt(s.stddev)} (${pct(s.stddev, s.mean)}%)`);

  return {
    date: new Date().toISOString(),
    runs: RUNS,
    facts: linearCount,
    rules: ruleCount,
    tree: {
      nodes: symexec.countNodes(symexec.explore(state, calc.forwardRules, { maxDepth: 200, calc: calcCtx })),
    },
    timing: {
      mean: s.mean,
      median: s.median,
      p95: s.p95,
      min: s.min,
      max: s.max,
      stddev: s.stddev,
    }
  };
}

// ─── Comparison ──────────────────────────────────────────────────────────────

function compareBaseline(current) {
  if (!fs.existsSync(BASELINE_PATH)) {
    console.log('\nNo baseline found. Run with --save first.');
    return;
  }

  const baseline = JSON.parse(fs.readFileSync(BASELINE_PATH, 'utf8'));
  console.log(`\nCOMPARISON vs baseline (${baseline.date})`);
  console.log('─'.repeat(50));

  const bm = baseline.timing.median;
  const cm = current.timing.median;
  const diff = ((cm - bm) / bm * 100);
  const symbol = diff < -5 ? '↓' : diff > 5 ? '↑' : '≈';

  console.log(`  Baseline median: ${fmt(bm)}`);
  console.log(`  Current median:  ${fmt(cm)}`);
  console.log(`  Change:          ${diff > 0 ? '+' : ''}${diff.toFixed(1)}% ${symbol}`);

  if (baseline.tree && current.tree) {
    console.log(`  Tree nodes:      ${baseline.tree.nodes} → ${current.tree.nodes}`);
  }
}

// ─── Main ────────────────────────────────────────────────────────────────────

async function main() {
  const args = process.argv.slice(2);
  const doSave = args.includes('--save');
  const doCompare = args.includes('--compare');
  const doProfile = args.includes('--profile');

  console.log('═'.repeat(60));
  console.log('  SYMEXEC TREE BENCHMARK — EVM Multisig');
  console.log('═'.repeat(60));
  console.log();

  const result = await runBenchmark(doProfile);

  if (doProfile) return;

  if (doSave) {
    fs.writeFileSync(BASELINE_PATH, JSON.stringify(result, null, 2));
    console.log(`\nBaseline saved to ${BASELINE_PATH}`);
  }

  if (doCompare) {
    compareBaseline(result);
  } else if (fs.existsSync(BASELINE_PATH)) {
    // Auto-compare if baseline exists
    compareBaseline(result);
  }
}

main().catch(console.error);
