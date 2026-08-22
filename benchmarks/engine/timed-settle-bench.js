/**
 * Timed-settle olympic benchmarks — TODO_0277.
 *
 * The target contract (0277): settle+view must be a few ms at ANY horizon,
 * steady-state memory flat, cost dependent only on live distinct facts —
 * never on elapsed time or nominal magnitudes.
 *
 *   B1 ticks       PP2 game tick loop (200 ms ticks) — per-tick settle ms at
 *                  game-time checkpoints. PASS: flat across checkpoints.
 *   B2 magnitude   !_10^k iron seeded, one settle. PASS: k-independent.
 *   B3 memory      long tick run — Store arena + linear entries. PASS: plateau.
 *   OR rules       N-rule calculi (one active) — per-settle cost vs N.
 *   OF cohorts     N distinct-stamp cohorts, drain one step — cost vs N.
 *   OT deep-time   small periodic economy settled 0 → T. PASS: O(1) in T
 *                  (needs loop acceleration; linear = #events until then).
 *
 * Usage: node benchmarks/engine/timed-settle-bench.js [--json out.json]
 *        [--only B1,OT] [--ticks N] [--coalesce]
 */

import path from 'path';
import os from 'os';
import fs from 'fs';
import { performance } from 'perf_hooks';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

const ROOT = path.join(import.meta.dirname, '../../');
const PP2 = path.join(ROOT, 'calculus/till/game/PP2.till');

const args = process.argv.slice(2);
const flag = (n) => args.includes(n);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const ONLY = opt('--only', null)?.split(',') || null;
const run = (id) => !ONLY || ONLY.includes(id);
const COALESCE = flag('--coalesce');
const ACCEL = flag('--accel');
const results = {};

const horizonOf = (secs) => `${Math.max(0, Math.round(secs * 1000))}/1000`;
const atom = (n) => Store.put('atom', [n]);
const settleOpts = {
  ...(COALESCE ? { coalesce: true } : {}),
  ...(ACCEL ? { accelerate: true } : {}),
};

function liveLinear(state) {
  return Object.keys(state.linear || {}).length;
}

function report(id, rows, cols) {
  console.log(`\n── ${id} ─────────────────────────────`);
  console.log(cols.map(c => String(c).padStart(11)).join(''));
  for (const r of rows) console.log(r.map(v =>
    String(typeof v === 'number' && !Number.isInteger(v) ? v.toFixed(2) : v).padStart(11)).join(''));
  results[id] = { cols, rows };
}

// ── B1 + B3: PP2 tick loop ──────────────────────────────────────────
// Drives the real game model exactly like the bridge: settle each 200 ms
// tick to T = ticks*0.2, plus a view proxy (menuStatus sweep over standing
// menus — the bridge's per-tick UI query).
if (run('B1')) {
  const calc = mde.load(PP2, { calculusConfig: tillConfig, cache: false });
  const start = convert.decomposeQuery(calc.splitQueries.get('expect_shell_start').lhsHash);
  let state = start;
  const dt = 0.2;
  const totalTicks = Number(opt('--ticks', 1500));   // 1500 ticks = 300 s game time
  const checkpoints = new Set(
    [8, 30, 60, 120, 180, 300, 600, 1200, 3600].map(s => Math.round(s / dt)));
  const rows = [];
  const menus = [];
  for (const hStr in (state.persistent || {})) {
    if (Store.tag(Number(hStr)) === 'with') menus.push(Number(hStr));
  }
  const t0all = performance.now();
  for (let i = 1; i <= totalTicks; i++) {
    const T = i * dt;
    const t0 = performance.now();
    const r = calc.settle(state, horizonOf(T), settleOpts);
    state = r.state;
    // view proxy: menu greying + a full state scan (what the HUD reads)
    for (const m of menus) calc.menuStatus(state, m, horizonOf(T));
    let scan = 0;
    for (const hStr in state.linear) scan += state.linear[hStr];
    const ms = performance.now() - t0;
    if (checkpoints.has(i)) {
      rows.push([T, ms, liveLinear(state), Store.size(),
        Math.round(process.memoryUsage().rss / 1e6)]);
      if (performance.now() - t0all > 120000) { console.log('  (budget hit — stopping early)'); break; }
    }
  }
  report('B1-ticks', rows, ['T(s)', 'tick ms', 'linear', 'store', 'rssMB']);
  const first = rows[0], last = rows[rows.length - 1];
  console.log(`  growth: tick ms ×${(last[1] / Math.max(first[1], 0.01)).toFixed(1)}, linear ×${(last[2] / Math.max(first[2], 1)).toFixed(1)} over ${(last[0] / first[0]).toFixed(0)}× time`);
}

// ── B3: steady-state memory — long tick run, Store/RSS plateau ──────
// Chained raw ticks with coalesce; rebase every 256 ticks resets the time
// origin so the stamp vocabulary stays finite. PASS: Store.size() and RSS
// plateau (no monotonic growth).
if (run('B3')) {
  const calc = mde.load(PP2, { calculusConfig: tillConfig, cache: false });
  let state = convert.decomposeQuery(calc.splitQueries.get('expect_shell_start').lhsHash);
  const dt = 0.2;
  const total = Number(opt('--b3ticks', 100000));
  let base = 0;
  const rows = [];
  const t0all = performance.now();
  for (let i = 1; i <= total; i++) {
    const T = i * dt - base;
    const r = calc.settle(state, horizonOf(T), {
      coalesce: true, raw: true, rebase: i % 256 === 0,
    });
    state = r.state;
    if (r.rebase !== undefined) {
      const [n, d] = ratParts(r.rebase);
      base += Number(n) / Number(d);
    }
    if (i % Math.floor(total / 10) === 0) {
      rows.push([i, (i * dt).toFixed(0), Store.size(),
        Math.round(process.memoryUsage().rss / 1e6),
        ((performance.now() - t0all) / i).toFixed(3)]);
    }
  }
  report('B3-memory', rows, ['tick', 'T(s)', 'store', 'rssMB', 'ms/tick']);
}

// ── B2: magnitude scaling — !_10^k wood, one kiln batch ─────────────
if (run('B2')) {
  const calc = mde.load(PP2, { calculusConfig: tillConfig, cache: false });
  const rows = [];
  for (let k = 0; k <= 6; k++) {
    const n = 10 ** k;
    const st = { linear: { [atom('kiln')]: 1, [atom('wood')]: n }, persistent: {} };
    const t0 = performance.now();
    const r = calc.settle(st, '10', settleOpts);
    const ms = performance.now() - t0;
    rows.push([`10^${k}`, ms, r.events.length]);
    if (ms > 500) { console.log('  (case exceeded 500 ms — skipping larger k)'); break; }
  }
  report('B2-magnitude', rows, ['count', 'settle ms', 'events']);
}

// ── OR: rule-count scaling ──────────────────────────────────────────
// N producer rules, each gated on its own machine token; only ONE machine
// present. Cost of settling 10 events should not scale with N.
if (run('OR')) {
  const rows = [];
  for (const N of [10, 100, 1000, 5000]) {
    let src = '';
    for (let i = 0; i < N; i++) src += `m${i}: type.\na${i}: type.\n`;
    for (let i = 0; i < N; i++) src += `p${i}: $m${i} -o { a${i} }@1.\n`;
    const file = path.join(os.tmpdir(), `till-or-${N}.till`);
    fs.writeFileSync(file, src);
    const t0l = performance.now();
    const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
    const loadMs = performance.now() - t0l;
    const st = { linear: { [atom('m0')]: 1 }, persistent: {} };
    const t0 = performance.now();
    const r = calc.settle(st, '10', { ...settleOpts, raw: true });   // p0 fires at 0..10
    const cold = performance.now() - t0;
    if (r.events.length !== 11) throw new Error(`OR ${N}: ${r.events.length} events`);
    // warm: chained tick over the live State — scheduler cache hits
    const t1 = performance.now();
    const r2 = calc.settle(r.state, '20', { ...settleOpts, raw: true });
    const warm = performance.now() - t1;
    if (r2.events.length !== 10) throw new Error(`OR ${N} warm: ${r2.events.length} events`);
    rows.push([N, cold, warm, loadMs]);
    if (cold > 20000 || loadMs > 60000) break;
  }
  report('OR-rules', rows, ['#rules', 'cold ms', 'warm ms', 'load ms']);
}

// ── OF: live-cohort scaling ─────────────────────────────────────────
// N distinct-stamp cohorts of an INERT token on stage + one active rule.
// Per-event cost should not scale with the inert population.
if (run('OF')) {
  const src = `m: type.\na: type.\njunk: type.
p: $m -o { a }@1.\n`;
  const file = path.join(os.tmpdir(), 'till-of.till');
  fs.writeFileSync(file, src);
  const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const tcfg = calc.timedConfig;
  const rows = [];
  for (const N of [10, 100, 1000, 10000, 100000, 1000000]) {
    const linear = { [atom('m')]: 1 };
    for (let i = 0; i < N; i++) {
      linear[Store.put('at', [atom('junk'), tcfg.parseStamp(String(i))])] = 1;
    }
    const st = { linear, persistent: {} };
    const t0 = performance.now();
    const r = calc.settle(st, '10', { ...settleOpts, raw: true });
    const cold = performance.now() - t0;
    if (r.events.length !== 11) throw new Error(`OF ${N}: ${r.events.length} events`);
    // warm: incremental re-settle over the live State (10 more firings)
    const t1 = performance.now();
    const r2 = calc.settle(r.state, '20', { ...settleOpts, raw: true });
    const warm = performance.now() - t1;
    if (r2.events.length !== 10) throw new Error(`OF ${N} warm: ${r2.events.length} events`);
    rows.push([N, cold, warm]);
    if (cold > 20000) break;
  }
  report('OF-cohorts', rows, ['#cohorts', 'cold ms', 'warm ms']);
}

// ── OT: deep-time jump ──────────────────────────────────────────────
// Small periodic economy settled straight from 0 to T. Without loop
// acceleration this is O(#events) = O(T); the 0277 target is O(1).
if (run('OT')) {
  const calc = mde.load(PP2, { calculusConfig: tillConfig, cache: false });
  const rows = [];
  for (const T of [10, 100, 1000, 10000, 100000, 1000000, 100000000]) {
    const st = { linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} };
    const t0 = performance.now();
    const r = calc.settle(st, String(T), { ...settleOpts, maxSteps: 10000000 });
    const ms = performance.now() - t0;
    const skipped = (r.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
    rows.push([T, ms, r.events.length, skipped, liveLinear(r.state)]);
    if (ms > 20000) break;
  }
  report('OT-deeptime', rows, ['T', 'settle ms', 'events', 'skipped', 'linear']);
}

const jsonOut = opt('--json', null);
if (jsonOut) fs.writeFileSync(jsonOut, JSON.stringify(results, null, 2));
console.log('\ndone.');
