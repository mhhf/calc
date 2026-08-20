/**
 * till scheduler benchmark — TODO_0265 Phase 5.
 *
 * First perf tracking for the timed matcher: tryTimedMatch is exponential
 * in coupled patterns (per-rule branch-and-bound over cohort assignments),
 * and settle/settleExplore had no numbers at all. These four scenarios are
 * the gate for the Phase-7 "fingerprint/strategy theory-awareness" item —
 * measure before optimizing.
 *
 *   economy      10/10/10 time.mjs scenario settled to T=1 (7 firings)
 *   economy-XL   100/100/100 settled to T=10 (~150 firings, deep schedule)
 *   duel         8v8 weighted duel to quiescence (woplus PRF draws)
 *   duel-explore 3v3 exhaustive settleExplore (weighted tree, ~100+ leaves)
 *   coupled      x*y over 24×24 distinct-stamp cohorts (B&B match stress)
 *
 * Usage: bun benchmarks/engine/till-bench.js  (or node)
 */

import path from 'path';
import { performance } from 'perf_hooks';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { putRat } from '../../lib/kernel/rat-term.js';

const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
const FIX = (f) => path.join(import.meta.dirname, '../../tests/fixtures', f);
const atom = (n) => Store.put('atom', [n]);

function bench(name, iters, fn) {
  fn();                                          // warmup + correctness
  const times = [];
  for (let i = 0; i < iters; i++) {
    const t0 = performance.now();
    fn();
    times.push(performance.now() - t0);
  }
  times.sort((a, b) => a - b);
  const mean = times.reduce((s, t) => s + t, 0) / times.length;
  console.log(`${name.padEnd(14)} ${mean.toFixed(2).padStart(8)} ms/op  (min ${times[0].toFixed(2)}, n=${iters})`);
  return mean;
}

// ── economy: the acceptance scenario, small and scaled ──────────────
const economy = mde.load(SPEC('economy.ill'), { calculusConfig: tillConfig, cache: false });
const econSmall = convert.decomposeQuery(economy.splitQueries.get('expect_economy').lhsHash);
bench('economy', 50, () => {
  const r = economy.settle(econSmall, '1');
  if (r.events.length !== 7) throw new Error(`economy: ${r.events.length} events, want 7`);
});

const econXL = { linear: {
  [atom('sawmill')]: 1, [atom('smith')]: 1,
  [atom('wood')]: 100, [atom('plank')]: 100, [atom('stone')]: 100,
}, persistent: {} };
bench('economy-XL', 10, () => {
  const r = economy.settle(econXL, '10');
  if (r.events.length < 50) throw new Error(`economy-XL: only ${r.events.length} events`);
});

// ── duel: weighted-choice PRF sampling to quiescence ────────────────
const duel = mde.load(FIX('till-duel.ill'), { calculusConfig: tillConfig, cache: false });
bench('duel', 50, () => {
  const r = duel.settle({ linear: { [atom('rock')]: 8, [atom('sci')]: 8 }, persistent: {} },
    '0', { seed: 42 });
  if (r.events.length < 8) throw new Error('duel: too few fights');
});

bench('duel-explore', 10, () => {
  const { leaves } = duel.settleExplore(
    { linear: { [atom('rock')]: 3, [atom('sci')]: 3 }, persistent: {} }, '0');
  if (leaves.length < 20) throw new Error(`duel-explore: ${leaves.length} leaves`);
});

// ── coupled patterns: B&B over 24×24 cohort assignments ─────────────
const coupled = mde.load(FIX('till-perm-a.ill'), { calculusConfig: tillConfig, cache: false });
// reuse serve: cust * bread -o { fed } — spread both inputs over 24 stamps
const coupledState = { linear: {}, persistent: {} };
for (let i = 1; i <= 24; i++) {
  coupledState.linear[Store.put('at', [atom('cust'), putRat(BigInt(i), 1n)])] = 1;
  coupledState.linear[Store.put('at', [atom('bread'), putRat(BigInt(i), 1n)])] = 1;
}
bench('coupled', 20, () => {
  const r = coupled.settle(coupledState, '24');
  if (r.events.length !== 24) throw new Error(`coupled: ${r.events.length} events, want 24`);
});
