#!/usr/bin/env node
/**
 * TODO_0216 Phase 0 H10 — per-put overhead probe
 *
 * Measures the wall-cost of adding a single `Uint8Array[index] = byte` write
 * to the Store.put hot path. Phase 1 (idea D — ground-bit) introduces exactly
 * such a side-table write per term insertion. If the overhead exceeds the
 * agreed budget (≤0.5%), Phase 1 must find a different representation.
 *
 * Methodology:
 *   • Baseline trial: N iterations of "put-like" work (object hash + dedupe
 *     Map lookup + typed-array arena append).
 *   • Probed trial: identical loop, plus one Uint8Array[i] = bit write.
 *   • Median of K trials each to tamp down GC noise.
 *
 * Writes doc/_scratch/0216-put-overhead.json and asserts the delta.
 *
 * Usage: node tools/0216-put-overhead.js
 */

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const OUT  = path.join(ROOT, 'doc/_scratch/0216-put-overhead.json');

const N        = 2_000_000;  // puts per trial
const TRIALS   = 7;
const BUDGET   = 0.005;      // 0.5% delta budget

// A hand-rolled put surrogate that mirrors the arithmetic of the real one:
// a key-hash compute + dedup Map check + an arena write. Does NOT allocate a
// real Store (we want to isolate the cost of the extra write).
function makeHarness({ withSideTable }) {
  const arena = new Uint32Array(N * 3);         // tag + 2 children per node
  const side  = withSideTable ? new Uint8Array(N) : null;
  const dedup = new Map();
  let next = 0;

  return function putLike(tag, a, b) {
    // Simulate hash compute.
    const k = (tag * 0x9E3779B1) ^ (a * 0x85EBCA77) ^ (b * 0xC2B2AE3D);
    const got = dedup.get(k);
    if (got !== undefined) return got;
    const idx = next++;
    arena[idx * 3]     = tag;
    arena[idx * 3 + 1] = a;
    arena[idx * 3 + 2] = b;
    if (side !== null) side[idx] = ((a | b) & 1);  // dead-code write
    dedup.set(k, idx);
    return idx;
  };
}

function runTrial(withSideTable) {
  const put = makeHarness({ withSideTable });
  // Warmup so V8 JITs the loop identically in both variants.
  for (let i = 0; i < 100_000; i++) put(i & 7, i, i + 1);

  const t0 = process.hrtime.bigint();
  // Use a pattern with medium dedupe rate so the Map path is exercised.
  for (let i = 0; i < N; i++) {
    put(i & 31, i & 0xFFFFF, (i + 17) & 0xFFFFF);
  }
  const t1 = process.hrtime.bigint();
  return Number(t1 - t0) / 1e6;  // ms
}

function median(xs) {
  const s = xs.slice().sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
}

function main() {
  const base = [];
  const side = [];
  for (let t = 0; t < TRIALS; t++) {
    base.push(runTrial(false));
    side.push(runTrial(true));
  }
  const baseMedian = median(base);
  const sideMedian = median(side);
  const delta = (sideMedian - baseMedian) / baseMedian;

  const payload = {
    schema: '0216-put-overhead/v1',
    recorded: new Date().toISOString(),
    node: process.version,
    N, trials: TRIALS, budget: BUDGET,
    base_ms: base,
    side_ms: side,
    base_median_ms: baseMedian,
    side_median_ms: sideMedian,
    delta_frac: delta,
    within_budget: delta <= BUDGET,
  };
  fs.mkdirSync(path.dirname(OUT), { recursive: true });
  fs.writeFileSync(OUT, JSON.stringify(payload, null, 2));
  console.log(`Wrote ${OUT}`);
  console.log(`base median: ${baseMedian.toFixed(3)} ms`);
  console.log(`side median: ${sideMedian.toFixed(3)} ms`);
  console.log(`delta: ${(delta * 100).toFixed(3)}% (budget ≤${(BUDGET * 100).toFixed(2)}%)`);
  if (delta > BUDGET) {
    console.error('OVER BUDGET — Phase 1 ground-bit side-table is too expensive.');
    process.exit(1);
  }
  console.log('OK');
}

main();
