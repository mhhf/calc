/**
 * will decimation benchmark — audit 2026-09-02.
 *
 * First perf tracking for the ∃_ρ surface: the collapse driver
 * (sample/exact), lazy-PCFG recursive draws, load-time inside-mass
 * solving (datasort-mass.js Gaussian elimination), and schema expansion
 * had no numbers at all. Future regressions in decimate.js/sorts.js are
 * invisible without this gate.
 *
 *   load-datasorts    load lst/even/odd program incl. exact mass solve
 *   load-schema       load with a 24-member classifier × 2 schema rules
 *   collapse-grid     12-wave finite sample collapse (one seed sweep)
 *   collapse-exact    exact enumeration over 4 finite waves (3^4 worlds)
 *   collapse-rec      recursive `exists X: even @w.` sample draws (lazy PCFG)
 *
 * Usage: bun benchmarks/engine/will-decimate-bench.js  (or node)
 */

import fs from 'fs';
import os from 'os';
import path from 'path';
import { performance } from 'perf_hooks';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import willConfig from '../../calculus/will/calculus-config.js';

const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-bench-'));
process.on('exit', () => fs.rmSync(tmp, { recursive: true, force: true }));
const atom = (n) => Store.put('atom', [n]);

const writeProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return f;
};
const loadProg = (f) => mde.load(f, { calculusConfig: willConfig, cache: false });

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
  console.log(`${name.padEnd(16)} ${mean.toFixed(2).padStart(8)} ms/op  (min ${times[0].toFixed(2)}, n=${iters})`);
  return mean;
}

// ── load-datasorts: the B8 worked example — mass solve at load ──────
const REC = writeProg('rec.will', `#import(${MEASURE})
bit: sort.
b0: bit @w 1.
b1: bit @w 1.
lst: sort.
nil: lst @w 2.
cons: (h: bit) -> (t: lst) -> lst @w 1/4.
even <: lst.
odd <: lst.
even/n: even nil.
even/c: even (cons H T) <- odd T.
odd/c: odd (cons H T) <- even T.
mk: type.
box: (x: lst) -> type.
spawn: mk -o { exists X: even @w. box X }.
`);
bench('load-datasorts', 20, () => {
  const calc = loadProg(REC);
  if (!calc.masses || calc.masses.get('even')[0] !== 8n) throw new Error('mass solve wrong');
});

// ── load-schema: 24-member classifier × 2 schema rules ──────────────
const members = Array.from({ length: 24 }, (_, i) => `t${i}: tile_t @w ${(i % 3) + 1}.`).join('\n');
const SCHEMA = writeProg('schema.will', `#import(${MEASURE})
tile_t: sort.
${members}
have: (t: tile_t) -> type.
seen: (t: tile_t) -> type.
gone: (t: tile_t) -> type.
s1: (t: tile_t) have t -o { seen t }.
s2: (t: tile_t) seen t -o { gone t }.
`);
bench('load-schema', 20, () => {
  const calc = loadProg(SCHEMA);
  if (calc.forwardRules.length < 48) throw new Error(`schema: ${calc.forwardRules.length} rules, want 48`);
});

// ── collapse-grid: 12 finite waves, sample mode ─────────────────────
const cells = Array.from({ length: 12 }, (_, i) => `c${i}: pos2.`).join('\n');
const GRID = loadProg(writeProg('grid.will', `#import(${MEASURE})
pos2: sort.
${cells}
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
mk: (c: pos2) -> type.
tile: (c: pos2) -> (t: tile_t) -> type.
spawn: mk C -o { exists T: tile_t @w. tile C T }.
`));
const gridInit = () => {
  const linear = {};
  for (let i = 0; i < 12; i++) linear[Store.put('mk', [atom(`c${i}`)])] = 1;
  return { linear, persistent: {} };
};
bench('collapse-grid', 30, () => {
  for (let seed = 0; seed < 4; seed++) {
    const r = GRID.collapse(gridInit(), { seed });
    if (!r.ground) throw new Error('grid: not ground');
  }
});

// ── collapse-exact: 4 finite waves, full enumeration (3^4 worlds) ───
const gridInit4 = () => {
  const linear = {};
  for (let i = 0; i < 4; i++) linear[Store.put('mk', [atom(`c${i}`)])] = 1;
  return { linear, persistent: {} };
};
bench('collapse-exact', 30, () => {
  const r = GRID.collapse(gridInit4(), { mode: 'exact' });
  if (r.outcomes.length !== 81) throw new Error(`exact: ${r.outcomes.length} worlds, want 81`);
});

// ── collapse-rec: recursive conditioned draws (lazy PCFG) ───────────
const RECC = loadProg(REC);
bench('collapse-rec', 30, () => {
  for (let seed = 0; seed < 8; seed++) {
    const r = RECC.collapse({ linear: { [atom('mk')]: 1 }, persistent: {} }, { seed });
    if (!r.ground) throw new Error('rec: not ground');
  }
});
