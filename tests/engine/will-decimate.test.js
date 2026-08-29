/**
 * Decimation driver (TODO_0297 P2; 0292 L3/M4/M8/M9, THY_0026 T1/T3).
 *
 * Pins:
 *   - suspended ∃-facts open into evar waves; wave sorts resolve from
 *     signature positions; plain settle leaves them inert (D4 opt-in)
 *   - 'exact' realizes the measure: outcomes carry exact unnormalized
 *     masses, Σ = product of domain totals (T1 mass conservation)
 *   - bias facts (M8) condition posteriors: forward-derived exclusion
 *     removes the outcome and its mass, symmetric rules make it
 *     order-independent; clause-derived bias rides the prover probe
 *   - contradiction (all-zero posterior) restarts 'sample' (M9) and
 *     kills the branch in 'exact'
 *   - importance accounting (T3): importance = Π posterior totals,
 *     E[importance] = total surviving mass
 *   - correlation: one binder over a tensor body collapses BOTH facts
 *     with the same witness
 *   - 'solve' returns a ground state deterministically
 *   - M7: supercritical priors hard-error without maxCollapses
 *   - substituteEvar re-hashes nested occurrences and merges counts
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import { collapse, substituteEvar } from '../../lib/engine/decimate.js';
import { freshEvar } from '../../lib/kernel/fresh.js';
import willConfig from '../../calculus/will/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-decimate-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

const HEADER = `#import(${MEASURE})
pos2: sort.
a0: pos2.
a1: pos2.
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
mk: (c: pos2) -> type.
tile: (c: pos2) -> (t: tile_t) -> type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> type.
spawn: mk C -o { exists T. tile C T }.
`;

const loadProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const init2 = () => ({
  linear: { [Store.put('mk', [atom('a0')])]: 1, [Store.put('mk', [atom('a1')])]: 1 },
  persistent: {},
});
const tileOf = (state, cell) => {
  for (const k of Object.keys(state.linear)) {
    let h = Number(k);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    if (Store.tag(h) === 'tile' && Store.child(Store.child(h, 0), 0) === cell) {
      return Store.child(Store.child(h, 1), 0);
    }
  }
  return null;
};
const q = ([n, d]) => Number(n) / Number(d);

describe('decimation driver — unbiased two-wave program', () => {
  let calc;
  before(() => { calc = loadProg('plain.will', HEADER); });

  it('plain settle leaves the suspended ∃-facts inert (D4)', () => {
    const res = calc.settle(init2(), 0, { maxSteps: 20 });
    assert.ok(res.quiescent);
    const tags = Object.keys(res.state.linear).map((k) => {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      return Store.tag(h);
    });
    assert.deepEqual(tags.sort(), ['exists', 'exists']);
  });

  it("'exact': 9 outcomes, exact masses, total 25 (T1)", () => {
    const r = calc.collapse(init2(), { mode: 'exact' });
    assert.equal(r.outcomes.length, 9);
    assert.deepEqual(r.total, [25n, 1n]);
    const seaSea = r.outcomes.find((o) => tileOf(o.state, 'a0') === 'sea' && tileOf(o.state, 'a1') === 'sea');
    assert.deepEqual(seaSea.mass, [4n, 1n]);
  });

  it("'sample': ground states, importance = 25 exactly, 2:1:2 marginals", () => {
    const tally = { sea: 0, coast: 0, land: 0 };
    for (let seed = 0; seed < 120; seed++) {
      const r = calc.collapse(init2(), { seed });
      assert.ok(r.ground);
      assert.deepEqual(r.importance, [25n, 1n]);
      assert.equal(r.collapses.length, 2);
      tally[tileOf(r.state, 'a0')]++;
      tally[tileOf(r.state, 'a1')]++;
    }
    assert.ok(tally.sea > 60 && tally.land > 60 && tally.coast > 20 && tally.coast < 80,
      `marginals off: ${JSON.stringify(tally)}`);
  });

  it("'solve': deterministic ground state", () => {
    const a = calc.collapse(init2(), { mode: 'solve' });
    const b = calc.collapse(init2(), { mode: 'solve' });
    assert.ok(a.ground && b.ground);
    assert.equal(tileOf(a.state, 'a0'), tileOf(b.state, 'a0'));
    assert.equal(tileOf(a.state, 'a1'), tileOf(b.state, 'a1'));
  });
});

describe('bias conditioning (M8) — forward-derived, order-independent', () => {
  // Symmetric watch rules: whichever cell collapses to sea first biases
  // the OTHER wave against sea. Surviving mass 25 − 4 = 21 either order.
  const PROG = HEADER + `
watch1: type.
watch2: type.
nosea1: watch1 * $tile a0 sea * $tile a1 X -o { !bias X sea 0 }.
nosea2: watch2 * $tile a1 sea * $tile a0 X -o { !bias X sea 0 }.
`;
  const init = () => {
    const s = init2();
    s.linear[atom('watch1')] = 1;
    s.linear[atom('watch2')] = 1;
    return s;
  };
  let calc;
  before(() => { calc = loadProg('bias.will', PROG); });

  it("'exact': (sea,sea) excluded, total mass 21", () => {
    const r = calc.collapse(init(), { mode: 'exact' });
    assert.deepEqual(r.total, [21n, 1n]);
    assert.ok(!r.outcomes.some((o) => tileOf(o.state, 'a0') === 'sea' && tileOf(o.state, 'a1') === 'sea'));
    assert.equal(r.outcomes.length, 8);
  });

  it("'sample': never (sea,sea); E[importance] ≈ 21 (T3)", () => {
    let sum = 0;
    const N = 200;
    for (let seed = 0; seed < N; seed++) {
      const r = calc.collapse(init(), { seed });
      assert.ok(!(tileOf(r.state, 'a0') === 'sea' && tileOf(r.state, 'a1') === 'sea'), `seed ${seed}`);
      // per-run consistency: importance = Π totals of the collapse log
      const prod = r.collapses.reduce((acc, c) => acc * q(c.total), 1);
      assert.ok(Math.abs(q(r.importance) - prod) < 1e-9);
      sum += q(r.importance);
    }
    const mean = sum / N;
    assert.ok(mean > 19 && mean < 23, `E[importance] = ${mean}, want ≈ 21`);
  });
});

describe('contradiction → restart (M9) / dead branch (exact)', () => {
  // Whichever cell hits sea first kills the other wave entirely.
  const PROG = HEADER + `
watch1: type.
watch2: type.
kill1: watch1 * $tile a0 sea * $tile a1 X -o { !bias X sea 0 * !bias X coast 0 * !bias X land 0 }.
kill2: watch2 * $tile a1 sea * $tile a0 X -o { !bias X sea 0 * !bias X coast 0 * !bias X land 0 }.
`;
  const init = () => {
    const s = init2();
    s.linear[atom('watch1')] = 1;
    s.linear[atom('watch2')] = 1;
    return s;
  };
  let calc;
  before(() => { calc = loadProg('kill.will', PROG); });

  it("'exact': the first-drawn-sea branch is dead — total 15", () => {
    const r = calc.collapse(init(), { mode: 'exact' });
    assert.deepEqual(r.total, [15n, 1n]);
  });

  it("'sample': restarts on contradiction and still grounds", () => {
    let restarted = 0;
    for (let seed = 0; seed < 60; seed++) {
      const r = calc.collapse(init(), { seed });
      assert.ok(r.ground, `seed ${seed}`);
      if (r.attempts > 0) restarted++;
    }
    assert.ok(restarted > 0, 'no seed ever restarted — contradiction path untested');
  });
});

describe('clause-derived bias (prover probe)', () => {
  const PROG = HEADER + `
bias/nocoast: bias X coast 0.
`;
  it("'exact': coast clause-pruned from every wave — total 16", () => {
    const calc = loadProg('clausebias.will', PROG);
    const r = calc.collapse(init2(), { mode: 'exact' });
    assert.deepEqual(r.total, [16n, 1n]);          // (2+2)²
    assert.ok(!r.outcomes.some((o) => tileOf(o.state, 'a0') === 'coast' || tileOf(o.state, 'a1') === 'coast'));
  });
});

describe('correlation — one binder over a tensor body', () => {
  const PROG = HEADER + `
mark: (t: tile_t) -> type.
mk2: (c: pos2) -> type.
spawn2: mk2 C -o { exists T. (tile C T * mark T) }.
`;
  it('both conjuncts collapse to the SAME witness', () => {
    const calc = loadProg('corr.will', PROG);
    const init = { linear: { [Store.put('mk2', [atom('a0')])]: 1 }, persistent: {} };
    for (const seed of [0, 1, 2, 3, 4]) {
      const r = calc.collapse(init, { seed });
      assert.ok(r.ground);
      assert.equal(r.collapses.length, 1, 'one wave, one draw');
      const t = tileOf(r.state, 'a0');
      const marks = Object.keys(r.state.linear).map(Number)
        .map((h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h))
        .filter((h) => Store.tag(h) === 'mark')
        .map((h) => Store.child(Store.child(h, 0), 0));
      assert.deepEqual(marks, [t], `mark must carry the tile's witness (seed ${seed})`);
    }
  });
});

describe('guards', () => {
  it('M7: supercritical priors hard-error without maxCollapses', () => {
    const calc = loadProg('m7.will', HEADER);
    const fake = { ...calc, priorLint: [{ kind: 'supercritical-prior', sort: 'x', m: 2 }] };
    assert.throws(() => collapse(fake, init2(), { stampTag: 'at' }), /supercritical|depth bound/);
    const ok = collapse(fake, init2(), { stampTag: 'at', maxCollapses: 50 });
    assert.ok(ok.ground);
  });

  it('substituteEvar: nested re-hash, count merge', () => {
    const e = freshEvar();
    const f1 = Store.put('tile', [atom('a0'), e]);
    const f2 = Store.put('tile', [atom('a0'), atom('sea')]);
    const state = { linear: { [f1]: 2, [f2]: 1 }, persistent: { [Store.put('bias', [e, atom('sea'), atom('x')])]: 1 } };
    const out = substituteEvar(state, e, atom('sea'));
    assert.equal(out.linear[f2], 3);               // merged 2 + 1
    assert.equal(Object.keys(out.linear).length, 1);
    const [pk] = Object.keys(out.persistent).map(Number);
    assert.equal(Store.child(pk, 0), atom('sea'));
  });
});
