/**
 * will WFC demo + entropy chooser (TODO_0297 P1).
 *
 * Pins:
 *   - 'entropy' chooser (M5): H=0 candidates (deterministic consequents)
 *     fire before weighted draws; tighter distributions before wider;
 *     residual ties fall to the PRF path — and 'random' provably differs
 *   - game/WFC.will: the zero-engine-change collapse loop — every seed
 *     fully assembles the beach (4 tiles, no dom residue, no dom 0) and
 *     the sea–land adjacency constraint holds in every quiescent state
 *   - the collapse is genuinely stochastic across seeds (both sea-heavy
 *     and land-heavy beaches occur)
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import willConfig from '../../calculus/will/calculus-config.js';

const WFC = path.join(import.meta.dirname, '../../calculus/will/game/WFC.will');
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-wfc-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

const atom = (n) => Store.put('atom', [n]);
const bin = (n) => Store.put1('binlit', n);

/** Decode a settled linear state into [{pred, args(names)}] (stamp-blind). */
function facts(state) {
  const out = [];
  for (const [hStr, c] of Object.entries(state.linear)) {
    let h = Number(hStr);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    const tag = Store.tag(h);
    const args = [];
    for (let i = 0; i < Store.arity(h); i++) {
      const a = Store.child(h, i);
      args.push(Store.tag(a) === 'atom' ? Store.child(a, 0) : Store.tag(a));
    }
    for (let k = 0; k < c; k++) out.push({ pred: tag, args });
  }
  return out;
}

describe("entropy chooser (M5) — least-uncertain candidate first", () => {
  const PROG = `
s1: type.
s2: type.
s3: type.
p: type.
u: type.
v: type.
x: type.
y: type.
det:  s1 -o { p }.
wide: s2 -o { x +[1/2] y }.
tight: s3 -o { u +[1/10] v }.
`;
  let calc;
  before(() => {
    const f = path.join(tmp, 'entropy.will');
    fs.writeFileSync(f, PROG);
    calc = mde.load(f, { calculusConfig: willConfig, cache: false });
  });
  const initial = () => ({
    linear: { [atom('s1')]: 1, [atom('s2')]: 1, [atom('s3')]: 1 },
    persistent: {},
  });

  it('orders det < tight < wide for every seed', () => {
    for (const seed of [0, 1, 7, 42, 1234]) {
      const res = calc.settle(initial(), 0, { seed, keepEvents: true });
      assert.deepEqual(res.events.map((e) => e.rule), ['det', 'tight', 'wide'], `seed ${seed}`);
    }
  });

  it("'random' differs from 'entropy' on some seed (the policy is real)", () => {
    const differs = [...Array(32).keys()].some((seed) => {
      const res = calc.settle(initial(), 0, { seed, chooser: 'random', keepEvents: true });
      return res.events.map((e) => e.rule).join() !== 'det,tight,wide';
    });
    assert.ok(differs, 'random chooser never deviated in 32 seeds — entropy test is vacuous');
  });
});

describe('WFC.will — the ∃_ρ + bias surface assembles a valid beach (TODO_0298)', () => {
  let calc;
  before(() => {
    calc = mde.load(WFC, { calculusConfig: willConfig, cache: false });
  });
  const CELLS = ['c0', 'c1', 'c2', 'c3'];
  const initial = () => {
    const linear = {};
    for (const c of CELLS) linear[Store.put('mk', [atom(c)])] = 1;
    for (let i = 0; i < 3; i++) {
      linear[Store.put('guard', [atom(CELLS[i]), atom(CELLS[i + 1])])] = 1;
      linear[Store.put('guard', [atom(CELLS[i + 1]), atom(CELLS[i])])] = 1;
    }
    return { linear, persistent: {} };
  };

  it('plain settle only suspends (D4): four waves, no ground tile', () => {
    const res = calc.settle(initial(), 0, { maxSteps: 100 });
    assert.ok(res.quiescent);
    const fs_ = facts(res.state);
    assert.equal(fs_.filter((f) => f.pred === 'superpose').length, 4);
    assert.equal(fs_.filter((f) => f.pred === 'tile').length, 0);
  });

  it('every seed: ground, no restarts (arc-consistent), constraint holds, all tiles occur', () => {
    const seen = new Set();
    for (let seed = 0; seed < 40; seed++) {
      const r = calc.collapse(initial(), { seed });
      assert.ok(r.ground, `seed ${seed}: not ground`);
      assert.equal(r.attempts, 0, `seed ${seed}: restarted on an arc-consistent set`);
      assert.equal(r.collapses.length, 4, `seed ${seed}: expected 4 draws`);
      const byCell = {};
      for (const f of facts(r.state)) if (f.pred === 'tile') byCell[f.args[0]] = f.args[1];
      assert.deepEqual(Object.keys(byCell).sort(), CELLS, `seed ${seed}: one tile per cell`);
      for (let i = 0; i < 3; i++) {
        const pair = [byCell[CELLS[i]], byCell[CELLS[i + 1]]].sort().join('-');
        assert.notEqual(pair, 'land-sea', `seed ${seed}: sea–land adjacent (${CELLS[i]})`);
      }
      seen.add(CELLS.map((c) => byCell[c]).join(','));
    }
    assert.ok(seen.size > 3, `only ${seen.size} distinct beaches in 40 seeds`);
    const all = [...seen].join(';');
    assert.ok(all.includes('sea') && all.includes('land') && all.includes('coast'),
      'across seeds all three tiles should occur');
  });

  it('propagation shows in the posteriors: bias-pruned draws (total 3) occur across seeds', () => {
    // bias-free wave total = 2+1+2 = 5; a pruned neighbor totals 3
    let sawPruned = false;
    for (let seed = 0; seed < 12 && !sawPruned; seed++) {
      const r = calc.collapse(initial(), { seed });
      if (r.collapses.some((c) => c.total[0] === 3n && c.total[1] === 1n)) sawPruned = true;
    }
    assert.ok(sawPruned, 'no sampled run ever drew from a pruned posterior');
  });

  it('stepwise (shell face): forcing c0 = sea prunes land from c1', () => {
    const session = { state: initial(), waveMap: new Map(), skolemSet: new Set() };
    let waves = calc.collapseView(session);
    assert.equal(waves.length, 4);
    const cellOf = (w) => {
      for (const k of Object.keys(session.state.linear)) {
        let h = Number(k);
        if (Store.tag(h) === 'at') h = Store.child(h, 0);
        if (Store.tag(h) === 'tile' && Store.child(h, 1) === w.e) {
          return Store.child(Store.child(h, 0), 0);
        }
      }
      return null;
    };
    const w0 = waves.find((w) => cellOf(w) === 'c0');
    const rec = calc.collapseDraw(session, w0, { member: 'sea' });
    assert.equal(rec.member, 'sea');
    assert.deepEqual(rec.weight, [2n, 1n]);
    waves = calc.collapseView(session);                  // re-settles: constrain fires
    const w1 = waves.find((w) => cellOf(w) === 'c1');
    const { members, weights, total } = w1.posterior;
    assert.equal(weights[members.indexOf('land')][0], 0n, 'land must be bias-pruned');
    assert.deepEqual(total, [3n, 1n]);
    // the pruned wave now sorts FIRST (min entropy — the driver's pick)
    assert.equal(cellOf(waves[0]), 'c1');
  });

  it('exact mode realizes the constrained measure: no forbidden beach has mass', () => {
    const r = calc.collapse(initial(), { mode: 'exact' });
    for (const o of r.outcomes) {
      const byCell = {};
      for (const f of facts(o.state)) if (f.pred === 'tile') byCell[f.args[0]] = f.args[1];
      for (let i = 0; i < 3; i++) {
        const pair = [byCell[CELLS[i]], byCell[CELLS[i + 1]]].sort().join('-');
        assert.notEqual(pair, 'land-sea', 'forbidden beach carries mass');
      }
    }
    // T1 sanity: some mass survives and less than the unconstrained 5⁴
    assert.ok(r.total[0] > 0n);
    assert.ok(r.total[0] < 625n * r.total[1]);
  });
});

describe('D16 strict-measure refinement (TODO_0298) — measured self-loops are not Zeno', () => {
  const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');
  const load = (name, src) => {
    const f = path.join(tmp, name);
    fs.writeFileSync(f, `#import(${MEASURE})\n` + src);
    return mde.load(f, { calculusConfig: willConfig, cache: false });
  };

  it('the bit-test idiom (div/mod/eq + qsub of the set bit) silences the advisory', () => {
    // the old WFC propagation shape, kept as the D16 bit-test pin
    const calc = load('bittest.will', `
dm: (m: q) -> type.
bt: (b: q) -> type.
prop: dm M * $bt B * !div M B Q * !mod Q 2 R * !eq R 1 * !qsub M B M' -o { dm M' }.
`);
    assert.deepEqual(calc.timedLint, []);
  });

  it('the modernized WFC loads with no advisory', () => {
    const calc = mde.load(WFC, { calculusConfig: willConfig, cache: false });
    assert.deepEqual(calc.timedLint, []);
    assert.ok(!calc.timedAdvice.some((a) => a.kind === 'persistent-conclusion'),
      'the bias machinery predicate must be Hypothesis-S exempt');
  });

  it('a ground positive decrement silences the advisory; an identity re-produce still flags', () => {
    const measured = load('measured.will', `
ctr: (n: q) -> type.
dec: ctr N * !qsub N 1 N' -o { ctr N' }.
`);
    assert.deepEqual(measured.timedLint, []);
    const zeno = load('zeno.will', `
ctr: (n: q) -> type.
spin: ctr N -o { ctr N }.
`);
    assert.deepEqual(zeno.timedLint, [{ kind: 'self-cycle', rule: 'spin' }]);
  });

  it('a qsub by an UNEVIDENCED amount still flags (B could be 0)', () => {
    const calc = load('unevidenced.will', `
ctr: (n: q) -> type.
amt: (b: q) -> type.
dec: ctr N * $amt B * !qsub N B N' -o { ctr N' }.
`);
    assert.deepEqual(calc.timedLint, [{ kind: 'self-cycle', rule: 'dec' }]);
  });
});
