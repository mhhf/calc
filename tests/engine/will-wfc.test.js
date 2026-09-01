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

describe('WFC.will — the collapse loop assembles a valid beach', () => {
  let calc;
  before(() => {
    calc = mde.load(WFC, { calculusConfig: willConfig, cache: false });
  });
  const initial = () => ({
    linear: {
      [Store.put('dom', [atom('c0'), bin(7n)])]: 1,
      [Store.put('dom', [atom('c1'), bin(7n)])]: 1,
      [Store.put('dom', [atom('c2'), bin(7n)])]: 1,
      [Store.put('dom', [atom('c3'), bin(7n)])]: 1,
    },
    persistent: {},
  });

  it('every seed: quiescent, fully collapsed, constraint holds', () => {
    const CELLS = ['c0', 'c1', 'c2', 'c3'];
    const seen = new Set();
    for (let seed = 0; seed < 40; seed++) {
      const res = calc.settle(initial(), 0, { seed, maxSteps: 500 });
      assert.ok(res.quiescent, `seed ${seed}: not quiescent`);
      const fs_ = facts(res.state);
      assert.ok(!fs_.some((f) => f.pred === 'dom'), `seed ${seed}: dom residue`);
      const tiles = fs_.filter((f) => f.pred === 'tile');
      assert.equal(tiles.length, 4, `seed ${seed}: expected 4 tiles`);
      const byCell = {};
      for (const t of tiles) byCell[t.args[0]] = t.args[1];
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

  it('decimation order: after a propagating collapse, the shrunk neighbor collapses before any full-domain cell', () => {
    for (const seed of [0, 3, 11, 29]) {
      const res = calc.settle(initial(), 0, { seed, maxSteps: 500, keepEvents: true });
      const ev = res.events.map((e) => e.rule);
      // Whenever a prop fired, some non-clp7 collapse must precede any
      // LATER clp7 (the shrunk domain has strictly lower entropy).
      const firstProp = ev.indexOf('prop');
      if (firstProp === -1) continue;
      const rest = ev.slice(firstProp + 1);
      const nextClp = rest.find((r) => r.startsWith('clp'));
      if (nextClp !== undefined) {
        assert.notEqual(nextClp, 'clp7',
          `seed ${seed}: full-domain cell collapsed before the shrunk neighbor (${ev.join(',')})`);
      }
    }
  });
});

describe('D16 strict-measure refinement (TODO_0298) — measured self-loops are not Zeno', () => {
  const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');
  const load = (name, src) => {
    const f = path.join(tmp, name);
    fs.writeFileSync(f, `#import(${MEASURE})\n` + src);
    return mde.load(f, { calculusConfig: willConfig, cache: false });
  };

  it("WFC's prop (bit-test + qsub) loads with no self-cycle advisory", () => {
    const calc = mde.load(WFC, { calculusConfig: willConfig, cache: false });
    assert.deepEqual(calc.timedLint, []);
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
