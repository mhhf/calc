/**
 * Certified conditional independence (T4-d(iii), THY_0031, TODO_0302).
 *
 * Numeric pins for the separation criterion's load-bearing design
 * decisions — each block computes exact conditioned masses via the
 * driver's 'exact' mode and checks the cross-product CI identity
 *   μ(x,y|·)·μ(x',y'|·) = μ(x,y'|·)·μ(x',y|·)
 * (division-free, zero-safe) by hand-verified rationals:
 *
 *   1. COLLIDER (D4): two waves feeding one fire are marginally
 *      independent; conditioning on the fire's output breaks it
 *      (explaining away) — d-separation's v-structure, verbatim.
 *   2. MASS-OBSERVED EXISTENCE (A2×A4): a wave whose existence depends
 *      on both sides leaks dependence through its TOTAL prior mass
 *      alone when the total ≠ 1 (unnormalized restriction semantics);
 *      the normalized twin (total = 1) is independent. Naive
 *      d-separation (blocked collider) is UNSOUND for will's measure
 *      without the mass-child discipline (THY_0031 §4).
 *   3. CONTEXT-SPECIFIC EDGE (D1): a bias rule enabled only in the
 *      X=va world makes Y dependent on X, while the X=vb run's
 *      certificate contains NO bias fire — separation must be read on
 *      the CLASS graph (static cover), never on one run's actual
 *      edges (THY_0031 §5, the LDAG lesson).
 *   4. CHAIN BLOCKING: X → M → Y through spawn-order + bias;
 *      conditioning on the mediator's value restores exact
 *      factorization in every context, marginal dependence without.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import willConfig from '../../calculus/will/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-ci-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

const HEADER = `#import(${MEASURE})
v: sort.
va: v @w 1.
vb: v @w 2.
pos: sort.
x0: pos.
x1: pos.
x2: pos.
mk: (c: pos) -> type.
tile: (c: pos) -> (t: v) -> type.
bias: (x: v) -> (c: v) -> (w: q) -> type.
spawn: mk C -o { exists T: v @w. tile C T }.
`;

const loadProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const tileOf = (state, cell) => {
  for (const k of Object.keys(state.linear)) {
    let h = Number(k);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    if (Store.tag(h) === 'tile' && Store.child(Store.child(h, 0), 0) === cell) {
      const t = Store.child(h, 1);
      return Store.tag(t) === 'atom' ? Store.child(t, 0) : null; // evar → null
    }
  }
  return null;
};
const hasAtom = (state, name) => Object.keys(state.linear).map(Number)
  .some((h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h) === atom(name));

// exact rational helpers on [n, d] BigInt pairs
const ZERO = [0n, 1n];
const addF = ([a, b], [c, d]) => [a * d + c * b, b * d];
const mulF = ([a, b], [c, d]) => [a * c, b * d];
const eqF = ([a, b], [c, d]) => a * d === c * b;

/** Sum the masses of outcomes selected by `pick`. */
const massOf = (r, pick) =>
  r.outcomes.filter((o) => pick(o.state)).reduce((acc, o) => addF(acc, o.mass), ZERO);

/** The cross-product CI identity for two binary wave values. */
const factorizes = (m) => eqF(mulF(m.aa, m.bb), mulF(m.ab, m.ba));

const joint = (r, cellX, cellY, cond = () => true) => ({
  aa: massOf(r, (s) => cond(s) && tileOf(s, cellX) === 'va' && tileOf(s, cellY) === 'va'),
  ab: massOf(r, (s) => cond(s) && tileOf(s, cellX) === 'va' && tileOf(s, cellY) === 'vb'),
  ba: massOf(r, (s) => cond(s) && tileOf(s, cellX) === 'vb' && tileOf(s, cellY) === 'va'),
  bb: massOf(r, (s) => cond(s) && tileOf(s, cellX) === 'vb' && tileOf(s, cellY) === 'vb'),
});

describe('CI pin 1 — collider: marginal independence, explaining away (D4)', () => {
  const PROG = HEADER + `
chk: type.
matched: type.
req: chk * $tile x0 T * $tile x1 T -o { matched }.
`;
  const init = () => ({
    linear: {
      [Store.put('mk', [atom('x0')])]: 1,
      [Store.put('mk', [atom('x1')])]: 1,
      [atom('chk')]: 1,
    },
    persistent: {},
  });
  let r;
  before(() => { r = loadProg('ci-collider.will', PROG).collapse(init(), { mode: 'exact' }); });

  it('exact masses: 1/2/2/4, total 9', () => {
    assert.deepEqual(r.total, [9n, 1n]);
    const m = joint(r, 'x0', 'x1');
    assert.deepEqual([m.aa, m.ab, m.ba, m.bb], [[1n, 1n], [2n, 1n], [2n, 1n], [4n, 1n]]);
  });

  it('marginally independent: unconditioned collider is blocked', () => {
    assert.ok(factorizes(joint(r, 'x0', 'x1')));
  });

  it('conditioning on the collider output breaks independence (explaining away)', () => {
    const m = joint(r, 'x0', 'x1', (s) => hasAtom(s, 'matched'));
    assert.deepEqual(m.ab, ZERO);
    assert.deepEqual(m.ba, ZERO);
    assert.ok(!factorizes(m), 'X ⊥̸ Y | matched');
  });
});

describe('CI pin 2 — mass-observed existence (A2×A4): totals ≠ 1 leak dependence', () => {
  // W spawns only when X = Y; W is drawn and never used. With total
  // prior mass 2 on W's sort, the mere EXISTENCE of W multiplies the
  // run mass by 2 — X ⊥̸ Y although the collider (the spawn fire) is
  // unobserved and naive d-separation would call the path blocked.
  const SPAWNW = (wa, wb) => HEADER + `
w2: sort.
wc: w2 @w ${wa}.
wd: w2 @w ${wb}.
probe: (t: w2) -> type.
chk: type.
spw: chk * $tile x0 T * $tile x1 T -o { exists W: w2 @w. probe W }.
`;
  const init = () => ({
    linear: {
      [Store.put('mk', [atom('x0')])]: 1,
      [Store.put('mk', [atom('x1')])]: 1,
      [atom('chk')]: 1,
    },
    persistent: {},
  });

  it('unnormalized (total 2): dependence through existence alone', () => {
    const r = loadProg('ci-exist2.will', SPAWNW('1', '1')).collapse(init(), { mode: 'exact' });
    assert.deepEqual(r.total, [14n, 1n]);
    const m = joint(r, 'x0', 'x1');
    assert.deepEqual([m.aa, m.ab, m.ba, m.bb], [[2n, 1n], [2n, 1n], [2n, 1n], [8n, 1n]]);
    assert.ok(!factorizes(m), 'total mass 2 on the contingent wave leaks X ⊥̸ Y');
  });

  it('normalized twin (total 1): independence restored', () => {
    const r = loadProg('ci-exist1.will', SPAWNW('1/2', '1/2')).collapse(init(), { mode: 'exact' });
    assert.deepEqual(r.total, [9n, 1n]);
    assert.ok(factorizes(joint(r, 'x0', 'x1')));
  });
});

describe('CI pin 3 — context-specific edge (D1): one run’s certificate shows no edge', () => {
  // Y spawns only after X grounds (per-member rules); the bias fire
  // exists only in the X=va world. Dependence is real, yet every X=vb
  // run's certificate contains no bias fire — separation must be read
  // on the class graph, not on one run's actual edges.
  const PROG = HEADER + `
mky: type.
gb: type.
sya: mky * $tile x0 va -o { exists U: v @w. tile x1 U }.
syb: mky * $tile x0 vb -o { exists U: v @w. tile x1 U }.
ba: gb * $tile x0 va * $tile x1 E -o { !bias E va 3 }.
`;
  const init = () => ({
    linear: {
      [Store.put('mk', [atom('x0')])]: 1,
      [atom('mky')]: 1,
      [atom('gb')]: 1,
    },
    persistent: {},
  });
  let calc;
  before(() => { calc = loadProg('ci-ctx.will', PROG); });

  it('exact masses 3/2/2/4 (bias 3 lands only in the va world): dependent', () => {
    const r = calc.collapse(init(), { mode: 'exact', settleBranching: 'seed' });
    assert.deepEqual(r.total, [11n, 1n]);
    const m = joint(r, 'x0', 'x1');
    assert.deepEqual([m.aa, m.ab, m.ba, m.bb], [[3n, 1n], [2n, 1n], [2n, 1n], [4n, 1n]]);
    assert.ok(!factorizes(m), 'X ⊥̸ Y — the context-specific bias edge is live');
  });

  it('an X=vb run fires no bias rule; an X=va run does (certificate asymmetry)', () => {
    const firesOf = (run) => run.trace.filter((t) => t.settle)
      .flatMap((t) => t.settle.map((ev) => ev.rule));
    let sawVa = false;
    let sawVb = false;
    for (let seed = 0; seed < 40 && !(sawVa && sawVb); seed++) {
      const run = calc.collapse(init(), { seed, trace: true });
      assert.ok(run.ground, `seed ${seed}`);
      const fires = firesOf(run);
      if (tileOf(run.state, 'x0') === 'va') {
        assert.ok(fires.some((n) => /^ba/.test(n)), `seed ${seed}: va world must bias`);
        sawVa = true;
      } else {
        assert.ok(!fires.some((n) => /^ba/.test(n)), `seed ${seed}: vb world must not bias`);
        sawVb = true;
      }
    }
    assert.ok(sawVa && sawVb, 'both worlds sampled');
  });
});

describe('CI pin 4 — chain X → M → Y: mediator conditioning blocks', () => {
  const PROG = HEADER + `
mkm: type.
mky: type.
t1: type.
t2: type.
sma: mkm * $tile x0 va -o { exists U: v @w. tile x1 U }.
smb: mkm * $tile x0 vb -o { exists U: v @w. tile x1 U }.
bm: t1 * $tile x0 va * $tile x1 E -o { !bias E va 4 }.
sya: mky * $tile x1 va -o { exists W: v @w. tile x2 W }.
syb: mky * $tile x1 vb -o { exists W: v @w. tile x2 W }.
by: t2 * $tile x1 va * $tile x2 E -o { !bias E vb 5 }.
`;
  const init = () => ({
    linear: {
      [Store.put('mk', [atom('x0')])]: 1,
      [atom('mkm')]: 1,
      [atom('mky')]: 1,
      [atom('t1')]: 1,
      [atom('t2')]: 1,
    },
    persistent: {},
  });
  let r;
  before(() => {
    r = loadProg('ci-chain.will', PROG).collapse(init(), { mode: 'exact', settleBranching: 'seed' });
  });

  it('exact joint over (X, M, Y): total 84, hand-verified masses', () => {
    assert.deepEqual(r.total, [84n, 1n]);
    const cell = (x, m, y) => massOf(r, (s) =>
      tileOf(s, 'x0') === x && tileOf(s, 'x1') === m && tileOf(s, 'x2') === y);
    assert.deepEqual(cell('va', 'va', 'vb'), [40n, 1n]); // 1·4·10
    assert.deepEqual(cell('vb', 'vb', 'vb'), [8n, 1n]);  // 2·2·2
  });

  it('X ⊥ Y | M = m for both m (chain blocked at the conditioned mediator)', () => {
    for (const m of ['va', 'vb']) {
      assert.ok(factorizes(joint(r, 'x0', 'x2', (s) => tileOf(s, 'x1') === m)),
        `X ⊥ Y | M=${m}`);
    }
  });

  it('X ⊥̸ Y marginally (active chain through the unobserved mediator)', () => {
    assert.ok(!factorizes(joint(r, 'x0', 'x2')));
  });
});
