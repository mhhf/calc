/**
 * sill product stamps (TODO_0285 P6a) — the (time × dist) axis.
 *
 * One stamp carries both axes: componentwise tropical values, LEX total
 * order for the committed scheduler (time primary, dist tie-break),
 * Pareto frontier in the exploration layer (settleFrontier — dominance
 * derived from the join, a ⊑ b iff a ⊔ b = b). Scalar grades embed as
 * time-only and REIFY back to scalar terms (canonical collapse), so
 * till/gill surface programs ride in unchanged.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';
import os from 'os';
import Store from '../../lib/kernel/store.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import engine from '../../lib/engine/index.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { certifyRun } from '../../lib/prover/timed/elaborate-trace.js';
import sillConfig, { productGrades, loadSillSequent } from '../../calculus/sill/calculus-config.js';
import { tillCalculusConfig } from '../../calculus/till/calculus-config.js';

const v = productGrades.values;
const q = (n, d = 1) => [BigInt(n), BigInt(d)];
const pv = (tn, td, dn, dd) => [BigInt(tn), BigInt(td), BigInt(dn), BigInt(dd)];

const atom = (n) => Store.put('atom', [n]);
const at = (a, s) => Store.put('at', [a, s]);
const tpair = (t, d) => Store.put('tpair', [t, d]);

function loadTmp(source, config) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'sill-prod-'));
  const file = path.join(dir, 'p.sill');
  fs.writeFileSync(file, source);
  return engine.load(file, { calculusConfig: config, cache: false });
}

describe('productValues (pure algebra)', () => {
  it('cmp is LEX: time primary, dist tie-break, ∞ above finite', () => {
    assert.ok(v.cmp(pv(1, 1, 9, 1), pv(2, 1, 0, 1)) < 0, 'time decides');
    assert.ok(v.cmp(pv(2, 1, 1, 1), pv(2, 1, 3, 1)) < 0, 'dist breaks time ties');
    assert.equal(v.cmp(pv(2, 1, 3, 1), pv(2, 1, 3, 1)), 0);
    assert.ok(v.cmp(pv(2, 1, 1, 0), pv(2, 1, 999, 1)) > 0, 'inf dist above finite');
    assert.equal(v.cmp(pv(2, 1, 1, 0), pv(2, 1, 1, 0)), 0, 'inf == inf');
  });

  it('add and merge act componentwise (merge = join per axis)', () => {
    assert.deepEqual(v.add(pv(1, 1, 2, 1), pv(3, 1, 4, 1)), pv(4, 1, 6, 1));
    // lex max would pick (4,2) wholesale; componentwise join keeps dist 5
    assert.deepEqual(v.merge(pv(3, 1, 5, 1), pv(4, 1, 2, 1)), pv(4, 1, 5, 1));
  });

  it('reify collapses dist-0 to the scalar term; pairs round-trip', () => {
    assert.equal(v.reify(pv(6, 1, 0, 1)), putRat(6n, 1n));
    const p = v.reify(pv(6, 1, 2, 1));
    assert.equal(Store.tag(p), 'tpair');
    assert.deepEqual(v.parse(p), pv(6, 1, 2, 1));
    assert.deepEqual(v.parse(putRat(6n, 1n)), pv(6, 1, 0, 1));
  });

  it('parseStamp widens a scalar horizon to the down-set (T, ∞)', () => {
    const h = productGrades.parseStamp('5');
    const val = v.parse(h);
    assert.deepEqual([val[0], val[1]], q(5));
    assert.equal(val[3], 0n, 'dist half is ∞');
  });
});

describe('sill settle — product scheduling', () => {
  it('a product delay lands the fact at (t, d); scalar delays stay scalar', () => {
    const calc = loadTmp(`
g1: type.
g2: type.
r1: g1 -o { g2 }@(3 ~ 2).
r2: g2 -o { g1 }@4.
`, sillConfig);
    // horizon 2: r1 fires (activation (0,0)); r2's activation (3,2)
    // lies beyond (2,∞) — g2 survives with its pair stamp
    const r = calc.settle({ linear: { [atom('g1')]: 1 }, persistent: {} }, '2');
    assert.ok(r.quiescent);
    const key = at(atom('g2'), tpair(putRat(3n, 1n), putRat(2n, 1n)));
    assert.equal(r.state.linear[key], 1, 'g2 at (3 ~ 2)');
  });

  it('chained delays compose componentwise', () => {
    const calc = loadTmp(`
g1: type.
g2: type.
g3: type.
r1: g1 -o { g2 }@(3 ~ 2).
r2: g2 -o { g3 }@(1 ~ 4).
`, sillConfig);
    const r = calc.settle({ linear: { [atom('g1')]: 1 }, persistent: {} }, '10');
    const key = at(atom('g3'), tpair(putRat(4n, 1n), putRat(6n, 1n)));
    assert.equal(r.state.linear[key], 1, 'g3 at (4 ~ 6)');
  });

  it('multi-input activation joins componentwise (waits in time, carries dearest dist)', () => {
    const calc = loadTmp(`
a1: type.
b1: type.
c1: type.
join_r: a1 * b1 -o { c1 }@(1 ~ 1).
`, sillConfig);
    const init = {
      linear: {
        [at(atom('a1'), tpair(putRat(3n, 1n), putRat(5n, 1n)))]: 1,
        [at(atom('b1'), tpair(putRat(4n, 1n), putRat(2n, 1n)))]: 1,
      },
      persistent: {},
    };
    const r = calc.settle(init, '10');
    // activation = (max(3,4), max(5,2)) = (4, 5); done = (5, 6)
    const key = at(atom('c1'), tpair(putRat(5n, 1n), putRat(6n, 1n)));
    assert.equal(r.state.linear[key], 1, 'c1 at (5 ~ 6)');
  });

  it('B&B take-choice prefers the dist-cheaper cohort at equal time (lex tie-break)', () => {
    const calc = loadTmp(`
gg: type.
key1: type.
win: type.
take: key1 * gg -o { win }.
`, sillConfig);
    const init = {
      linear: {
        [atom('key1')]: 1,
        [at(atom('gg'), tpair(putRat(2n, 1n), putRat(5n, 1n)))]: 1,
        [at(atom('gg'), tpair(putRat(2n, 1n), putRat(1n, 1n)))]: 1,
      },
      persistent: {},
    };
    const r = calc.settle(init, '10');
    const win = at(atom('win'), tpair(putRat(2n, 1n), putRat(1n, 1n)));
    const leftover = at(atom('gg'), tpair(putRat(2n, 1n), putRat(5n, 1n)));
    assert.equal(r.state.linear[win], 1, 'win carries the cheap cohort stamp');
    assert.equal(r.state.linear[leftover], 1, 'dear cohort left behind');
  });

  it('a scalar horizon admits any dist at time ≤ T (down-set semantics)', () => {
    const calc = loadTmp(`
g1: type.
g2: type.
r1: g1 -o { g2 }@(5 ~ 99).
`, sillConfig);
    const r = calc.settle({ linear: { [atom('g1')]: 1 }, persistent: {} }, '5');
    // production at time 5 with dist 99: r1's ACTIVATION is (0,0) ≤ (5,∞);
    // the produced fact then sits beyond nothing — settle reaches it
    const key = at(atom('g2'), tpair(putRat(5n, 1n), putRat(99n, 1n)));
    assert.equal(r.state.linear[key], 1);
  });

  it('settleChunked keeps fact stamps finite (chunk is an extent, not a threshold)', () => {
    // parseStamp widens thresholds to (T, ∞); a chunk is a WIDTH and
    // must not widen — a widened chunk would absorb ∞ into every fact
    // stamp through the chunk accumulator (parseExtent, TODO_0285).
    const calc = loadTmp(`
g1: type.
g2: type.
r1: g1 -o { g2 }@(3 ~ 2).
`, sillConfig);
    const r = calc.settleChunked({ linear: { [atom('g1')]: 1 }, persistent: {} }, '4', { chunk: '2' });
    const key = at(atom('g2'), tpair(putRat(3n, 1n), putRat(2n, 1n)));
    assert.equal(r.state.linear[key], 1, 'g2 at (3 ~ 2), dist finite');
  });

  it('accelerate rejects the product algebra loudly', () => {
    const calc = loadTmp(`
g1: type.
r1: $g1 -o { g1 }@(1 ~ 1).
`, sillConfig);
    assert.throws(
      () => calc.settle({ linear: { [atom('g1')]: 1 }, persistent: {} }, '100', { accelerate: true }),
      /scale\/floorDiv|acceleration is unavailable/
    );
  });
});

describe('product-stamp certification (clause-only checker)', () => {
  it('certifyRun verifies a run whose activation is a componentwise join', () => {
    // r3's activation = (2,5) ⊔ (3,1) = (3,5) — attained by NO single
    // input: the fire-check attainment-by-membership shortcut would
    // reject it; the declared sjoin clauses (fire config join) derive it.
    const calc = loadTmp(`
a1: type.
a2: type.
bb: type.
cc: type.
dd: type.
r1: a1 -o { bb }@(2 ~ 5).
r2: a2 -o { cc }@(3 ~ 1).
r3: bb * cc -o { dd }@(1 ~ 1).
`, sillConfig);
    const seqCalc = loadSillSequent();
    const kernel = createKernel(seqCalc);
    const horizonTerm = Store.child(seqCalc.parse('x@10'), 1);
    const r = certifyRun({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: { linear: { [atom('a1')]: 1, [atom('a2')]: 1 }, persistent: {} },
      horizon: '10', horizonTerm,
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.events.length, 3);
  });

  it('certifyRun verifies a transport run (compound variable delay (T ~ D))', () => {
    // The delay is a compound term with antecedent-bound variables —
    // compiled as { term }, θ-substituted at fire, re-grounded by the
    // checker's bind map (P6b).
    const prelude = path.resolve(import.meta.dirname, '../../calculus/sill/prelude/spatial.sill');
    const calc = loadTmp(`#import(${prelude})
good: type.
delivered: type.
l00: place.
l01: place.
road: (a: place) -> (b: place) -> type.
dist: (a: place) -> (b: place) -> (t: delay) -> (d: dist) -> type.
transport: (good @@ L1) * road L1 L2 * !dist L1 L2 T D -o { (good @@ L2) }@(T ~ D).
deliver: (good @@ l01) -o { delivered }.
`, sillConfig);
    const seqCalc = loadSillSequent();
    const kernel = createKernel(seqCalc);
    const horizonTerm = Store.child(seqCalc.parse('x@10'), 1);
    const loc = (f, p) => Store.put('loc', [atom(f), atom(p)]);
    const r = certifyRun({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: {
        linear: {
          [loc('good', 'l00')]: 1,
          [Store.put('road', [atom('l00'), atom('l01')])]: 1,
        },
        persistent: {
          [Store.put('dist', [atom('l00'), atom('l01'), Store.put('binlit', [2n]), Store.put('binlit', [5n])])]: true,
        },
      },
      horizon: '10', horizonTerm,
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.events.length, 2, 'transport + deliver');
  });
});

describe('settleFrontier — Pareto-minimal completions', () => {
  it('returns the frontier (incomparable routes) and drops dominated ones', () => {
    const calc = loadTmp(`
tok: type.
goal: type.
fast: tok -o { goal }@(1 ~ 9).
cheap: tok -o { goal }@(9 ~ 1).
bad: tok -o { goal }@(10 ~ 10).
`, sillConfig);
    const r = calc.settleFrontier({ linear: { [atom('tok')]: 1 }, persistent: {} }, '20');
    assert.equal(r.leaves.length, 3, 'three chooser worlds');
    assert.equal(r.frontier.length, 2, 'fast and cheap are incomparable; bad is dominated');
    const costs = r.frontier.map((f) => f.cost).sort();
    const fastCost = tpair(putRat(1n, 1n), putRat(9n, 1n));
    const cheapCost = tpair(putRat(9n, 1n), putRat(1n, 1n));
    assert.deepEqual(costs, [fastCost, cheapCost].sort());
  });

  it('degenerates to the least completion for a scalar (total) algebra', () => {
    const calc = loadTmp(`
tok: type.
goal: type.
slow: tok -o { goal }@2.
quick: tok -o { goal }@1.
`, tillCalculusConfig);
    const r = calc.settleFrontier({ linear: { [atom('tok')]: 1 }, persistent: {} }, '10');
    assert.equal(r.leaves.length, 2);
    assert.equal(r.frontier.length, 1, 'total order: unique least completion');
    assert.equal(r.frontier[0].cost, putRat(1n, 1n));
  });
});
