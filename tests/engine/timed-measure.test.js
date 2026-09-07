/**
 * Trace measures — the usage-axis factorization (THY_0034,
 * settle-optimality §8.5).
 *
 * A conservation quantity (fuel, cost) is NEVER a stamp axis: stamp
 * values are cartesian (one `done` broadcast to every output, joined
 * over reads, re-emitted by $-catalysts — all duplication sites), while
 * conserved quantities are linear at the value level, so a
 * non-idempotent axis in the stamp slot double-counts. The
 * factorization routes each role to an existing slot; these pins
 * execute the two value-level ones on the fuel-transport domain:
 *
 *   accounting  → additive trace measure (opts.leafMeasure fold),
 *                 a function of the world's event multiset;
 *   gating      → fuel as linear tokens (counted takes) — conservation
 *                 enforced by linearity itself;
 *
 * and pin their EQUIVALENCE: the measure answer on the fuel-free
 * program equals the tokens-burned answer on the fuel-token program,
 * leaf by leaf. The (time, fuel) Pareto set lives over LEAVES (the
 * measure brings its own order); the stamp-only frontier filter
 * correctly drops nothing it shouldn't — and demonstrably DOES drop
 * the measure-better leaf, which is why dominance is never derived
 * from the stamp join for measures. Completeness of the leaf set is
 * CERTIFIED: the program is contended but tied (certifyContention's
 * tiedContention level), so by the adequacy proposition (§8.4) the
 * explore leaves are outcome-complete and the leaf Pareto set is the
 * TRUE (time, fuel) frontier.
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import mde from '../../lib/engine/index.js';
import { tillCalculusConfig } from '../../calculus/till/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'timed-measure-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const load = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: tillCalculusConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const at = (a, s) => Store.put('at', [a, s]);

// fast: 2 time units, 5 fuel; cheap: 9 time units, 1 fuel — tied
// contention on `start` at activation 0 (a genuine explore branch).
const ROUTES_MEASURE = `
start: type.
arrived: type.
fast: start -o { arrived }@2.
cheap: start -o { arrived }@9.
`;
const ROUTES_TOKENS = `
start: type.
fuel: type.
arrived: type.
fast: start * !_5 fuel -o { arrived }@2.
cheap: start * !_1 fuel -o { arrived }@9.
`;
const FUEL = { fast: 5n, cheap: 1n };
const fuelMeasure = { unit: 0n, step: (acc, m) => acc + (FUEL[m.rule.name] ?? 0n) };

const fuelLeft = (leafState) => {
  let left = 0;
  for (const k in leafState.linear) {
    const h = Number(k);
    const inner = Store.tag(h) === 'at' ? Store.child(h, 0) : h;
    if (inner === atom('fuel')) left += leafState.linear[k];
  }
  return left;
};

describe('trace measures — the usage-axis factorization (THY_0034)', () => {
  it('measure ≡ tokens: the factorization translation, leaf by leaf', () => {
    const M = load('routes-m.till', ROUTES_MEASURE);
    const rM = M.settleFrontier({ linear: { [atom('start')]: 1 }, persistent: {} }, '20',
      { leafMeasure: fuelMeasure });
    assert.equal(rM.leaves.length, 2, 'tied conflict — both worlds');
    const byStamp = (leaves, t) =>
      leaves.find((l) => l.state.linear[at(atom('arrived'), putRat(t, 1n))]);
    assert.equal(byStamp(rM.leaves, 2n).measure, 5n, 'fast world pays 5');
    assert.equal(byStamp(rM.leaves, 9n).measure, 1n, 'cheap world pays 1');

    const T = load('routes-t.till', ROUTES_TOKENS);
    const rT = T.settleFrontier(
      { linear: { [atom('start')]: 1, [atom('fuel')]: 5 }, persistent: {} }, '20');
    assert.equal(rT.leaves.length, 2);
    assert.equal(5 - fuelLeft(byStamp(rT.leaves, 2n).state), 5, 'fast burns 5 tokens');
    assert.equal(5 - fuelLeft(byStamp(rT.leaves, 9n).state), 1, 'cheap burns 1 token');
  });

  it('the (time, fuel) Pareto set lives over leaves; the stamp frontier drops the cheap world', () => {
    const M = load('routes-m2.till', ROUTES_MEASURE);
    const r = M.settleFrontier({ linear: { [atom('start')]: 1 }, persistent: {} }, '20',
      { leafMeasure: fuelMeasure });
    // stamp-only dominance: 2 < 9 totally, so only the fast leaf survives —
    // measure-better leaves are NOT protected (documented; measures bring
    // their own order, never derived from the stamp join)
    assert.equal(r.frontier.length, 1);
    assert.equal(r.frontier[0].cost, putRat(2n, 1n));
    assert.equal(r.frontier[0].measure, 5n);
    // the true (time, fuel) Pareto set over leaves: both incomparable
    const pairs = r.leaves.map((l) => ({
      t: l.state.linear[at(atom('arrived'), putRat(2n, 1n))] ? 2n : 9n,
      u: l.measure,
    }));
    const minimal = pairs.filter((p) => !pairs.some((q) =>
      q !== p && q.t <= p.t && q.u <= p.u && (q.t < p.t || q.u < p.u)));
    assert.equal(minimal.length, 2, 'fast and cheap are (time,fuel)-incomparable');
  });

  it('the leaf set is CERTIFIED complete: contended but tied (§8.4 adequacy)', () => {
    const M = load('routes-m3.till', ROUTES_MEASURE);
    const c = M.certifyContention({ linear: { [atom('start')]: 1 }, persistent: {} }, '20');
    assert.equal(c.certified, false, 'T2 refused — genuine contention on start');
    assert.equal(c.tiedContention, true, 'every dependent pair co-activated');
    assert.ok(c.contended.every((p) => p.coActivated));
  });

  it('a measure is a function of the world, not the schedule (settle fold ≡ explore fold)', () => {
    // tied INDEPENDENT pair: explore commits one order; settle's chooser
    // may order them either way per seed — the event multiset (hence any
    // trace measure) is seed-invariant, and equals explore's leaf measure.
    const P = load('indep.till', `
a: type. b: type. c: type. d: type.
p1: a -o { b }@1.
p2: c -o { d }@1.
`);
    const W = { p1: 7n, p2: 11n };
    const init = () => ({ linear: { [atom('a')]: 1, [atom('c')]: 1 }, persistent: {} });
    const fold = (events) => events.reduce(
      (acc, e) => acc + (W[e.rule] ?? 0n) * BigInt(e.multiplicity || 1), 0n);
    const measures = [0, 1, 2, 42].map((seed) => fold(P.settle(init(), '10', { seed }).events));
    assert.ok(measures.every((m) => m === measures[0]), String(measures));
    const r = P.settleExplore(init(), '10', {
      leafMeasure: { unit: 0n, step: (acc, m) => acc + (W[m.rule.name] ?? 0n) } });
    assert.equal(r.leaves.length, 1, 'independent tied set — committed, no branch');
    assert.equal(r.leaves[0].measure, measures[0]);
  });

  it('woplus alternatives carry per-branch measures (altIndex visible to the fold)', () => {
    const P = load('flip.till', `
a: type. heads: type. tails: type.
flip: a -o { woplus 1/2 heads tails }@1.
`);
    const r = P.settleExplore({ linear: { [atom('a')]: 1 }, persistent: {} }, '10', {
      leafMeasure: { unit: 0n, step: (acc, m) =>
        acc + (m.rule.name === 'flip' ? (m.altIndex === 0 ? 10n : 1n) : 0n) } });
    assert.equal(r.leaves.length, 2);
    assert.deepEqual(r.leaves.map((l) => l.measure).sort(), [10n, 1n].sort());
  });
});
