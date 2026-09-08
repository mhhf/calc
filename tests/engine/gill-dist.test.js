/**
 * gill distance axis (TODO_0284 P3) — the (min,+) reading of the timed
 * scheduler, property-tested against an independent Dijkstra.
 *
 * Model (depot.gill discipline): node-reachability tokens are READ
 * (measured, never consumed — original stamp, no committed-choice
 * competition between outgoing edges), roads are one-shot linear tokens
 * (each edge relaxes once), segment cost = rule delay. Then per-firing
 * optimality (B&B keeps the ≤-least candidate — an edge fires reading
 * the FIRST arrival at its source) + nondecreasing frontier order give
 * exactly Dijkstra: min arrival stamp per node = shortest distance.
 * Exact rationals throughout (weights include halves — never a float).
 *
 * Also pins the P3 registry plumbing: gradeAlgebraFor routes haul → dist
 * → distGrades and monad → delay → tillGrades; buildTimedConfig accepts
 * distGrades (order class); distGrades is a distinct frozen instance
 * with the canonical slots.
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import { buildTimedConfig } from '../../lib/engine/timed/timed.js';
import { ratParts } from '../../lib/kernel/rat-term.js';
import { add as ratAdd, cmp as ratCmp } from '../../lib/rat.js';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import gillConfig, { distGrades, gillGradeRegistry, gradeAlgebraFor, loadGillSequent } from '../../calculus/gill/calculus-config.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { certifyRun } from '../../lib/prover/timed/elaborate-trace.js';

// ── seeded PRNG (mulberry32 — deterministic graphs) ──
function prng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// weights: exact rationals, integers and halves ([n, d] BigInt pairs)
const WEIGHTS = [
  [1n, 1n], [2n, 1n], [3n, 1n], [5n, 1n], [7n, 1n], [9n, 1n],
  [1n, 2n], [3n, 2n], [5n, 2n],
];
const wStr = ([n, d]) => (d === 1n ? `${n}` : `(${n}/${d})`);

function randomGraph(rnd, n, m) {
  const edges = [];
  for (let i = 0; i < m; i++) {
    const u = Math.floor(rnd() * n);
    let v = Math.floor(rnd() * n);
    if (v === u) v = (v + 1) % n;
    edges.push({ u, v, w: WEIGHTS[Math.floor(rnd() * WEIGHTS.length)] });
  }
  return { n, edges };
}

// independent reference: Dijkstra on exact rationals (O(V²) scan)
function dijkstra(g, src) {
  const dist = Array(g.n).fill(null);   // null = ∞
  const done = Array(g.n).fill(false);
  dist[src] = [0n, 1n];
  for (;;) {
    let u = -1;
    for (let i = 0; i < g.n; i++) {
      if (!done[i] && dist[i] !== null && (u === -1 || ratCmp(dist[i], dist[u]) < 0)) u = i;
    }
    if (u === -1) return dist;
    done[u] = true;
    for (const e of g.edges) {
      if (e.u !== u) continue;
      const d = ratAdd(dist[u], e.w);
      if (dist[e.v] === null || ratCmp(d, dist[e.v]) < 0) dist[e.v] = d;
    }
  }
}

function graphProgram(g) {
  const lines = [];
  for (let i = 0; i < g.n; i++) lines.push(`n${i}: type.`);
  g.edges.forEach((_, i) => lines.push(`e${i}: type.`));
  g.edges.forEach((e, i) =>
    lines.push(`hop${i}: read n${e.u} * e${i} -o { n${e.v} }@${wStr(e.w)}.`));
  return lines.join('\n') + '\n';
}

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'gill-dijkstra-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

/** Settle the graph program and read min arrival stamp per node. */
function settleDistances(g, file, config = gillConfig) {
  fs.writeFileSync(file, graphProgram(g));
  const calc = mde.load(file, { calculusConfig: config, cache: false });
  const linear = { [Store.put('atom', ['n0'])]: 1 };
  g.edges.forEach((_, i) => { linear[Store.put('atom', [`e${i}`])] = 1; });
  let horizon = [1n, 1n];
  for (const e of g.edges) horizon = ratAdd(horizon, e.w);
  const res = calc.settle({ linear, persistent: {} }, `${horizon[0]}/${horizon[1]}`,
    { maxSteps: 10000 });
  const arrived = Array(g.n).fill(null);
  for (const hStr in res.state.linear) {
    const h = Number(hStr);
    const inner = Store.tag(h) === 'at' ? Store.child(h, 0) : h;
    if (Store.tag(inner) !== 'atom') continue;
    const name = Store.child(inner, 0);
    if (!/^n\d+$/.test(name)) continue;
    const i = parseInt(name.slice(1), 10);
    const stamp = Store.tag(h) === 'at' ? ratParts(Store.child(h, 1)) : [0n, 1n];
    if (arrived[i] === null || ratCmp(stamp, arrived[i]) < 0) arrived[i] = stamp;
  }
  return arrived;
}

describe('gill dist axis: settle ≡ Dijkstra (P3 property test)', () => {
  it('fixed diamond: two routes 3+4 vs 5+1 → depot at 6 (the todo acceptance shape)', () => {
    const g = { n: 4, edges: [
      { u: 0, v: 1, w: [3n, 1n] }, { u: 1, v: 3, w: [4n, 1n] },
      { u: 0, v: 2, w: [5n, 1n] }, { u: 2, v: 3, w: [1n, 1n] },
    ] };
    const got = settleDistances(g, path.join(tmp, 'diamond.gill'));
    assert.deepEqual(got, [[0n, 1n], [3n, 1n], [5n, 1n], [6n, 1n]]);
  });

  it('random graphs: min arrival stamp per node = exact Dijkstra distance', () => {
    const rnd = prng(20260828);
    for (let k = 0; k < 6; k++) {
      const n = 5 + Math.floor(rnd() * 4);
      const g = randomGraph(rnd, n, 2 * n + Math.floor(rnd() * n));
      const want = dijkstra(g, 0);
      const got = settleDistances(g, path.join(tmp, `g${k}.gill`));
      for (let i = 0; i < n; i++) {
        if (want[i] === null) {
          assert.equal(got[i], null, `graph ${k}: node n${i} unreachable`);
        } else {
          assert.ok(got[i] !== null, `graph ${k}: node n${i} should be reached`);
          assert.equal(ratCmp(got[i], want[i]), 0,
            `graph ${k}: n${i} got ${got[i]} want ${want[i]}`);
        }
      }
    }
  });
});

describe('gill grade registry (P3)', () => {
  it('gradeAlgebraFor routes by the grade sort of the connective', () => {
    assert.strictEqual(gradeAlgebraFor('haul'), distGrades);
    assert.strictEqual(gradeAlgebraFor('monad'), tillGrades);
    assert.strictEqual(gradeAlgebraFor('at'), tillGrades);       // delay stamp
    assert.strictEqual(gradeAlgebraFor('bang'), tillGrades);     // count: structural → default
    assert.strictEqual(gradeAlgebraFor('tensor'), tillGrades);   // no grade arg → default
    assert.strictEqual(gillGradeRegistry.bySort.dist, distGrades);
    assert.strictEqual(gillGradeRegistry.default, tillGrades);
  });

  it('distGrades is a distinct frozen instance with the canonical slots', () => {
    assert.notStrictEqual(distGrades, tillGrades);
    assert.ok(Object.isFrozen(distGrades));
    assert.equal(distGrades.values.merge, 'join');    // R2 pin: ⊔ stays join
    assert.deepEqual(distGrades.aggregate, { class: 'order', realizations: ['prune'] });
  });

  it('buildTimedConfig accepts distGrades (order class — a schedulable axis)', () => {
    const tcfg = buildTimedConfig({ ...gillConfig, grades: distGrades });
    assert.ok(tcfg);
    assert.deepEqual(tcfg.aggregate, { class: 'order', realizations: ['prune'] });
  });

  it('distGrades as the ACTIVE axis: a live settle schedules identically (one dioid, two readings)', () => {
    // Not just registry data: the frozen dist instance actually DRIVES a
    // settle as cc.grades. Same arrivals as the time reading — the
    // identity of the two tropical instances, exercised, not asserted.
    const g = { n: 4, edges: [
      { u: 0, v: 1, w: [3n, 1n] }, { u: 1, v: 3, w: [4n, 1n] },
      { u: 0, v: 2, w: [5n, 1n] }, { u: 2, v: 3, w: [1n, 1n] },
    ] };
    const got = settleDistances(g, path.join(tmp, 'diamond-dist.gill'),
      { ...gillConfig, grades: distGrades });
    assert.deepEqual(got, [[0n, 1n], [3n, 1n], [5n, 1n], [6n, 1n]]);
  });
});

describe('gill certified run (TODO_0296 P2 — the verification face is generic)', () => {
  it('the diamond depot run elaborates and fully kernel-verifies under gill', () => {
    // The genericity claim made executable: gill binds fire: in its
    // loader (same additive ⊕/⊖ stamp shape as till), the depot trace —
    // READ node tokens, one-shot roads, cost-as-delay — elaborates into
    // an @fire chain, and gill's OWN kernel re-derives it. Until this
    // test, "generic over till/gill" was aspirational.
    const g = { n: 4, edges: [
      { u: 0, v: 1, w: [3n, 1n] }, { u: 1, v: 3, w: [4n, 1n] },
      { u: 0, v: 2, w: [5n, 1n] }, { u: 2, v: 3, w: [1n, 1n] },
    ] };
    const file = path.join(tmp, 'diamond-cert.gill');
    fs.writeFileSync(file, graphProgram(g));
    const engineCalc = mde.load(file, { calculusConfig: gillConfig, cache: false });
    const seqCalc = loadGillSequent();
    assert.ok(seqCalc.fire && seqCalc.stepCheckers, 'gill must bind the fire checker');
    const kernel = createKernel(seqCalc);
    const linear = { [Store.put('atom', ['n0'])]: 1 };
    g.edges.forEach((_, i) => { linear[Store.put('atom', [`e${i}`])] = 1; });
    const horizonTerm = Store.child(seqCalc.parse('x@13'), 1);
    const r = certifyRun({
      engineCalc, calculus: seqCalc, kernel,
      state: { linear, persistent: {} },
      horizon: '13', horizonTerm,
      settleOpts: { maxSteps: 1000 },
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.ok(r.events.length >= 4, 'all four edges relax');
  });
});
