/**
 * Decimation driver (TODO_0297 P2+P3; 0292 L3/M1/M4/M8/M9, THY_0026).
 *
 * Pins:
 *   - ∃_ρ surface (`exists X: s @w. A`) settles to a suspended
 *     superpose-fact; plain settle leaves it inert (D4 opt-in); plain
 *     `exists X. A` is a SKOLEM under the driver (M1)
 *   - recursion (P3): constructor members collapse lazily (one head per
 *     draw), geometric lengths, truncated exact totals are a monotone
 *     lower approximant of the mass fixpoint (D2(iii)); structured
 *     sorts require an explicit depth bound in exact/solve; Chi–Geman
 *     supercritical priors warn at load and hard-error in the driver
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
spawn: mk C -o { exists T: tile_t @w. tile C T }.
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

  it('plain settle leaves the suspended ∃_ρ-facts inert (D4)', () => {
    const res = calc.settle(init2(), 0, { maxSteps: 20 });
    assert.ok(res.quiescent);
    const tags = Object.keys(res.state.linear).map((k) => {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      return Store.tag(h);
    });
    assert.deepEqual(tags.sort(), ['superpose', 'superpose']);
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

describe('clause-derived bias (all-solutions query)', () => {
  const PROG = HEADER + `
bias/nocoast: bias X coast 0.
`;
  it("'exact': coast clause-pruned from every wave — total 16", () => {
    const calc = loadProg('clausebias.will', PROG);
    const r = calc.collapse(init2(), { mode: 'exact' });
    assert.deepEqual(r.total, [16n, 1n]);          // (2+2)²
    assert.ok(!r.outcomes.some((o) => tileOf(o.state, 'a0') === 'coast' || tileOf(o.state, 'a1') === 'coast'));
  });

  it('independent clauses on one (wave, member) ALL multiply; same-value derivations dedup', () => {
    // sea: 2 · 1/2 · 1/4 = 1/4 (two INDEPENDENT biases — committed
    // choice would keep only the first); coast: 1 · 1/2 (the same value
    // derived twice dedups to ONE factor — set semantics); land: 2.
    // Per-wave total 1/4 + 1/2 + 2 = 11/4; two waves → (11/4)².
    const calc = loadProg('multibias.will', HEADER + `
bias/seahalf: bias X sea 1/2.
bias/seaquarter: bias X sea 1/4.
bias/coasthalf: bias X coast 1/2.
bias/coasthalf2: bias X coast 1/2.
`);
    const r = calc.collapse(init2(), { mode: 'exact' });
    assert.deepEqual(r.total, [121n, 16n]);
  });
});

describe('exact × woplus (settleExplore composition, TODO_0298)', () => {
  const PROG = HEADER + `
flip: type.
heads: type.
tails: type.
flipr: flip -o { woplus 1/4 heads tails }.
`;
  const initFlip = () => ({
    linear: { [Store.put('mk', [atom('a0')])]: 1, [atom('flip')]: 1 },
    persistent: {},
  });
  const hasAtom = (state, name) => Object.keys(state.linear).map(Number)
    .some((h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h) === atom(name));

  it("'exact' enumerates woplus branches with exact weights; T1 total unchanged", () => {
    const calc = loadProg('woplus.will', PROG);
    const r = calc.collapse(initFlip(), { mode: 'exact' });
    assert.equal(r.outcomes.length, 6);            // 3 members × 2 coin sides
    assert.deepEqual(r.total, [5n, 1n]);           // woplus weights sum to 1
    const seaHeads = r.outcomes.find((o) => tileOf(o.state, 'a0') === 'sea' && hasAtom(o.state, 'heads'));
    assert.deepEqual(seaHeads.mass, [1n, 2n]);     // 2 · 1/4
    const landTails = r.outcomes.find((o) => tileOf(o.state, 'a0') === 'land' && hasAtom(o.state, 'tails'));
    assert.deepEqual(landTails.mass, [3n, 2n]);    // 2 · 3/4
  });

  it("'sample': mass includes the woplus factor; importance stays Π wave totals (T3)", () => {
    const calc = loadProg('woplus-sample.will', PROG);
    const tw = { sea: [2n, 1n], coast: [1n, 1n], land: [2n, 1n] };
    for (let seed = 0; seed < 10; seed++) {
      const r = calc.collapse(initFlip(), { seed });
      assert.ok(r.ground, `seed ${seed}`);
      assert.deepEqual(r.importance, [5n, 1n], 'woplus factors cancel in the estimator');
      const [tn, td] = tw[tileOf(r.state, 'a0')];
      const [fn, fd] = hasAtom(r.state, 'heads') ? [1n, 4n] : [3n, 4n];
      assert.equal(r.mass[0] * td * fd, tn * fn * r.mass[1],
        `seed ${seed}: mass ${r.mass} ≠ ${tn * fn}/${td * fd}`);
    }
  });

  it("settleBranching: 'seed' restores the chooser-resolved reading (one settle world)", () => {
    const calc = loadProg('woplus-seed.will', PROG);
    const r = calc.collapse(initFlip(), { mode: 'exact', settleBranching: 'seed' });
    assert.equal(r.outcomes.length, 3);
  });

  it('a genuine conflict is a loud error (adversarial worlds, not ⊕)', () => {
    const calc = loadProg('conflict.will', HEADER + `
coin: type.
g1: type.
g2: type.
grab1: coin -o { g1 }.
grab2: coin -o { g2 }.
`);
    const init = { linear: { [Store.put('mk', [atom('a0')])]: 1, [atom('coin')]: 1 }, persistent: {} };
    assert.throws(() => calc.collapse(init, { mode: 'exact' }), /conflict/);
    const ok = calc.collapse(init, { mode: 'exact', settleBranching: 'seed' });
    assert.equal(ok.outcomes.length, 3);
  });
});

describe('correlation — one binder over a tensor body', () => {
  const PROG = HEADER + `
mark: (t: tile_t) -> type.
mk2: (c: pos2) -> type.
spawn2: mk2 C -o { exists T: tile_t @w. (tile C T * mark T) }.
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

// ─── P3: skolems, recursion, truncation (TODO_0297 P3) ──────────────

describe('plain ∃ is a skolem under the driver (M1/D4)', () => {
  const PROG = HEADER + `
kick: type.
opaque: (t: tile_t) -> type.
skol: kick -o { exists T. opaque T }.
`;
  it('skolem evar survives, no collapse, reported', () => {
    const calc = loadProg('skol.will', PROG);
    const init = { linear: { [atom('kick')]: 1 }, persistent: {} };
    const r = calc.collapse(init, { seed: 0 });
    assert.ok(r.ground);
    assert.equal(r.skolems, 1);
    assert.equal(r.collapses.length, 0);
    assert.deepEqual(r.mass, [1n, 1n]);
    const evars = Object.keys(r.state.linear).filter((k) => {
      let found = false;
      (function walk(h) {
        if (Store.tag(h) === 'evar') { found = true; return; }
        for (let i = 0; i < Store.arity(h); i++) {
          const c = Store.child(h, i);
          if (Store.isTermChild(c)) walk(c);
        }
      })(Number(k));
      return found;
    });
    assert.equal(evars.length, 1, 'the opaque fact keeps its skolem witness');
  });
});

describe('recursion: lazy head-constructor collapse (P3, THY_0026 §3)', () => {
  // PCFG over lists: nil @w 1, cons @w 1/2 — subcritical (m = 1/3),
  // renormalized p(cons) = 1/3, geometric lengths E[L] = 1/2,
  // true total mass = 1/(1 − 1/2) = 2.
  const PROG = `#import(${MEASURE})
lst: sort.
nil: lst @w 1.
cons: (a: lst) -> lst @w 1/2.
kick: type.
out: (x: lst) -> type.
go: kick -o { exists X: lst @w. out X }.
`;
  let calc;
  before(() => { calc = loadProg('pcfg.will', PROG); });
  const init = () => ({ linear: { [atom('kick')]: 1 }, persistent: {} });
  const lenOf = (state) => {
    for (const k of Object.keys(state.linear)) {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      if (Store.tag(h) !== 'out') continue;
      let n = 0;
      let t = Store.child(h, 0);
      while (Store.tag(t) === 'cons') { n++; t = Store.child(t, 0); }
      assert.equal(Store.tag(t) === 'atom' ? Store.child(t, 0) : Store.tag(t), 'nil', 'ground list ends in nil');
      return n;
    }
    return null;
  };

  it('subcritical prior: no load advisory', () => {
    assert.equal(calc.priorLint.length, 0);
  });

  it("'sample': ground lists, geometric lengths, importance = (3/2)^draws", () => {
    let lenSum = 0;
    let impSum = 0;
    const N = 300;
    for (let seed = 0; seed < N; seed++) {
      const r = calc.collapse(init(), { seed });
      assert.ok(r.ground);
      const len = lenOf(r.state);
      assert.ok(len !== null);
      assert.equal(r.collapses.length, len + 1, 'n cons + 1 nil draws');
      assert.ok(Math.abs(q(r.importance) - Math.pow(1.5, len + 1)) < 1e-9);
      lenSum += len;
      impSum += q(r.importance);
    }
    const meanLen = lenSum / N;
    assert.ok(meanLen > 0.3 && meanLen < 0.7, `E[len] = ${meanLen}, want ≈ 0.5`);
    const meanImp = impSum / N;
    assert.ok(meanImp > 1.5 && meanImp < 2.5, `E[importance] = ${meanImp}, want ≈ 2 (the true total mass)`);
  });

  it("'exact': depth-bounded totals are a monotone lower approximant of the fixpoint 2 (D2(iii))", () => {
    const r1 = calc.collapse(init(), { mode: 'exact', maxCollapses: 1 });
    const r2 = calc.collapse(init(), { mode: 'exact', maxCollapses: 2 });
    const r4 = calc.collapse(init(), { mode: 'exact', maxCollapses: 4 });
    assert.deepEqual(r1.total, [1n, 1n]);          // nil only
    assert.deepEqual(r2.total, [3n, 2n]);          // + cons(nil)
    assert.deepEqual(r4.total, [15n, 8n]);         // 2 − (1/2)³
    assert.ok(r1.truncated && r2.truncated && r4.truncated);
  });

  it("'exact' without a depth bound over a structured sort is a loud error", () => {
    assert.throws(() => calc.collapse(init(), { mode: 'exact' }), /structured sort|maxCollapses/);
  });
});

describe('supercritical priors: load advisory + M7 integration (P3)', () => {
  const PROG = `#import(${MEASURE})
lst: sort.
leaf: lst @w 1.
node: (a: lst) -> (b: lst) -> lst @w 3.
kick: type.
out: (x: lst) -> type.
go: kick -o { exists X: lst @w. out X }.
`;
  it('load warns (m = 1.5); driver hard-errors without a bound; truncated exact works', () => {
    const calc = loadProg('super.will', PROG);
    assert.equal(calc.priorLint.length, 1);
    assert.equal(calc.priorLint[0].kind, 'supercritical-prior');
    assert.ok(Math.abs(calc.priorLint[0].m - 1.5) < 1e-9);
    const init = { linear: { [atom('kick')]: 1 }, persistent: {} };
    assert.throws(() => calc.collapse(init, { seed: 0 }), /supercritical|depth bound/);
    const r = calc.collapse(init, { mode: 'exact', maxCollapses: 3 });
    assert.deepEqual(r.total, [4n, 1n]);           // leaf (1) + node(leaf,leaf) (3)
    assert.ok(r.truncated);
  });
});

describe('schema expansion over a structured sort is a load error (rung 2)', () => {
  it('loud, names the constructor member', () => {
    assert.throws(() => loadProg('schema-rec.will', `#import(${MEASURE})
lst: sort.
nil: lst.
cons: (a: lst) -> lst.
seen: type.
mark: (r: lst) r -o { seen }.
`), /cannot schema-expand.*cons|constructor member 'cons'/);
  });
});

describe('evidence discipline (T4-d(i), THY_0028) — single counting + certificate visibility', () => {
  // Confluent programs; bias rules have persistent conclusions, which trip
  // the conservative instant-feed branch check — 'seed' is exact here.
  const OPTS = { mode: 'exact', settleBranching: 'seed' };
  const HEAD = `#import(${MEASURE})
cell: sort.
k0: cell.
src_t: sort.
s1: src_t.
s2: src_t.
mk: (c: cell) -> type.
tile: (c: cell) -> (t: tile_t) -> type.
spawn: mk C -o { exists T: tile_t @w. tile C T }.
`.replace('#import', `tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
#import`);
  const init = (extra) => {
    const linear = { [Store.put('mk', [atom('k0')])]: 1 };
    for (const [n, c] of Object.entries(extra)) linear[atom(n)] = c;
    return { linear, persistent: {} };
  };

  it('value-only bias facts UNDER-count independent evidence (fact-hash identity)', () => {
    const calc = loadProg('t4d-a.will', HEAD + `
obs1: type.
obs2: type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> type.
r1: obs1 * $tile C X -o { !bias X sea 1/2 }.
r2: obs2 * $tile C X -o { !bias X sea 1/2 }.
`);
    const r = calc.collapse(init({ obs1: 1, obs2: 1 }), OPTS);
    assert.deepEqual(r.total, [4n, 1n]);           // 2·(1/2) + 1 + 2 — ONE factor
  });

  it('source-tagged bias facts count independent evidence once each (Thm 1)', () => {
    const calc = loadProg('t4d-b.will', HEAD + `
obs1: type.
obs2: type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> (s: src_t) -> type.
r1: obs1 * $tile C X -o { !bias X sea 1/2 s1 }.
r2: obs2 * $tile C X -o { !bias X sea 1/2 s2 }.
`);
    const r = calc.collapse(init({ obs1: 1, obs2: 1 }), OPTS);
    assert.deepEqual(r.total, [7n, 2n]);           // 2·(1/2)·(1/2) + 1 + 2
  });

  it('idempotent re-derivation dedups: same rule, same source, fired twice', () => {
    const calc = loadProg('t4d-d.will', HEAD + `
obs: type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> (s: src_t) -> type.
r1: obs * $tile C X -o { !bias X sea 1/2 s1 }.
`);
    const r = calc.collapse(init({ obs: 2 }), OPTS);
    assert.deepEqual(r.total, [4n, 1n]);
  });

  it('smuggling is numerically INVISIBLE but certificate-visible (Thm 2)', () => {
    // C: ONE $-read observation feeds both rules — same total as B, but
    // the bias fires' provenances overlap where B's are disjoint.
    const calc = loadProg('t4d-c.will', HEAD + `
obs: type.
mk1: type.
mk2: type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> (s: src_t) -> type.
r1: $obs * $tile C X * mk1 -o { !bias X sea 1/2 s1 }.
r2: $obs * $tile C X * mk2 -o { !bias X sea 1/2 s2 }.
`);
    const r = calc.collapse(init({ obs: 1, mk1: 1, mk2: 1 }), OPTS);
    assert.deepEqual(r.total, [7n, 2n], 'identical to the honest total — no numeric detection');

    const provOf = (run) => {
      const out = [];
      for (const seg of run.trace.filter((t) => t.settle)) {
        for (const ev of seg.settle) {
          if (!/^r[0-9]/.test(ev.rule)) continue;
          const toks = [...Object.keys(ev.consumed || {}), ...Object.keys(ev.reserved || {})]
            .map((k) => {
              let h = Number(k);
              if (Store.tag(h) === 'at') h = Store.child(h, 0);
              return Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h);
            })
            .filter((n) => /^obs/.test(n));
          out.push(toks.sort().join(','));
        }
      }
      return out.sort();
    };
    const smuggled = provOf(calc.collapse(init({ obs: 1, mk1: 1, mk2: 1 }), { seed: 0, trace: true }));
    assert.deepEqual(smuggled, ['obs', 'obs'], 'overlapping provenance exhibited');

    const honest = loadProg('t4d-b2.will', HEAD + `
obs1: type.
obs2: type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> (s: src_t) -> type.
r1: obs1 * $tile C X -o { !bias X sea 1/2 s1 }.
r2: obs2 * $tile C X -o { !bias X sea 1/2 s2 }.
`);
    const disjoint = provOf(honest.collapse(init({ obs1: 1, obs2: 1 }), { seed: 0, trace: true }));
    assert.deepEqual(disjoint, ['obs1', 'obs2'], 'disjoint provenance in the honest program');
  });
});
