/**
 * GradeAlgebra conformance harness (TODO_0284 P0/P0b).
 *
 * Executable form of doc/documentation/grade-algebra.md: takes an algebra
 * object in the canonical signature and property-checks the condition
 * family selected by aggregate.class.
 *
 *   order class   — C1 total order, C2 monotone ⊗, C3 inflationary ⊗,
 *                   C4 merge = join, residual fence, prunes default.
 *                   (C5 termination is operational — Zeno guard/horizon,
 *                   pinned by the till suite, not property-testable here.)
 *   measure class — ⊗ monoid laws + NON-inflationarity (the class split),
 *                   M1 mass conservation, M2 monotone ω-chain to the
 *                   fixpoint + subcriticality, M3 unbiased sampling.
 *
 * Fixtures:
 *   - tillGrades, READ-ONLY: the canonical view is derived exactly as
 *     timed.js computes it inline today (merge = max by cmp at :211/:323/
 *     :368, prunes = cmp >= 0 at :247). Documents that the live time
 *     algebra already satisfies C. Plus hash-face ≡ value-face coherence.
 *   - weightGrades (ℚ≥0, ·): standalone literal — the P3b/0292 measure
 *     instance, engine-independent today, checked against a reference
 *     weighted-choice-forest evaluator (M1/M3) and the THY_0026 T2
 *     recursive-mass chain (M2).
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import { add, sub, mul, div, cmp as ratCmp, norm } from '../../lib/rat.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

// ── deterministic PRNG (mulberry32) — seeded, so no flakes ──
function prng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const randRat = (rnd) => norm(BigInt(Math.floor(rnd() * 1000)), BigInt(1 + Math.floor(rnd() * 99)));
const V = (n, d = 1n) => norm(BigInt(n), BigInt(d));

// ── canonical views (grade-algebra.md signature) ──

const vals = tillGrades.values;
const tillView = {
  name: 'tillGrades(time)',
  unit: vals.unit,
  compose: (a, b) => vals.add(a, b),
  residual: (a, b) => { const r = vals.sub(a, b); return r[0] < 0n ? null : r; },
  cmp: vals.cmp,
  merge: (a, b) => (vals.cmp(a, b) > 0 ? a : b),
  prunes: (p, b) => vals.cmp(p, b) >= 0,
  aggregate: { class: 'order', realizations: ['prune'] },
};

const weightGrades = {
  name: 'weightGrades(ℚ≥0,·)',
  unit: [1n, 1n],
  compose: mul,
  residual: (a, b) => (b[0] === 0n ? null : div(a, b)),
  cmp: ratCmp,                       // index order only — NEVER a prune direction
  merge: mul,                        // co-consumed independence (THY_0026 T4-d)
  aggregate: { class: 'measure', realizations: ['sum', 'sample'] },
};

// ── order-class harness ──

function conformOrder(alg, { seed = 42, samples = 300 } = {}) {
  const rnd = prng(seed);
  const draws = Array.from({ length: samples }, () => randRat(rnd));
  describe(`order-class conformance: ${alg.name}`, () => {
    it('C1: cmp is a total order (reflexive, antisymmetric, transitive)', () => {
      for (let i = 0; i < samples; i++) {
        const a = draws[i], b = draws[(i + 1) % samples], c = draws[(i + 2) % samples];
        assert.equal(alg.cmp(a, a), 0);
        assert.ok([-1, 0, 1].includes(alg.cmp(a, b)));
        assert.equal(alg.cmp(a, b), -alg.cmp(b, a));
        if (alg.cmp(a, b) <= 0 && alg.cmp(b, c) <= 0) assert.ok(alg.cmp(a, c) <= 0);
      }
    });
    it('C2: compose is monotone in both arguments', () => {
      for (let i = 0; i < samples; i++) {
        const a = draws[i], b = draws[(i + 1) % samples], d = draws[(i + 2) % samples];
        const aUp = alg.compose(a, d);            // a ≤ aUp by C3
        assert.ok(alg.cmp(alg.compose(a, b), alg.compose(aUp, b)) <= 0);
        assert.ok(alg.cmp(alg.compose(b, a), alg.compose(b, aUp)) <= 0);
      }
    });
    it('C3: compose is inflationary and unit is least', () => {
      for (let i = 0; i < samples; i++) {
        const a = draws[i], b = draws[(i + 1) % samples];
        assert.ok(alg.cmp(alg.unit, a) <= 0);
        assert.ok(alg.cmp(a, alg.compose(a, b)) <= 0);
        assert.deepEqual(alg.compose(a, alg.unit), a);
      }
    });
    it('C4: merge is the join for cmp', () => {
      for (let i = 0; i < samples; i++) {
        const a = draws[i], b = draws[(i + 1) % samples], d = draws[(i + 2) % samples];
        const m = alg.merge(a, b);
        assert.ok(alg.cmp(a, m) <= 0 && alg.cmp(b, m) <= 0);
        // least upper bound (total order): the join IS one of the arguments
        assert.ok(alg.cmp(m, a) === 0 || alg.cmp(m, b) === 0);
        const aUp = alg.merge(a, d);
        assert.ok(alg.cmp(m, alg.merge(aUp, b)) <= 0);   // monotone
      }
    });
    it('residual fence: compose(b, residual(a,b)) = a, null ⟺ a < b', () => {
      for (let i = 0; i < samples; i++) {
        const a = draws[i], b = draws[(i + 1) % samples];
        const r = alg.residual(a, b);
        if (r === null) assert.ok(alg.cmp(a, b) < 0);
        else assert.deepEqual(alg.compose(b, r), a);
      }
    });
    it('prunes default = cmp(partial, best) >= 0; realization is [prune]', () => {
      assert.deepEqual(alg.aggregate, { class: 'order', realizations: ['prune'] });
      for (let i = 0; i < samples; i++) {
        const p = draws[i], b = draws[(i + 1) % samples];
        assert.equal(alg.prunes(p, b), alg.cmp(p, b) >= 0);
      }
    });
  });
}

// ── measure-class harness ──
//
// The engine cannot run weighted programs before P3b/0292, so M1/M3 are
// checked against a reference evaluator over weighted choice forests: a
// tree is leaf(name) or choice([[w, child], ...]); the mass of a leaf is
// unit, of a choice Σ wᵢ ⊗ mass(childᵢ) — the unnormalized measure.

function leafMasses(alg, tree, pathW, out) {
  if (tree.leaf) { out.push([tree.leaf, pathW]); return out; }
  for (const [w, child] of tree.alts) leafMasses(alg, child, alg.compose(pathW, w), out);
  return out;
}
function massOf(alg, tree) {
  if (tree.leaf) return alg.unit;
  let m = null;
  for (const [w, child] of tree.alts) {
    const part = alg.compose(w, massOf(alg, child));
    m = m === null ? part : add(m, part);
  }
  return m;
}
function randTree(rnd, depth, nextLeaf) {
  if (depth === 0 || rnd() < 0.3) return { leaf: `L${nextLeaf.n++}` };
  const k = 2 + Math.floor(rnd() * 2);
  const alts = [];
  for (let i = 0; i < k; i++) {
    const w = norm(BigInt(1 + Math.floor(rnd() * 9)), BigInt(1 + Math.floor(rnd() * 9)));
    alts.push([w, randTree(rnd, depth - 1, nextLeaf)]);
  }
  return { alts };
}
function sampleLeaf(alg, tree, rnd) {
  while (!tree.leaf) {
    const fl = ([n, d]) => Number(n) / Number(d);
    const total = tree.alts.reduce((s, [w]) => s + fl(w), 0);
    let u = rnd() * total;
    let pick = tree.alts[tree.alts.length - 1][1];
    for (const [w, child] of tree.alts) {
      u -= fl(w);
      if (u < 0) { pick = child; break; }
    }
    tree = pick;
  }
  return tree.leaf;
}

function conformMeasure(alg, { seed = 7, samples = 300 } = {}) {
  const rnd = prng(seed);
  describe(`measure-class conformance: ${alg.name}`, () => {
    it('⊗ is a commutative monoid, monotone — and NOT inflationary (class split)', () => {
      for (let i = 0; i < samples; i++) {
        const a = randRat(rnd), b = randRat(rnd), c = randRat(rnd);
        assert.deepEqual(alg.compose(alg.unit, a), a);
        assert.deepEqual(alg.compose(a, b), alg.compose(b, a));
        assert.deepEqual(alg.compose(alg.compose(a, b), c), alg.compose(a, alg.compose(b, c)));
        if (ratCmp(a, b) <= 0) assert.ok(ratCmp(alg.compose(a, c), alg.compose(b, c)) <= 0);
      }
      // a weight < 1 SHRINKS mass — order-class C3 fails, so prune is unsound
      const shrunk = alg.compose(V(3), V(1, 2));
      assert.ok(ratCmp(shrunk, V(3)) < 0);
      assert.equal(alg.prunes, undefined);
      assert.deepEqual(alg.aggregate, { class: 'measure', realizations: ['sum', 'sample'] });
    });
    it('residual fence: compose(b, residual(a,b)) = a; null only at mass 0', () => {
      for (let i = 0; i < samples; i++) {
        const a = randRat(rnd), b = randRat(rnd);
        const r = alg.residual(a, b);
        if (b[0] === 0n) assert.equal(r, null);
        else assert.deepEqual(alg.compose(b, r), a);
      }
    });
    it('M1: leaf-mass sum = recursive mass, exactly, at every choice point', () => {
      for (let t = 0; t < 40; t++) {
        const tree = randTree(rnd, 3, { n: 0 });
        const total = massOf(alg, tree);
        const leafSum = leafMasses(alg, tree, alg.unit, [])
          .reduce((s, [, w]) => (s === null ? w : add(s, w)), null);
        assert.deepEqual(leafSum, total);                  // exact rationals — no floats
        if (tree.alts) {                                   // conservation at the root choice
          const parts = tree.alts.map(([w, c]) => alg.compose(w, massOf(alg, c)));
          assert.deepEqual(parts.reduce(add), total);
        }
      }
    });
    it('M3: empirical sample frequency ≈ exact renormalized mass (seeded)', () => {
      const tree = randTree(prng(seed + 1), 3, { n: 0 });
      const exact = leafMasses(alg, tree, alg.unit, []);
      const total = massOf(alg, tree);
      const N = 20000;
      const counts = new Map();
      const srnd = prng(seed + 2);
      for (let i = 0; i < N; i++) {
        const l = sampleLeaf(alg, tree, srnd);
        counts.set(l, (counts.get(l) || 0) + 1);
      }
      for (const [leaf, w] of exact) {
        const p = Number(w[0]) / Number(w[1]) / (Number(total[0]) / Number(total[1]));
        const emp = (counts.get(leaf) || 0) / N;
        assert.ok(Math.abs(emp - p) < 0.02,
          `leaf ${leaf}: empirical ${emp} vs exact ${p}`);
      }
    });
    it('M2: depth-bounded mass is a monotone chain to the fixpoint iff subcritical', () => {
      // THY_0026 T2 shape — recursive sort c₀ | c₁(rec) | c₂(rec):
      //   m₀ = 0,  m_{k+1} = w₀ + (w₁ + w₂) ⊗ m_k
      const chain = (w0, wrec, K) => {
        const ms = [V(0)];
        for (let k = 0; k < K; k++) ms.push(add(w0, alg.compose(wrec, ms[k])));
        return ms;
      };
      // subcritical: w₁+w₂ = 3/8 < 1 ⇒ lub = w₀/(1 − 3/8) = 4/5
      const sub_ = chain(V(1, 2), V(3, 8), 40);
      const fix = V(4, 5);
      for (let k = 0; k < 40; k++) {
        assert.ok(ratCmp(sub_[k], sub_[k + 1]) <= 0);      // monotone ↑
        assert.ok(ratCmp(sub_[k], fix) <= 0);              // bounded by the lub
      }
      assert.ok(ratCmp(sub(fix, sub_[40]), V(1, 1000000n)) < 0);  // converged
      // supercritical: w₁+w₂ = 5/4 > 1 ⇒ mass diverges (no finite total)
      const sup = chain(V(1, 2), V(5, 4), 30);
      assert.ok(ratCmp(sup[30], V(100)) > 0);
    });
  });
}

// ── run the fixtures ──

conformOrder(tillView);
conformMeasure(weightGrades);

// ── tillGrades face coherence: hash face ≡ value face (read-only) ──

describe('tillGrades hash-face ≡ value-face coherence', () => {
  const rnd = prng(99);
  it('effect.{unit,compose,residual} and availability.cmp agree with values', () => {
    assert.deepEqual(ratParts(tillGrades.effect.unit()), vals.unit);
    for (let i = 0; i < 100; i++) {
      const a = randRat(rnd), b = randRat(rnd);
      const ha = vals.reify(a), hb = vals.reify(b);
      assert.deepEqual(ratParts(tillGrades.effect.compose(ha, hb)), add(a, b));
      assert.equal(tillGrades.availability.cmp(ha, hb), vals.cmp(a, b));
      const hr = tillGrades.effect.residual(ha, hb);
      const vr = tillView.residual(a, b);
      if (vr === null) assert.equal(hr, null);
      else assert.deepEqual(ratParts(hr), vr);
    }
  });
});
