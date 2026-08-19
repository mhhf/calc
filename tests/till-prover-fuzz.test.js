/**
 * Sequent-level fuzz for the till backward prover — round-15 F6.ii.
 *
 * Two decidable fragments with INDEPENDENT oracles (not the prover, not
 * the grade algebra):
 *
 *   A. multiplicative/counted fragment {atoms, ⊗, I, !_k}: provability
 *      ⟺ equal atom bags (each side is a commutative-monoid word; !_k
 *      contributes k copies). Catches counted-bang rule miscompiles and
 *      template-guard bugs in BOTH directions (false proofs AND false
 *      refutations).
 *
 *   B. graded-monad towers {…{a}@d₁…}@dₙ ⊢ {a}@e: provable ⟺ e ≥ Σdᵢ
 *      (graded-μ + fused subeffecting; empty tower ⊢ {a}@e always).
 *      The oracle sums exact fractions in BigInt — independent of the
 *      engine's rational algebra.
 *
 * Every prover SUCCESS must be FULLY kernel-verified (valid, no
 * unverified steps — round-15 F1 contract).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadTillSequent, tillGrades } from '../calculus/till/calculus-config.js';

// deterministic PRNG (xorshift32)
const mkRand = (seed) => {
  let s = seed >>> 0 || 1;
  return () => {
    s ^= s << 13; s >>>= 0;
    s ^= s >> 17;
    s ^= s << 5; s >>>= 0;
    return s / 0x100000000;
  };
};
const pick = (rnd, xs) => xs[Math.floor(rnd() * xs.length)];

describe('till sequent fuzz — prover vs independent oracles', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadTillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
  });

  const prove = (linear, succ) =>
    prover.prove(Seq.fromArrays(linear, [], succ), { rules: specs, alternatives });

  const check = (linear, succ, expectProvable, desc) => {
    const r = prove(linear, succ);
    assert.strictEqual(r.success, expectProvable,
      `${desc}: prover says ${r.success ? 'provable' : 'refuted'}, oracle says ${expectProvable ? 'provable' : 'refuted'}`);
    if (r.success) {
      const v = kernel.verifyTree(r.proofTree);
      assert.ok(v.valid, `${desc}: kernel rejected: ${v.errors.join('; ')}`);
      assert.strictEqual(v.unverified, undefined, `${desc}: unverified steps`);
    }
  };

  // ── fragment A: {atoms, ⊗, I, !_k} vs the bag oracle ────────────────
  // formula := atom | I | !_k atom (k ≥ 1) | formula ⊗ formula
  // bag(w) = atom multiset; Γ ⊢ G provable ⟺ bag(Γ) = bag(G)
  const ATOMS = ['fza', 'fzb'];
  const genWord = (rnd, depth, bag) => {
    const r = rnd();
    if (depth <= 0 || r < 0.35) {
      const a = pick(rnd, ATOMS);
      bag[a] = (bag[a] || 0) + 1;
      return P(a);
    }
    if (r < 0.45) return P('I');
    if (r < 0.6) {
      const a = pick(rnd, ATOMS);
      const k = 1 + Math.floor(rnd() * 3);
      bag[a] = (bag[a] || 0) + k;
      return P(`!_${k} ${a}`);
    }
    const l = genWord(rnd, depth - 1, bag);
    const rr = genWord(rnd, depth - 1, bag);
    return Store.put('tensor', [l, rr]);
  };
  const bagEq = (x, y) => {
    const ks = new Set([...Object.keys(x), ...Object.keys(y)]);
    for (const k of ks) if ((x[k] || 0) !== (y[k] || 0)) return false;
    return true;
  };

  // realize a bag as a random word (different parcel/tensor shape each
  // time — the provable cases then exercise peel/merge across regroupings)
  const wordFromBag = (rnd, bag) => {
    const parts = [];
    for (const [a, count] of Object.entries(bag)) {
      let left = count;
      while (left > 0) {
        const k = 1 + Math.floor(rnd() * left);        // split k off this atom's count
        parts.push(k > 1 ? P(`!_${k} ${a}`) : P(a));
        left -= k;
      }
    }
    if (parts.length === 0 || rnd() < 0.2) parts.push(P('I'));
    let w = parts[0];
    for (let i = 1; i < parts.length; i++) {
      w = rnd() < 0.5 ? Store.put('tensor', [w, parts[i]]) : Store.put('tensor', [parts[i], w]);
    }
    return w;
  };

  it('fragment A: 80 random words — provability ⟺ equal atom bags', () => {
    const rnd = mkRand(0xf00d);
    for (let i = 0; i < 80; i++) {
      const lb = {}, rb = {};
      const nLeft = 1 + Math.floor(rnd() * 2);
      const linear = Array.from({ length: nLeft }, () => genWord(rnd, 2, lb));
      // even i: right side REALIZES the left bag (provable, reshaped);
      // odd i: independent generation (mostly refuted)
      const succ = i % 2 === 0 ? wordFromBag(rnd, lb) : genWord(rnd, 2, rb);
      const expect = i % 2 === 0 ? true : bagEq(lb, rb);
      check(linear, succ, expect, `A#${i} bags ${JSON.stringify(lb)} vs ${i % 2 === 0 ? 'realized' : JSON.stringify(rb)}`);
    }
  });

  // ── fragment B: monad towers vs BigInt fraction arithmetic ──────────
  // {…{a}@d₁…}@dₙ ⊢ {a}@e provable ⟺ e ≥ Σdᵢ  (n = 0 ⟹ always)
  const GRADES = [[0n, 1n], [1n, 1n], [2n, 1n], [1n, 2n], [3n, 2n]];
  const fracStr = ([n, d]) => (d === 1n ? `${n}` : `${n}/${d}`);
  const fracSum = (fs) => fs.reduce(([an, ad], [bn, bd]) => {
    const n = an * bd + bn * ad, d = ad * bd;
    return [n, d];
  }, [0n, 1n]);
  const fracGe = ([an, ad], [bn, bd]) => an * bd >= bn * ad;   // ad, bd > 0
  const tower = (grades) => {
    let f = P('fza');
    for (const g of grades) {
      f = Store.put('monad', [tillGrades.parseStamp(fracStr(g)), f]);
    }
    return f;
  };

  it('fragment B: 80 random towers — provability ⟺ e ≥ Σdᵢ', () => {
    const rnd = mkRand(0xbeef);
    for (let i = 0; i < 80; i++) {
      const n = Math.floor(rnd() * 4);                       // 0..3 levels
      const ds = Array.from({ length: n }, () => pick(rnd, GRADES));
      const e = pick(rnd, GRADES);
      const lhs = tower(ds);
      const rhs = Store.put('monad', [tillGrades.parseStamp(fracStr(e)), P('fza')]);
      const expect = fracGe(e, fracSum(ds));
      check([lhs], rhs, expect,
        `B#${i} tower [${ds.map(fracStr)}] ⊢ {a}@${fracStr(e)}`);
    }
  });

  it('fragment B corner: tower ⊢ bare atom is refuted for n ≥ 1', () => {
    check([tower([[1n, 1n]])], P('fza'), false, 'B corner {a}@1 ⊢ a');
    check([P('fza')], P('fza'), true, 'B corner a ⊢ a');
  });
});
