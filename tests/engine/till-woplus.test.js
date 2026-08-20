/**
 * till weighted internal choice `woplus Q A B` — TODO_0265 Phase 4b.
 *
 * Pins:
 *   - compile: exact alternative weights (Q, 1−Q), distribution sums to 1,
 *     loud rejection of out-of-range / variable weights and antecedent use
 *   - exec (settle): stateless PRF branch draw — same seed ⇒ replay-identical
 *     (including across horizon splits); both branches reachable across seeds
 *   - explore: weighted forks (weights sum to 1 per fork), leaves carry exact
 *     path weights — the tree IS the distribution; reproduces combat.mjs's
 *     absorbing-chain numbers on the duel (1r vs 2s ⇒ P(red) = 9/16)
 *   - exec-vs-explore agreement: every sampled outcome is a positive-weight leaf
 *   - untimed engine rejects weighted rules loudly
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { FIX, loadTill as load, atom, bag } from './till-helpers.js';

const wOf = (l) => Number(l.weight[0]) / Number(l.weight[1]);

// ─── combat.mjs absorbing-chain DP (ported reference) ────────────────
// Single-type armies: r rocks vs s scissors, p = P(rock beats scissors).
// Uniform matchmaking is trivial (one type per side), so per round a
// scissors dies w.p. p, a rock w.p. 1−p — exactly the deaths() formula of
// combat.mjs specialized to single types.
function winProbDP(r, s, p) {
  if (s === 0) return 1;
  if (r === 0) return 0;
  return p * winProbDP(r, s - 1, p) + (1 - p) * winProbDP(r - 1, s, p);
}

describe('woplus compile (Phase 4b)', () => {
  let calc;
  before(() => { calc = load(FIX('till-duel.ill')); });

  it('alternatives carry exact weights Q and 1−Q, rule marked weighted', () => {
    const fight = calc.forwardRules.find(r => r.name === 'fight');
    assert.ok(fight.weighted);
    assert.equal(fight.consequentAlts.length, 2);
    assert.deepEqual(fight.consequentAlts[0].weight, [3n, 4n]);
    assert.deepEqual(fight.consequentAlts[1].weight, [1n, 4n]);
    assert.deepEqual(fight.consequentAlts[0].linear, [atom('rock')]);
    assert.deepEqual(fight.consequentAlts[1].linear, [atom('sci')]);
  });

  it('rejects weights outside [0,1] and unbound weight variables', () => {
    assert.throws(() => load(FIX('till-woplus-bad.ill')), /weight must be in \[0, 1\]/);
    assert.throws(() => load(FIX('till-woplus-var.ill')), /not bound by any antecedent pattern or goal/);
  });

  it('untimed engine rejects weighted rules loudly', () => {
    const S = { linear: { [atom('rock')]: 1, [atom('sci')]: 1 }, persistent: {} };
    assert.throws(() => calc.exec(S), /woplus.*timed matcher|timed matcher.*woplus/);
  });
});

describe('woplus exec — PRF branch sampling (D17)', () => {
  let calc;
  before(() => { calc = load(FIX('till-duel.ill')); });
  const duel = (r, s) => ({
    linear: { [atom('rock')]: r, [atom('sci')]: s }, persistent: {},
  });

  it('same seed ⇒ replay-identical branch sequence and final state', () => {
    for (const seed of [0, 7, 42]) {
      const a = calc.settle(duel(2, 2), '0', { seed });
      const b = calc.settle(duel(2, 2), '0', { seed });
      assert.deepEqual(a.events.map(e => e.alt), b.events.map(e => e.alt));
      assert.deepEqual(bag(a.state), bag(b.state));
    }
  });

  it('both branches reachable across seeds (1v1)', () => {
    const outcomes = new Set();
    for (let s = 0; s < 32; s++) {
      outcomes.add(Object.keys(bag(calc.settle(duel(1, 1), '0', { seed: s }).state)).join(','));
    }
    assert.deepEqual([...outcomes].sort(), ['rock', 'sci']);
  });

  it('PRF golden pins: exact alt sequence per seed (round-13 residue i)', () => {
    // Concrete-draw pins (see till-settle PRF pins): a PRF-internals or
    // store-hashing change re-samples these — verify intent, then re-pin.
    // NOTE: the PRF mixes state.stateHash, which is arena-layout dependent —
    // these values are stable for THIS file's load order, not across files.
    // Adding tests above this one may shift them; re-pin deliberately.
    // node-only: bun's module evaluation interns in a different order.
    if (typeof Bun !== 'undefined') return;
    // Re-pinned (TODO_0268 A): till.calc declares the timed templates →
    // interning shift.
    assert.deepEqual({
      s4: calc.settle(duel(2, 2), '0', { seed: 4 }).events.map(e => e.alt),
      s10: calc.settle(duel(2, 2), '0', { seed: 10 }).events.map(e => e.alt),
    }, { s4: [0, 0], s10: [1, 0, 1] });
  });

  it('sampler frequency matches the declared weight (chi-square-lite, residue ii)', () => {
    // 4000 seeds on the 1v1 duel: P(rock survives) = 3/4. The draw is a
    // 32-bit floor-discretized PRF (bias < 2⁻³², documented in till.md).
    // Tolerance is 4σ = 4·√(p(1−p)/n) ≈ 0.027: the stream re-rolls on any
    // interning shift (fixture/.calc edits), so a 3σ gate falsely fails
    // ~1 in 370 unrelated edits — 4σ keeps the power, drops the noise
    // (a genuinely mis-weighted sampler is tens of σ out, not 4).
    let rock = 0;
    const n = 4000;
    for (let seed = 0; seed < n; seed++) {
      if (bag(calc.settle(duel(1, 1), '0', { seed }).state).rock) rock++;
    }
    assert.ok(Math.abs(rock / n - 0.75) < 4 * Math.sqrt(0.75 * 0.25 / n),
      `rock frequency ${rock / n} not within 4σ of 3/4`);
  });

  it('branch draws are horizon-split invariant (delayed duel)', () => {
    const S = { linear: { [atom('rockd')]: 2, [atom('scid')]: 2 }, persistent: {} };
    for (const seed of [1, 5, 9]) {
      const direct = calc.settle(S, '10', { seed });
      const mid = calc.settle(S, '3/2', { seed });
      const resumed = calc.settle(mid.state, '10', { seed });
      assert.deepEqual(
        [...mid.events, ...resumed.events].map(e => `${e.rule}:${e.alt}`),
        direct.events.map(e => `${e.rule}:${e.alt}`), `seed ${seed}`);
      assert.deepEqual(bag(resumed.state), bag(direct.state));
    }
  });
});

describe('woplus explore — the tree is the exact distribution', () => {
  let calc;
  before(() => { calc = load(FIX('till-duel.ill')); });

  it('1 rock vs 1 scissors: one fork, weights 3/4 and 1/4 (DP: 0.75)', () => {
    const S = { linear: { [atom('rock')]: 1, [atom('sci')]: 1 }, persistent: {} };
    const { tree, leaves } = calc.settleExplore(S, '0');
    assert.equal(tree.type, 'choice');
    assert.equal(tree.rule, 'fight');
    // weights sum to 1 per fork
    const sum = tree.children.reduce((s, c) => s + Number(c.weight[0]) / Number(c.weight[1]), 0);
    assert.equal(sum, 1);
    const pRock = leaves.filter(l => bag(l.state).rock).reduce((s, l) => s + wOf(l), 0);
    assert.equal(pRock, winProbDP(1, 1, 0.75));   // 0.75
  });

  it('1 rock vs 2 scissors: absorbing chain gives P(red) = 9/16 (combat.mjs DP)', () => {
    const S = { linear: { [atom('rock')]: 1, [atom('sci')]: 2 }, persistent: {} };
    const { leaves } = calc.settleExplore(S, '0');
    // exact rational aggregation: sum weights of leaves where rock survives
    let num = 0n, den = 1n;
    for (const l of leaves) {
      if (bag(l.state).rock) {
        const [n, d] = l.weight;
        num = num * d + n * den; den = den * d;
      }
    }
    // 3/4 · 3/4 = 9/16 exactly
    assert.equal(Number(num) / Number(den), 9 / 16);
    assert.equal(Number(num) / Number(den), winProbDP(1, 2, 0.75));
    // total mass across all leaves is exactly 1
    let tn = 0n, td = 1n;
    for (const l of leaves) { const [n, d] = l.weight; tn = tn * d + n * td; td = td * d; }
    assert.equal(Number(tn) / Number(td), 1);
  });

  it('exec outcomes are positive-weight explore leaves (agreement)', () => {
    const S = { linear: { [atom('rock')]: 1, [atom('sci')]: 2 }, persistent: {} };
    const leafBags = calc.settleExplore(S, '0').leaves
      .filter(l => l.weight[0] > 0n)
      .map(l => JSON.stringify(bag(l.state)));
    for (let seed = 0; seed < 16; seed++) {
      const out = JSON.stringify(bag(calc.settle(S, '0', { seed }).state));
      assert.ok(leafBags.includes(out), `seed ${seed}: ${out}`);
    }
  });
});

// ─── Phase 6: fire-time weights — woplus Q with Q bound by matching ──

describe('woplus fire-time weights (Phase 6)', () => {
  let calc;
  before(() => { calc = load(FIX('till-duel-dyn.ill')); });
  const u = (n) => atom(n);
  const vs = (a, b) => ({
    linear: { [Store.put('red', [u(a)])]: 1, [Store.put('blue', [u(b)])]: 1 },
    persistent: {},
  });

  it('compile: rule marked weighted + weightDynamic, symbolic weights slotted', () => {
    const duel = calc.forwardRules.find(r => r.name === 'duel');
    assert.ok(duel.weighted);
    assert.ok(duel.weightDynamic);
    assert.equal(duel.consequentAlts.length, 2);
    const [wl, wr] = duel.consequentAlts.map(a => a.weight);
    assert.deepEqual(wl.g, [1n, 1n]);
    assert.equal(wl.syms.length, 1);
    assert.equal(wl.syms[0].comp, false);
    assert.equal(wr.syms[0].comp, true);
    assert.equal(typeof wl.syms[0].slot, 'number');
    assert.equal(wl.syms[0].slot, wr.syms[0].slot);   // same Q
  });

  it('exec: weight 1 / weight 0 are deterministic across seeds', () => {
    for (let seed = 0; seed < 8; seed++) {
      // winprob rock paper 1 — red rock always wins (bag keys by tag)
      const win = bag(calc.settle(vs('rock', 'paper'), '0', { seed }).state);
      assert.deepEqual(win, { red: 1, fellb: 1 });
      // winprob paper rock 0 — red paper always falls
      const lose = bag(calc.settle(vs('paper', 'rock'), '0', { seed }).state);
      assert.deepEqual(lose, { blue: 1, fellr: 1 });
    }
  });

  it('exec: same seed ⇒ replay-identical (mirror duel, Q = 1/2)', () => {
    for (const seed of [0, 7, 42]) {
      const a = calc.settle(vs('rock', 'rock'), '0', { seed });
      const b = calc.settle(vs('rock', 'rock'), '0', { seed });
      assert.deepEqual(a.events.map(e => e.alt), b.events.map(e => e.alt));
      assert.deepEqual(bag(a.state), bag(b.state));
    }
  });

  it('sampler frequency matches the RESOLVED weight (Q = 3/4)', () => {
    let red = 0;
    const n = 800;
    for (let seed = 0; seed < n; seed++) {
      if (bag(calc.settle(vs('rock', 'sci'), '0', { seed }).state).red) red++;
    }
    assert.ok(Math.abs(red / n - 0.75) < 0.05, `red frequency ${red / n} not near 3/4`);
  });

  it('explore: fork edges carry the resolved weights; DP agreement 1v2 = 9/16', () => {
    const one = calc.settleExplore(vs('rock', 'sci'), '0');
    assert.equal(one.tree.type, 'choice');
    assert.deepEqual(one.tree.children.map(c => c.weight), [[3n, 4n], [1n, 4n]]);
    const S = { linear: { [Store.put('red', [u('rock')])]: 1, [Store.put('blue', [u('sci')])]: 2 }, persistent: {} };
    const { leaves } = calc.settleExplore(S, '0');
    let num = 0n, den = 1n;
    for (const l of leaves) {
      if (bag(l.state).red) { const [n, d] = l.weight; num = num * d + n * den; den = den * d; }
    }
    assert.equal(Number(num) / Number(den), winProbDP(1, 2, 0.75));   // 9/16
  });

  it('fire-time errors are loud: out-of-range and ill-sorted weights', () => {
    const range = load(FIX('till-woplus-dyn-range.ill'));
    assert.throws(
      () => range.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '0'),
      /outside \[0, 1\]/);
    const sort = load(FIX('till-woplus-dyn-sort.ill'));
    assert.throws(
      () => sort.settle({ linear: { [Store.put('p', [atom('foo')])]: 1 }, persistent: {} }, '0'),
      /did not resolve to a ground rational at fire time/);
  });
});
