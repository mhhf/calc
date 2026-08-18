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
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';

const FIX = (f) => path.join(import.meta.dirname, '../fixtures', f);
const load = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });

const atom = (n) => Store.put('atom', [n]);
const wOf = (l) => Number(l.weight[0]) / Number(l.weight[1]);

/** Multiset of unstamped inner atoms in a plain state. */
function bag(state) {
  const out = {};
  for (const [hStr, c] of Object.entries(state.linear)) {
    let h = Number(hStr);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    const k = Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h);
    out[k] = (out[k] || 0) + c;
  }
  return out;
}

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

  it('rejects weights outside [0,1] and weight variables', () => {
    assert.throws(() => load(FIX('till-woplus-bad.ill')), /weight must be in \[0, 1\]/);
    assert.throws(() => load(FIX('till-woplus-var.ill')), /weight must be a ground rational/);
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
