/**
 * dill governance runtime (TODO_0276 / TODO_0318 — P0).
 *
 * Exercises the two consensus faces + the entity-veil, all through the real
 * engine:
 *   - EAGER / in-logic threshold quorum: company_cake.ill settles to a cake at
 *     C with the 50/50 cap table intact (the composite-principal scenario).
 *   - LAZY / derived-view kernels: govern.js consensus() over a settled
 *     name-the-org state — argmax-oldest, threshold, n-of-set, priority,
 *     time-locked — memhub's read-time consens (no NAF needed; it is a fold).
 *   - Enactment bridge: injecting `winner P X*` settles to `current P X*`.
 *   - The entity-veil: `says 1 (stake 3 W) ⊬ says 3 (money M)` in the backward
 *     prover (poss_l) — Alice's equity cannot reach C's assets (NI-1 shadow).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import G from '../../calculus/dill/lib/govern.js';

const DILL = path.join(import.meta.dirname, '..', '..', 'calculus', 'dill');
const prog = (rel) => path.join(DILL, rel);

describe('dill governance — eager in-logic threshold quorum (company buys cake)', () => {
  let calc, state;
  before(() => {
    calc = G.loadGovernance(prog('tests/forward/company_cake.ill'));
    const initial = G.initFrom(calc, 'expect_cake');
    state = calc.settle(initial, 0, { maxSteps: 10000 }).state;
  });
  const has = (view, pred, argPred) =>
    view.facts.some((f) => f.pred === 'poss' && f.args[0] === argPred &&
      typeof f.args[1] === 'object' && f.args[1].pred === pred);

  it('the cake lands at C (says 3 (cake 1))', () => {
    const view = G.extractGov(state);
    const cake = view.facts.find((f) => f.pred === 'poss' && f.args[0] === 3 &&
      typeof f.args[1] === 'object' && f.args[1].pred === 'cake');
    assert.ok(cake, 'expected says 3 (cake ...) in the settled state');
  });
  it('C keeps the change (says 3 (money 300))', () => {
    const view = G.extractGov(state);
    const money = view.facts.find((f) => f.pred === 'poss' && f.args[0] === 3 &&
      typeof f.args[1] === 'object' && f.args[1].pred === 'money');
    assert.ok(money, 'expected says 3 (money ...)');
    assert.equal(money.args[1].args[0], 300, 'change should be 1000 - 700 = 300');
  });
  it('the 50/50 cap table is untouched (Alice + Bob still hold stake 1/2 of C)', () => {
    const view = G.extractGov(state);
    const stakes = view.facts.filter((f) => f.pred === 'poss' &&
      typeof f.args[1] === 'object' && f.args[1].pred === 'stake' && f.args[1].args[0] === 3);
    assert.equal(stakes.length, 2, 'two shareholders hold C-stake');
    assert.ok(stakes.every((s) => s.args[1].args[1] === 0.5), 'each holds 1/2');
  });
});

describe('dill governance — lazy derived-view kernels (name the org)', () => {
  let view;
  const P = 100;
  before(() => {
    const calc = G.loadGovernance(prog('programs/name_the_org.ill'));
    const state = calc.settle(G.initFrom(calc, 'run'), 0, { maxSteps: 10000 }).state;
    view = G.extractGov(state);
  });

  it('extracts memhub O = (shares, votes, candidates)', () => {
    assert.equal(view.shares.length, 2);
    assert.equal(view.votes.length, 6);
    assert.equal(view.candidates.length, 3);
  });
  it('value() is the stake-weighted range pairing', () => {
    assert.equal(G.value(view, P, 10), 0.5);
    assert.equal(G.value(view, P, 20), 0.45);
    assert.equal(G.value(view, P, 30), 0.5);
  });
  it('argmax-oldest: 10 and 30 tie at .5 → oldest (seq 1) wins → 10', () => {
    const r = G.consensus(view, P, 'argmax-oldest');
    assert.equal(r.winner, 10);
    assert.equal(r.decided, true);
    assert.deepEqual(r.ranking.map((e) => e.x), [10, 30, 20]);
  });
  it('threshold: leader .5 clears .5 (decided) but not .6 (undecided)', () => {
    assert.equal(G.consensus(view, P, 'threshold', { threshold: 0.5 }).decided, true);
    assert.equal(G.consensus(view, P, 'threshold', { threshold: 0.5 }).winner, 10);
    assert.equal(G.consensus(view, P, 'threshold', { threshold: 0.6 }).decided, false);
  });
  it('n-of-set: every candidate has 2 approvers → 2-of-set passes, 3-of-set fails', () => {
    assert.equal(G.consensus(view, P, 'n-of-set', { n: 2 }).decided, true);
    assert.equal(G.consensus(view, P, 'n-of-set', { n: 3 }).decided, false);
  });
  it('priority: fixed agenda picks the first supported candidate', () => {
    assert.equal(G.consensus(view, P, 'priority', { order: [20, 30, 10] }).winner, 20);
    assert.equal(G.consensus(view, P, 'priority', { order: [30, 10] }).winner, 30);
  });
  it('time-locked: undecided before the deadline, decided after', () => {
    assert.equal(G.consensus(view, P, 'time-locked', { deadline: 10, now: 5 }).decided, false);
    assert.equal(G.consensus(view, P, 'time-locked', { deadline: 10, now: 10 }).winner, 10);
  });
  it('kernel A/B: same votes, different kernels → potentially different winners', () => {
    const a = G.consensus(view, P, 'argmax-oldest').winner;      // 10
    const b = G.consensus(view, P, 'priority', { order: [20] }).winner; // 20
    assert.notEqual(a, b);
  });
});

describe('dill governance — enactment bridge (winner → current)', () => {
  it('injecting winner P X* settles to current P X*', () => {
    const calc = G.loadGovernance(prog('programs/name_the_org.ill'));
    const base = calc.settle(G.initFrom(calc, 'run'), 0, { maxSteps: 10000 }).state;
    // 1. compute the winner as a read-time view
    const win = G.consensus(G.extractGov(base), 100, 'argmax-oldest').winner;
    assert.equal(win, 10);
    // 2. admin mints it, 3. the enact rule records it in `current`
    const minted = G.inject(base, `winner 100 ${win}`);
    const after = calc.settle(minted, 0, { maxSteps: 10000 }).state;
    const cur = G.extractGov(after).currents.find((c) => c.n === 100);
    assert.ok(cur, 'expected a current cell for proposal 100');
    assert.equal(cur.t, 10, 'current binding should be the winner (10)');
  });
});

describe('dill governance — the entity-veil (backward prover, poss_l)', () => {
  let fp, specs, alternatives, prover;
  before(async () => {
    const { loadDillSequent, dillCalculusConfig } = await import('../../calculus/dill/calculus-config.js');
    const calc = loadDillSequent();
    fp = dillCalculusConfig.loader.buildParser();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
  });
  const prove = (lin, succ) => prover.prove(
    Seq.fromArrays(lin.map(fp), [].map(fp), fp(succ)),
    { rules: specs, alternatives, maxDepth: 300, exhaustive: true });

  it('Alice cannot reach C: says 1 (stake 3 w) ⊬ says 3 (money m)', () => {
    assert.equal(prove(['says 1 (stake 3 w)'], 'says 3 (money m)').success, false);
  });
  it('but C can affirm from truth: money m ⊢ says 3 (money m)', () => {
    assert.equal(prove(['money m'], 'says 3 (money m)').success, true);
  });
});
