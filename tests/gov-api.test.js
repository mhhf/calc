/**
 * gov-api — the governance sandbox server (TODO_0318 S0).
 *
 * Exercises handleGov end-to-end: a live State per session, admin/actor verbs,
 * and role-scoping AS non-interference (an actor confined to its own says-zone).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import { handleGov } from '../src/server/gov-api.js';

describe('gov-api — name-the-org session (kernels, consensus, enact)', () => {
  let id;
  before(async () => {
    const r = await handleGov('start', { program: 'calculus/dill/programs/name_the_org.ill', query: 'run' });
    assert.equal(r.ok, true);
    id = r.id;
  });

  it('start exposes memhub O + the argmax consensus', async () => {
    const r = await handleGov('state', { id });
    assert.equal(r.view.candidates.length, 3);
    assert.equal(r.view.votes.length, 6);
    assert.equal(r.view.consensus[100].winner, 10);
  });

  it('consensus verb: argmax-oldest → 10', async () => {
    const r = await handleGov('consensus', { id, p: 100, kernel: 'argmax-oldest' });
    assert.equal(r.result.winner, 10);
  });

  it('kernel A/B: priority order [20] → 20 (differs from argmax 10)', async () => {
    const r = await handleGov('consensus', { id, p: 100, kernel: 'priority', kernelParams: { order: [20] } });
    assert.equal(r.result.winner, 20);
  });

  it('enact mints the winner into the current cell', async () => {
    const r = await handleGov('enact', { id, p: 100 });
    assert.equal(r.ok, true);
    assert.equal(r.winner, 10);
    const cur = r.view.currents.find((c) => c.n === 100);
    assert.ok(cur && cur.t === 10);
  });

  it('fork isolates state: enact on the fork does not touch the origin', async () => {
    const f = await handleGov('fork', { id });
    const forkId = f.id;
    await handleGov('kernel', { id: forkId, kernel: 'priority', kernelParams: { order: [30] } });
    const fr = await handleGov('enact', { id: forkId, p: 100 });
    assert.equal(fr.winner, 30);
    // origin still shows argmax winner in its consensus view
    const orig = await handleGov('consensus', { id, p: 100, kernel: 'argmax-oldest' });
    assert.equal(orig.result.winner, 10);
  });
});

describe('gov-api — role-scoping IS non-interference (NI-1)', () => {
  let id;
  before(async () => {
    const r = await handleGov('start', { program: 'calculus/dill/prelude/governance.ill' });
    id = r.id;
  });

  it('actor 1 may inject its own says-zone', async () => {
    const r = await handleGov('inject', { id, role: 1, fact: 'says 1 (stake 3 (1/2))' });
    assert.equal(r.ok, true);
    assert.ok(r.view.zones[1] && r.view.zones[1].some((s) => s.includes('stake')));
  });

  it('actor 1 may NOT inject into C-s zone (says 3 ...)', async () => {
    const r = await handleGov('inject', { id, role: 1, fact: 'says 3 (money 999)' });
    assert.equal(r.ok, false);
    assert.match(r.error, /NI-1|poss_l|only inject/);
  });

  it('admin may mint any zone', async () => {
    const r = await handleGov('inject', { id, role: 'admin', fact: 'says 3 (money 1000)' });
    assert.equal(r.ok, true);
    assert.ok(r.view.zones[3] && r.view.zones[3].some((s) => s.includes('money')));
  });

  it('only admin may retract', async () => {
    const bad = await handleGov('retract', { id, role: 2, fact: 'says 3 (money 1000)' });
    assert.equal(bad.ok, false);
    const ok = await handleGov('retract', { id, role: 'admin', fact: 'says 3 (money 1000)' });
    assert.equal(ok.ok, true);
  });
});

describe('gov-api — company buys cake, settled server-side', () => {
  it('the quorum choreography settles to a cake at C', async () => {
    const r = await handleGov('start', { program: 'calculus/dill/tests/forward/company_cake.ill', query: 'expect_cake' });
    assert.equal(r.ok, true);
    const cake = r.view.rows.find((row) => row.text.includes('cake'));
    assert.ok(cake, 'expected a cake fact in the settled state');
    assert.ok(r.view.zones[3] && r.view.zones[3].some((s) => s.includes('cake')));
  });
});

describe('gov-api — the entity-veil as a backward query', () => {
  let id;
  before(async () => { id = (await handleGov('start', { program: 'calculus/dill/prelude/governance.ill' })).id; });

  it('says 1 (stake 3 w) ⊬ says 3 (money m) — Alice cannot reach C', async () => {
    const r = await handleGov('query', { id, sequent: 'says 1 (stake 3 w) |- says 3 (money m)' });
    assert.equal(r.provable, false);
  });
  it('money m ⊢ says 3 (money m) — C can affirm from truth', async () => {
    const r = await handleGov('query', { id, sequent: 'money m |- says 3 (money m)' });
    assert.equal(r.provable, true);
  });
});
