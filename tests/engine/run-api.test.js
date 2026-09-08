/**
 * run-api tests (TODO_0308 P3) — the server-side execution backend behind
 * the book's interactive widgets. Exercises all five routes against real
 * repo programs and pins the security fences.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { handleRun } from '../../src/server/run-api.js';

describe('run-api exec', () => {
  it('traces debug-demo to quiescence with consumed/produced diffs', async () => {
    const r = await handleRun('exec', {
      calculus: 'ill',
      file: 'calculus/ill/tests/forward/debug-demo.ill',
      maxSteps: 20,
    });
    assert.equal(r.ok, true, r.error);
    assert.ok(r.initial.some(f => f.startsWith('pc(')), 'initial has pc');
    assert.ok(r.steps.length >= 1);
    const s = r.steps[0];
    assert.equal(typeof s.rule, 'string');
    assert.ok(Array.isArray(s.consumed) && Array.isArray(s.produced) && Array.isArray(s.state));
    assert.equal(r.quiescent, true);
  });

  it('rejects files outside the whitelist', async () => {
    for (const file of ['../etc/passwd', 'server.js', 'lib/engine/index.js', 'calculus/../server.js']) {
      const r = await handleRun('exec', { calculus: 'ill', file });
      assert.equal(r.ok, false, `expected rejection for ${file}`);
    }
  });

  it('runs inline source', async () => {
    const r = await handleRun('exec', {
      calculus: 'ill',
      source: [
        'a: type.', 'b: type.', 'c: type.',
        'step1: a -o { b }.',
        'step2: b -o { c }.',
        '#expect_go a => c .',
      ].join('\n'),
      maxSteps: 10,
    });
    assert.equal(r.ok, true, r.error);
    assert.equal(r.steps.length, 2);
    assert.deepEqual(r.final, ['c']);
    assert.equal(r.quiescent, true);
  });
});

describe('run-api game', () => {
  it('start → choose (costed, cuts) → settle lands the job', async () => {
    const v = await handleRun('game/start', {
      calculus: 'till',
      file: 'tests/fixtures/till-shell-smoke.ill',
      init: 'expect_start',
    });
    assert.equal(v.ok, true, v.error);
    assert.ok(v.id);
    assert.equal(v.menus.length, 1);
    assert.equal(v.menus[0].alts.length, 2);
    assert.equal(v.menus[0].alts[0].enabled, true);

    const v2 = await handleRun('game/act', { id: v.id, action: 'choose', t: 1, menuIndex: 0, altIndex: 0 });
    assert.equal(v2.ok, true, v2.error);
    assert.ok(v2.pending.some(p => p.includes('farm_s')), `farm in flight: ${JSON.stringify(v2.pending)}`);

    const v3 = await handleRun('game/act', { id: v.id, action: 'settle', t: 5 });
    assert.ok(v3.state.some(s => s.text === 'farm_s'), 'farm landed');

    const end = await handleRun('game/act', { id: v.id, action: 'end' });
    assert.equal(end.ok, true);
  });

  it('unknown session errors cleanly', async () => {
    const r = await handleRun('game/act', { id: 'nope', action: 'settle', t: 1 });
    assert.equal(r.ok, false);
  });
});

describe('run-api collapse', () => {
  it('WFC start shows 4 waves; auto collapses to ground; restart resets', async () => {
    const v = await handleRun('collapse/start', {
      calculus: 'will',
      file: 'calculus/will/game/WFC.will',
      seed: 3,
    });
    assert.equal(v.ok, true, v.error);
    assert.equal(v.waves.length, 4);
    assert.ok(v.waves[0].members.length >= 2);
    assert.ok(typeof v.waves[0].entropy === 'number');

    const v2 = await handleRun('collapse/act', { id: v.id, action: 'auto' });
    assert.equal(v2.ok, true, v2.error);
    assert.equal(v2.done, true);
    assert.equal(v2.contradiction, false);
    assert.equal(v2.drawn.length, 4);
    assert.equal(v2.state.filter(s => s.startsWith('tile(')).length, 4);

    const v3 = await handleRun('collapse/act', { id: v.id, action: 'restart' });
    assert.equal(v3.waves.length, 4);
    assert.equal(v3.attempts, 2);
    assert.equal(v3.drawn.length, 0);
  });
});

describe('run-api fences', () => {
  it('unknown route and calculus error cleanly', async () => {
    assert.equal((await handleRun('nope', {})).ok, false);
    assert.equal((await handleRun('exec', { calculus: 'zill', file: 'calculus/ill/tests/forward/debug-demo.ill' })).ok, false);
  });
});
