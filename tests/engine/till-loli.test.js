/**
 * Timed possessed rules — loli facts as one-shot match sources (Phase 6c).
 *
 * The untimed engine has run state-resident lolis since the CLF/Celf
 * divergence (lnl/loli.js); this suite pins the TIMED semantics:
 *   - a loli fact fires like a rule: inputs matched, delay read from its
 *     stored {..}@d monad, consumed on firing (one-shot by linearity)
 *   - its own stamp joins the activation max (no use before it exists),
 *     entering tryTimedMatch as the BASE activation so before-windows and
 *     B&B pruning stay sound
 *   - plan semantics: a possessed rule waits for its inputs
 *   - rules can PRODUCE possessed rules (the fire() guard is gone)
 *   - determinism: seeded replay; dirty ≡ rescan trace-identical;
 *     horizon-split composability; exec outcome ∈ explore leaves
 *   - fences: non-ground lolis are loudly rejected (v1)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { FIX, loadTill as load, initQuery as init, atom, stamped, stampedStr, bagStr } from './till-helpers.js';

describe('timed possessed rules (loli facts)', () => {
  let calc;
  before(() => { calc = load(FIX('till-loli-timed.ill')); });
  const S = (kind) => init(calc, kind);

  it('fires with the stored delay; consumed on firing (one-shot)', () => {
    const r = calc.settle(S('expect_basic'), '10');
    assert.equal(stampedStr(r.state), 'farmz@3x1');
    assert.equal(r.events.length, 1);
    assert.match(r.events[0].rule, /^loli:/);
  });

  it('plan semantics: waits for inputs produced later', () => {
    assert.equal(stampedStr(calc.settle(S('expect_plan'), '10').state), 'farmz@5x1');
    // pending before the inputs exist
    assert.equal(stampedStr(calc.settle(S('expect_waiting'), '1').state),
      'loli@0x1,spc@2x2');
  });

  it('the loli stamp joins the activation max', () => {
    assert.equal(stampedStr(calc.settle(S('expect_stamp_join'), '10').state), 'relic@4x1');
  });

  it('one-shot: surplus resources survive; two copies fire twice', () => {
    assert.equal(stampedStr(calc.settle(S('expect_one_shot'), '10').state),
      'farmz@3x1,spc@0x2');
    assert.equal(stampedStr(calc.settle(S('expect_two_copies'), '10').state),
      'farmz@3x2');
  });

  it('rules produce possessed rules; ground windows work inside them', () => {
    assert.equal(stampedStr(calc.settle(S('expect_produced_rule'), '10').state), 'relic@1x1');
    assert.equal(stampedStr(calc.settle(S('expect_ground_window'), '10').state), 'opened@5x1');
  });

  it('composability: settle(settle(S,T1),T2) ≡ settle(S,T2) across the plan', () => {
    const direct = stampedStr(calc.settle(S('expect_plan'), '10').state);
    for (const t1 of ['0', '1', '2', '3', '5']) {
      const mid = calc.settle(S('expect_plan'), t1).state;
      assert.equal(stampedStr(calc.settle(mid, '10').state), direct, `split at ${t1}`);
    }
  });

  it('dirty ≡ rescan: trace-identical on loli programs', () => {
    for (const kind of ['expect_plan', 'expect_two_copies', 'expect_produced_rule']) {
      const a = calc.settle(S(kind), '10', { scheduler: 'rescan' });
      const b = calc.settle(S(kind), '10', { scheduler: 'dirty' });
      assert.deepEqual(
        b.events.map(e => `${e.rule}@${e.activation}`),
        a.events.map(e => `${e.rule}@${e.activation}`), kind);
      assert.equal(stampedStr(b.state), stampedStr(a.state), kind);
    }
  });

  it('seeded replay: identical traces per seed', () => {
    for (const seed of [0, 7]) {
      const a = calc.settle(S('expect_two_copies'), '10', { seed });
      const b = calc.settle(S('expect_two_copies'), '10', { seed });
      assert.deepEqual(a.events.map(e => e.rule), b.events.map(e => e.rule));
    }
  });

  it('exec outcome is an explore leaf', () => {
    for (const kind of ['expect_basic', 'expect_plan', 'expect_two_copies']) {
      const out = stampedStr(calc.settle(S(kind), '10').state);
      const leaves = getAllLeaves(calc.settleExplore(S(kind), '10').tree)
        .map(l => stampedStr(l.state));
      assert.ok(leaves.includes(out), `${kind}: ${out} ∉ ${leaves.join(' | ')}`);
    }
  });

  it('non-ground loli facts are loudly rejected (v1 fence)', () => {
    const w = Store.put('metavar', ['W']);
    const badLoli = Store.put('loli', [
      Store.put('pv', [w]), Store.put('gmonad', [Store.put1('binlit', 0n), Store.put('qv', [w])]),
    ]);
    const st = { linear: { [badLoli]: 1, [Store.put('pv', [atom('x')])]: 1 }, persistent: {} };
    assert.throws(() => calc.settle(st, '10'), /ground/);
  });
});
