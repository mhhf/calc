/**
 * External choice as with-projection — TODO_0265 Phase 6 (Denis's model):
 * a forward rule OFFERS a menu `A & B & …` as ONE inert linear fact; the
 * ENVIRONMENT (player/host) collapses it via calc.choose(state, h, i, {at})
 * — the engine never resolves external choice itself, and the host can only
 * choose among alternatives the game actually offered (no token injection).
 *
 * Pins:
 *   - a & consequent compiles to one inert fact; settle is quiescent on it
 *   - choose projects the i-th alternative at stamp max(menu stamp, at)
 *   - the chosen alternative decomposes like a fired consequent
 *     (tensor bundle, !_k counted parcel)
 *   - settle → choose → settle chains (the interactive loop)
 *   - loud errors: bad index, absent fact, non-menu fact
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { FIX, loadTill as load, atom, stamped, stampedStr } from './till-helpers.js';

const menuKey = (state) => Number(Object.keys(state.linear).find(h => {
  let x = Number(h);
  if (Store.tag(x) === 'at') x = Store.child(x, 0);
  return Store.tag(x) === 'with';
}));

describe('till external choice — offer and collapse (Phase 6)', () => {
  let calc, offered;
  before(() => {
    calc = load(FIX('till-menu.ill'));
    offered = calc.settle({ linear: { [atom('player')]: 1 }, persistent: {} }, '10');
  });

  it('the menu is ONE inert fact: settle offers it and goes quiescent', () => {
    assert.ok(offered.quiescent);
    assert.equal(Object.keys(offered.state.linear).length, 1);
    const key = menuKey(offered.state);
    assert.equal(Store.tag(key), 'at');
    assert.equal(Store.tag(Store.child(key, 0)), 'with');
    // stamped at the rule's delay
    assert.deepEqual(stamped(offered.state), { 'with@5': 1 });
  });

  it('choose(0): plain alternative, stamped at the menu stamp by default', () => {
    const s1 = calc.choose(offered.state, menuKey(offered.state), 0);
    assert.equal(stampedStr(s1), 'act_a@5x1');
    assert.equal(stampedStr(calc.settle(s1, '10').state), 'done_a@5x1');
  });

  it('choose at a later decision time: stamp is max(menu, at)', () => {
    const s1 = calc.choose(offered.state, menuKey(offered.state), 0, { at: '9' });
    assert.equal(stampedStr(s1), 'act_a@9x1');
    // an earlier at clamps to the menu stamp (no decisions before the offer)
    const s2 = calc.choose(offered.state, menuKey(offered.state), 0, { at: '3' });
    assert.equal(stampedStr(s2), 'act_a@5x1');
  });

  it('choose(1): a tensor bundle decomposes into its components', () => {
    const s1 = calc.choose(offered.state, menuKey(offered.state), 1);
    assert.equal(stampedStr(s1), 'act_b@5x2');
    assert.equal(stampedStr(calc.settle(s1, '10').state), 'done_b@5x2');
  });

  it('choose(2): a counted parcel yields k copies', () => {
    const s1 = calc.choose(offered.state, menuKey(offered.state), 2);
    assert.equal(stampedStr(s1), 'act_c@5x3');
    assert.equal(stampedStr(calc.settle(s1, '10').state), 'done_c@6x3');
  });

  it('the interactive loop: settle → choose → settle ≡ played trace', () => {
    // full loop from the raw initial state, deciding at t = 7
    const mid = calc.settle({ linear: { [atom('player')]: 1 }, persistent: {} }, '7');
    const chosen = calc.choose(mid.state, menuKey(mid.state), 0, { at: '7' });
    assert.equal(stampedStr(calc.settle(chosen, '20').state), 'done_a@7x1');
  });

  it('input state is not mutated', () => {
    const before = stampedStr(offered.state);
    calc.choose(offered.state, menuKey(offered.state), 1);
    assert.equal(stampedStr(offered.state), before);
  });

  it('loud errors: bad index, absent fact, non-menu fact', () => {
    const key = menuKey(offered.state);
    assert.throws(() => calc.choose(offered.state, key, 3), /out of range/);
    assert.throws(() => calc.choose(offered.state, key, -1), /out of range/);
    assert.throws(() => calc.choose(offered.state, atom('ghost'), 0), /not present/);
    const s = { linear: { [atom('player')]: 1 }, persistent: {} };
    assert.throws(() => calc.choose(s, atom('player'), 0), /not an external choice/);
  });
});
