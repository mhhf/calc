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
import { gradeW } from '../../lib/engine/grades.js';
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

  // ── Standing menus: !(A & B) in the persistent zone ────────────────
  // Seely: !(A & B) ≅ !A ⊗ !B — a persistent menu is an UNLIMITED supply
  // of its alternatives. choose projects WITHOUT consuming: any
  // alternative, any number of times, at any moment. Sub-menus are
  // bang-wrapped alternatives — projecting one ADDS the sub-menu to the
  // persistent zone (click-through navigation / menu unlocking).

  const standingMenu = () =>
    Store.put('with', [atom('act_a'), Store.put('with', [atom('act_b'), atom('act_c')])]);
  const standingState = () => ({ linear: {}, persistent: { [standingMenu()]: true } });

  it('standing menu: projection does not consume — repeat clicks work', () => {
    let s = calc.choose(standingState(), standingMenu(), 0, { at: '2' });
    s = calc.choose(s, standingMenu(), 0, { at: '2' });     // click build farm again
    s = calc.choose(s, standingMenu(), 1, { at: '2' });     // then right away act_b
    assert.equal(stampedStr(s), 'act_a@2x2,act_b@2x1');
    assert.ok(s.persistent[standingMenu()], 'menu still standing');
    assert.equal(stampedStr(calc.settle(s, '10').state), 'done_a@2x2,done_b@2x1');
  });

  it('standing menu: default stamp is the unit; at sets the decision time', () => {
    const s = calc.choose(standingState(), standingMenu(), 2);
    assert.equal(stampedStr(s), 'act_c@0x1');
  });

  it('sub-menu alternative (!(…)) lands in the persistent zone — click-through', () => {
    const sub = Store.put('with', [atom('act_b'), atom('act_c')]);
    const main = Store.put('with', [atom('act_a'), Store.put('bang', [gradeW(), sub])]);
    const s0 = { linear: {}, persistent: { [main]: true } };
    const s1 = calc.choose(s0, main, 1, { at: '3' });        // open the sub-menu
    assert.ok(s1.persistent[sub], 'sub-menu now visible');
    assert.ok(s1.persistent[main], 'main menu still standing');
    assert.equal(stampedStr(s1), '');                        // nothing linear yet
    const s2 = calc.choose(s1, sub, 0, { at: '4' });         // choose inside it
    assert.equal(stampedStr(s2), 'act_b@4x1');
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
