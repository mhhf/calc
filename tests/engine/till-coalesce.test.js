/**
 * Arrived-cohort coalescing (TODO_0277 approach 1) — coalesce.js.
 *
 * Pins:
 *   - exclusion derivation: stamp-binding patterns (A@Q) and before-window
 *     rules exclude their predicates; plain economies exclude nothing
 *   - observable equivalence: settle with coalesce reaches the same
 *     stamp-blind multiset as without, on deterministic scenarios
 *   - arrived facts land on the unit stamp; live-entry count shrinks
 *   - spoilage stays exact: food cohorts keep their stamps, spoil fires
 *     at Q+window identically (B4 of the 0277 spec)
 *   - composability survives coalescing (bag-level, deterministic runs)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { stampObservers } from '../../lib/timed/coalesce.js';
import { buildTimedConfig } from '../../lib/timed/timed.js';
import { ratParts } from '../../lib/kernel/rat-term.js';
import { tillCalculusConfig } from '../../calculus/till/calculus-config.js';
import { SPEC, FIX, loadTill as load, initQuery as init, bagStr, stamped, traceKey } from './till-helpers.js';

const tcfg = () => buildTimedConfig(tillCalculusConfig);

describe('coalesce — exclusion derivation (stampObservers)', () => {
  it('economy.ill observes no stamps: empty exclusion set', () => {
    const calc = load(SPEC('economy.ill'));
    const obs = stampObservers(calc.forwardRules, tcfg());
    assert.equal(obs.all, false);
    assert.deepEqual([...obs.preds], []);
  });

  it('spoilage.ill: food excluded (stamp-binding food@Q + before-window bakery)', () => {
    const calc = load(SPEC('spoilage.ill'));
    const obs = stampObservers(calc.forwardRules, tcfg());
    assert.equal(obs.all, false);
    assert.ok(obs.preds.has('food'), 'food must be stamp-load-bearing');
    // the before-window bakery rule also pins its OTHER antecedents
    assert.ok(obs.preds.has('bakery'), 'before-window rules exclude all their patterns');
  });
});

describe('coalesce — observable equivalence (deterministic scenarios)', () => {
  const cases = [
    ['economy.ill', 'expect_economy', '1'],
    ['economy.ill', 'expect_settled', '100'],
    ['grades.ill', 'expect_whole_cohort', '20'],
    ['grades.ill', 'expect_split_spread', '5'],
    ['read.ill', 'expect_atomic', '10'],
  ];
  for (const [file, kind, T] of cases) {
    it(`${file} ${kind}: bag-identical with and without coalesce`, () => {
      const calc = load(SPEC(file));
      const S = init(calc, kind);
      const plain = calc.settle(S, T);
      const coal = calc.settle(S, T, { coalesce: true });
      assert.equal(bagStr(coal.state), bagStr(plain.state));
      assert.equal(coal.events.length, plain.events.length);
    });
  }

  it('economy settled at 100: arrived facts coalesce onto the unit stamp', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const coal = calc.settle(S, '100', { coalesce: true }).state;
    for (const key of Object.keys(stamped(coal))) {
      assert.match(key, /@0$/, `arrived fact not on unit stamp: ${key}`);
    }
    const plain = calc.settle(S, '100').state;
    assert.ok(Object.keys(coal.linear).length <= Object.keys(plain.linear).length);
  });
});

describe('coalesce — spoilage exactness (0277 B4)', () => {
  for (const kind of ['expect_eaten_not_rotten', 'expect_fresh_only', 'expect_rots_at_two', 'expect_fifo']) {
    it(`${kind}: trace-identical with coalesce on`, () => {
      const calc = load(SPEC('spoilage.ill'));
      assert.ok(calc.splitQueries.has(kind), `spec kind missing: ${kind}`);
      const S = init(calc, kind);
      const T = '10';
      const plain = calc.settle(S, T);
      const coal = calc.settle(S, T, { coalesce: true });
      assert.equal(traceKey(coal.events), traceKey(plain.events));
      // food cohorts keep their exact stamps (excluded pred)
      const fp = Object.entries(stamped(plain.state)).filter(([k]) => k.startsWith('food@'));
      const fc = Object.entries(stamped(coal.state)).filter(([k]) => k.startsWith('food@'));
      assert.deepEqual(fc.sort(), fp.sort());
    });
  }
});

describe('coalesce — menu alternatives are durable observers (soundness audit)', () => {
  it('a stamp-matching menu alternative excludes its predicate before projection', () => {
    const calc = load(FIX('till-menu-observer.ill'));
    const S = init(calc, 'expect_menu_observer');
    const r = calc.settle(S, '10', { coalesce: true });
    const keys = Object.keys(stamped(r.state));
    // wood is observed by the (unprojected) menu alternative — stamps kept
    assert.ok(keys.includes('wood@2') && keys.includes('wood@3'),
      `wood cohorts must survive coalescing: ${keys.join(', ')}`);
    // iron is observed by nothing — coalesces onto the unit stamp
    assert.ok(keys.includes('iron@0') && !keys.includes('iron@1') && !keys.includes('iron@4'),
      `iron must coalesce: ${keys.join(', ')}`);
  });

  it('projecting the alternative after coalesced settling still fires on wood@2', () => {
    const calc = load(FIX('till-menu-observer.ill'));
    const S = init(calc, 'expect_menu_observer');
    const r = calc.settle(S, '10', { coalesce: true });
    let menu = null;
    for (const hStr in r.state.persistent) {
      if (Store.tag(Number(hStr)) === 'with') menu = Number(hStr);
    }
    assert.ok(menu !== null, 'standing menu present');
    const chosen = calc.choose(r.state, menu, 0, { at: '10' });
    const done = calc.settle(chosen, '10', { coalesce: true });
    assert.ok(Object.keys(stamped(done.state)).some(k => k.startsWith('plank@')),
      'projected rule must fire against the preserved wood@2 cohort');
  });
});

describe('coalesce — persistent-consequent menus are durable observers (audit)', () => {
  it('the exclusion derivation sees a menu inside alt.persistent', () => {
    // The audit found contribOf walked alt.linear only — a persistent
    // produced menu (`!( ... & ... )`) evaded the durable exclusion.
    const calc = load(FIX('till-menu-producer.ill'));
    const obs = stampObservers(calc.forwardRules, tcfg());
    assert.equal(obs.all, false);
    assert.ok(obs.preds.has('wood'), 'wood (before-window menu cost) must be excluded');
    assert.ok(!obs.preds.has('iron'), 'iron observed by nothing');
    assert.ok(obs.hasBefore && obs.hasWindow, 'formula-level window flags must surface');
  });

  it('wood stamps survive a coalesce while the menu producer is still pending', () => {
    // trigger@4: at settle(3) the menu does NOT exist yet — only the
    // durable consequent walk can keep wood's stamps.
    const calc = load(FIX('till-menu-producer.ill'));
    const S = init(calc, 'expect_menu_producer');
    const r = calc.settle(S, '3', { coalesce: true });
    const keys = Object.keys(stamped(r.state));
    assert.equal(r.events.length, 0, 'producer must still be pending');
    assert.ok(keys.includes('wood@2') && keys.includes('wood@3'),
      `wood cohorts must survive pre-production coalescing: ${keys.join(', ')}`);
    assert.ok(keys.includes('iron@0') && !keys.includes('iron@1'),
      `iron must still coalesce: ${keys.join(', ')}`);
  });
});

describe('rebase — translation of the time origin (0277 B3)', () => {
  it('chained rebased settles reach the same stamp-blind state as direct', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const direct = calc.settle(S, '100', { coalesce: true }).state;
    // settle to 40, rebase, then continue in the shifted frame
    const r1 = calc.settle(S, '40', { coalesce: true, rebase: true });
    const [n, d] = ratParts(r1.rebase);
    assert.equal(d, 1n, 'economy rebase lands on an integer stamp');
    const rest = 100 - Number(n);
    const r2 = calc.settle(r1.state, String(rest), { coalesce: true });
    assert.equal(bagStr(r2.state), bagStr(direct));
  });

  it('rebase without coalesce is a loud error', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    assert.throws(() => calc.settle(S, '10', { rebase: true }), /rebase requires coalesce/);
  });
});

describe('coalesce — composability (E5, bag level)', () => {
  it('settle(settle(S,T1,c),T2,c) ≡ settle(S,T2,c) on the economy', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const direct = calc.settle(S, '100', { coalesce: true }).state;
    for (const t1 of ['0', '1/2', '1', '10']) {
      const mid = calc.settle(S, t1, { coalesce: true }).state;
      const resumed = calc.settle(mid, '100', { coalesce: true }).state;
      assert.equal(bagStr(resumed), bagStr(direct), `split at ${t1}`);
    }
  });
});
