/**
 * till timed scheduler — TODO_0265 Phase 4 acceptance.
 *
 * settle/nextActivation/settleExplore + views over the real till calculus
 * (calculus/till/calculus-config.js), driven by the executable specs and
 * dedicated fixtures. Pins:
 *   - composability law: settle(settle(S,T₁),T₂) ≡ settle(S,T₂) (E5)
 *   - scheduler equivalence: dirty tracking ≡ rescan, trace-identical (P3/D13)
 *   - conflict chooser: PRF reproducibility, deterministic, custom fn (P5/D17)
 *   - explore branches ONLY on genuine conflicts; reads never conflict (E7.2)
 *   - cohort samplers: fifo vs lifo observable difference (D12)
 *   - delay terms: @D from a !qdiv goal, FFI on ≡ off (E7.1 + FFI principle)
 *   - untimed-engine guards: windows/counts/delays loudly rejected
 *   - Zeno guard (D16); oracle differential (tools/till-oracle.mjs)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import convert from '../../lib/engine/convert.js';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import { timedSubset, timedExact } from '../../lib/engine/timed.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';
import { SPEC, FIX, loadTill as load, initQuery as init, stamped, bagStr } from './till-helpers.js';

describe('till settle — composability and horizons (E5)', () => {
  let calc, S;
  before(() => { calc = load(SPEC('schedule.ill')); S = init(calc, 'expect_two_jobs'); });

  it('settle(settle(S,T1),T2) ≡ settle(S,T2) over horizon splits', () => {
    const direct = calc.settle(S, '1').state;
    for (const t1 of ['0', '0.4', '1/2', '0.7', '1']) {
      const mid = calc.settle(S, t1).state;
      const resumed = calc.settle(mid, '1').state;
      assert.deepEqual(stamped(resumed), stamped(direct), `split at ${t1}`);
    }
  });

  it('idempotence: settle(settle(S,T),T) ≡ settle(S,T)', () => {
    const once = calc.settle(S, '0.4').state;
    assert.deepEqual(stamped(calc.settle(once, '0.4').state), stamped(once));
  });

  it('result.next reports the earliest pending activation beyond the horizon', () => {
    const res = calc.settle(S, '0.4');
    assert.deepEqual(ratParts(res.next), [1n, 2n]);   // job2 activates at 1/2
    assert.equal(calc.settle(S, '1').next, null);      // fully settled
  });

  it('nextActivation peeks without firing', () => {
    assert.deepEqual(ratParts(calc.nextActivation(S)), [0n, 1n]);
    const mid = calc.settle(S, '0').state;
    assert.deepEqual(ratParts(calc.nextActivation(mid)), [1n, 2n]);
  });
});

describe('till schedulers — dirty tracking ≡ rescan (P3, the D13 gate)', () => {
  const scenarios = [
    ['schedule.ill', 'expect_two_jobs', '1'],
    ['spoilage.ill', 'expect_eaten_not_rotten', '5'],
    ['spoilage.ill', 'expect_fresh_only', '10'],
    ['grades.ill', 'expect_whole_cohort', '20'],
    ['read.ill', 'expect_atomic', '10'],
  ];
  for (const [file, kind, T] of scenarios) {
    it(`${file} ${kind}: trace-identical`, () => {
      const calc = load(SPEC(file));
      const S = init(calc, kind);
      const a = calc.settle(S, T);
      const b = calc.settle(S, T, { scheduler: 'dirty' });
      const key = (e) => `${e.rule}@${ratParts(e.activation).join('/')}`;
      assert.deepEqual(b.events.map(key), a.events.map(key));
      assert.deepEqual(stamped(b.state), stamped(a.state));
    });
  }
});

describe('till conflict chooser (P5/D17)', () => {
  let calc, one;
  before(() => {
    calc = load(FIX('till-conflict.ill'));
    one = { linear: { [Store.put('atom', ['coin'])]: 1 }, persistent: {} };
  });

  it('same seed ⇒ same winner (stateless PRF, replay-identical)', () => {
    const w1 = calc.settle(one, '0', { seed: 7 }).events[0].rule;
    const w2 = calc.settle(one, '0', { seed: 7 }).events[0].rule;
    assert.equal(w1, w2);
  });

  it('both outcomes reachable across seeds (it IS a choice)', () => {
    const winners = new Set();
    for (let s = 0; s < 32; s++) winners.add(calc.settle(one, '0', { seed: s }).events[0].rule);
    assert.deepEqual([...winners].sort(), ['grab_a', 'grab_b']);
  });

  it('deterministic chooser picks the canonical first', () => {
    const w = calc.settle(one, '0', { chooser: 'deterministic' }).events[0].rule;
    assert.equal(w, calc.settle(one, '0', { chooser: 'deterministic' }).events[0].rule);
  });

  it('custom chooser function is honored', () => {
    const pickB = (tied) => tied.find(m => m.rule.name === 'grab_b');
    assert.equal(calc.settle(one, '0', { chooser: pickB }).events[0].rule, 'grab_b');
  });

  it('PRF golden pins: exact winner per seed (round-13 residue i)', () => {
    // Pins the concrete PRF draw, not just reproducibility — a _mix32/
    // _thetaHash/store-hashing change re-samples every trace and ONLY this
    // test notices. On such a change: verify intent, then re-pin. (The PRF
    // mixes state.stateHash = arena-layout dependent — values are stable
    // for THIS file's load order only; re-pin if earlier tests change.
    // node-only: bun's module evaluation interns in a different order.)
    if (typeof Bun !== 'undefined') return;
    // Re-pinned (Phase 6): bin.ill gained min/max clauses → interning shift.
    assert.deepEqual(
      [0, 7, 42].map(seed => calc.settle(one, '0', { seed }).events[0].rule),
      ['grab_b', 'grab_a', 'grab_a']);
  });
});

describe('till explore — branch only on genuine conflicts (Phase 4)', () => {
  let calc;
  const coin = Store.put('atom', ['coin']);
  before(() => { calc = load(FIX('till-conflict.ill')); });

  it('one coin, two grabbers: genuine conflict ⇒ two leaves', () => {
    const { tree, leaves } = calc.settleExplore({ linear: { [coin]: 1 }, persistent: {} }, '0');
    assert.equal(tree.type, 'conflict');
    assert.equal(leaves.length, 2);
    const outcomes = leaves.map(l => Object.keys(stamped(l.state)).sort().join(','));
    assert.deepEqual(outcomes.sort(), ['got_a@0', 'got_b@0']);
  });

  it('two coins: shared cohort ⇒ all chooser-reachable outcomes (2a / ab / 2b)', () => {
    const { leaves } = calc.settleExplore({ linear: { [coin]: 2 }, persistent: {} }, '0');
    const canon = (m) => Object.entries(m).sort().map(([k, v]) => `${k}x${v}`).join(',');
    const distinct = new Set(leaves.map(l => canon(stamped(l.state))));
    assert.deepEqual([...distinct].sort(),
      ['got_a@0x1,got_b@0x1', 'got_a@0x2', 'got_b@0x2']);
  });

  it('disjoint tied set is independent ⇒ ONE leaf (partial-order reduction)', () => {
    const tx = Store.put('atom', ['tok_x']);
    const ty = Store.put('atom', ['tok_y']);
    const { tree, leaves } = calc.settleExplore({ linear: { [tx]: 1, [ty]: 1 }, persistent: {} }, '0');
    assert.equal(tree.type, 'leaf');
    assert.equal(leaves.length, 1);
    assert.deepEqual(stamped(leaves[0].state), { 'got_x@0': 1, 'got_y@0': 1 });
  });

  it('concurrent reads never conflict (E7.2): one leaf', () => {
    const rcalc = load(SPEC('read.ill'));
    const S = init(rcalc, 'expect_concurrent_reads');   // 2 choppers, 2 trees, 1 manual
    const { leaves } = rcalc.settleExplore(S, '0');
    assert.equal(leaves.length, 1);
  });

  it('read starvation: consumer vs reader of the last copy ⇒ conflict node (round-13 residue iv)', () => {
    // look: read t * probe -o {seen}.  take: t -o {gone}.  One t: take-first
    // starves the read ({gone, probe}); look-first preserves t ({seen, gone}).
    const rcalc = load(FIX('till-read-starve.ill'));
    const S = { linear: { [Store.put('atom', ['t'])]: 1, [Store.put('atom', ['probe'])]: 1 }, persistent: {} };
    const { tree, leaves } = rcalc.settleExplore(S, '0');
    assert.equal(tree.type, 'conflict');
    const outcomes = leaves.map(l => Object.keys(stamped(l.state)).sort().join(',')).sort();
    assert.deepEqual(outcomes, ['gone@0,probe@0', 'gone@0,seen@0']);
  });

  it('explore leaves agree with exec on conflict-free programs (confluence)', () => {
    const scalc = load(SPEC('schedule.ill'));
    const S = init(scalc, 'expect_two_jobs');
    const { leaves } = scalc.settleExplore(S, '1');
    assert.equal(leaves.length, 1);
    assert.deepEqual(stamped(leaves[0].state), stamped(scalc.settle(S, '1').state));
  });
});

describe('till cohort samplers (D12)', () => {
  it('min-activation dominates the sampler: lifo still takes the older food when it fires earlier', () => {
    // meal_order@0: a(food@0)=0 < a(food@1)=1 — the semantics (D12: ordering
    // is semantics) forces the older cohort regardless of enumeration order.
    const calc = load(FIX('till-eat.ill'));
    const food = Store.put('atom', ['food']);
    const food1 = Store.put('at', [food, Store.put1('binlit', 1n)]);
    const order = Store.put('atom', ['meal_order']);
    const S = { linear: { [food]: 1, [food1]: 1, [order]: 1 }, persistent: {} };
    assert.deepEqual(stamped(calc.settle(S, '5', { cohort: 'lifo' }).state),
      { 'eaten@0': 1, 'food@1': 1 });
  });

  it('fifo vs lifo differ exactly on equal-activation ties (selection is policy)', () => {
    // meal_order@2 lifts both candidates to a=2 — now the cohort sampler
    // is the tie-break: fifo takes food@0, lifo takes food@1.
    const calc = load(FIX('till-eat.ill'));
    const food = Store.put('atom', ['food']);
    const food1 = Store.put('at', [food, Store.put1('binlit', 1n)]);
    const order2 = Store.put('at', [Store.put('atom', ['meal_order']), Store.put1('binlit', 2n)]);
    const S = { linear: { [food]: 1, [food1]: 1, [order2]: 1 }, persistent: {} };
    assert.deepEqual(stamped(calc.settle(S, '5').state), { 'eaten@2': 1, 'food@1': 1 });
    assert.deepEqual(stamped(calc.settle(S, '5', { cohort: 'lifo' }).state),
      { 'eaten@2': 1, 'food@0': 1 });
  });
});

describe('till delay terms (E7.1) + FFI principle', () => {
  let calc, S;
  before(() => {
    calc = load(FIX('till-delay.ill'));
    const chopper = Store.put('atom', ['chopper']);
    const tree = Store.put('atom', ['tree']);
    const emp4 = Store.put('emp', [Store.put1('binlit', 4n)]);
    S = { linear: { [chopper]: 1, [tree]: 2, [emp4]: 1 }, persistent: {} };
  });

  it('duration derived from context: 10/N with N=4 ⇒ jobs at 0 and 5/2', () => {
    const res = calc.settle(S, '10');
    assert.deepEqual(stamped(res.state),
      { 'wood@5/2': 1, 'wood@5': 1, 'chopper@5': 1, 'emp@0': 1 });
    // the read arc kept emp at its ORIGINAL stamp and never consumed it
  });

  it('FFI off (clause path) agrees hash-for-hash', () => {
    const on = calc.settle(S, '10');
    const off = calc.settle(S, '10', { useFFI: false });
    assert.deepEqual(stamped(off.state), stamped(on.state));
  });

  it('views: pending / inFlight / observable at T=1', () => {
    const res = calc.settle(S, '10');
    const obs = calc.observable(res.state, '1');
    assert.equal(obs[Store.put('atom', ['wood'])] || 0, 0);   // wood still in flight at 1
    const pend = calc.pending(res.state, '1');
    assert.deepEqual(pend.map(p => ratParts(p.stamp)), [[5n, 2n], [5n, 1n], [5n, 1n]]);
    assert.deepEqual(ratParts(pend[0].remaining), [3n, 2n]);  // 5/2 − 1
    const jobs = calc.inFlight(res.events, '1');
    assert.deepEqual(jobs.map(j => j.rule), ['chop']);        // job1 running at T=1
    assert.deepEqual(ratParts(jobs[0].remaining), [3n, 2n]);
  });

  it('unbound delay variable is a loud compile error (E7.1 mode check)', () => {
    assert.throws(() => load(FIX('till-delay-unbound.ill')), /delay variable 'D'/);
  });
});

describe('till untimed-engine guards + Zeno (D16)', () => {
  it('calc.exec rejects delayed rules loudly', () => {
    const calc = load(SPEC('schedule.ill'));
    const S = init(calc, 'expect_two_jobs');
    assert.throws(() => calc.exec(S), /timed matcher/);
  });

  it('calc.exec rejects windowed and counted rules loudly', () => {
    const spoil = load(SPEC('spoilage.ill'));
    assert.throws(() => spoil.exec(init(spoil, 'expect_rots_at_two')), /timed matcher/);
    const grades = load(SPEC('grades.ill'));
    assert.throws(() => grades.exec(init(grades, 'expect_split_residual')), /timed matcher/);
  });

  it('zero-delay cycle trips the Zeno guard', () => {
    const calc = load(FIX('till-zeno.ill'));
    const a = Store.put('atom', ['a']);
    assert.throws(() => calc.settle({ linear: { [a]: 1 }, persistent: {} }, '0', { maxSteps: 50 }),
      /Zeno/);
  });
});

describe('till ≡ oracle (differential, conflict-free scenarios)', () => {
  it('schedule: engine and reference scheduler agree on the timed multiset', async () => {
    const oracle = await import('../../tools/till-oracle.mjs');
    const rules = [{ name: 'sawmill_rule',
      inputs: [{ atom: 'sawmill' }, { atom: 'wood' }],
      delay: '1/2', outputs: [['sawmill'], ['plank']] }];
    const calc = load(SPEC('schedule.ill'));
    const S = init(calc, 'expect_two_jobs');
    for (const T of ['0', '0.4', '1/2', '0.7', '1', '5']) {
      const eng = stamped(calc.settle(S, T).state);
      const ref = oracle.settle(
        oracle.makeState([['sawmill', 0], ['wood', 0, 2]]), T, { rules }).state;
      const refMap = {};
      for (const c of ref.values()) refMap[`${c.atom}@${oracle.rstr(c.stamp)}`] = c.count;
      assert.deepEqual(eng, refMap, `horizon ${T}`);
    }
  });

  it('spoilage worked example: eat at 1 beats spoil at 2 under a horizon jump', async () => {
    const oracle = await import('../../tools/till-oracle.mjs');
    const rules = [
      { name: 'eat', inputs: [{ atom: 'food' }, { atom: 'meal_order' }], outputs: [['eaten']] },
      { name: 'spoil', inputs: [{ atom: 'food', stampVar: 'Q' }],
        after: [th => oracle.radd(th.stamps.Q, oracle.rat(2))], outputs: [['rotten']] },
    ];
    const calc = load(SPEC('spoilage.ill'));
    const S = init(calc, 'expect_eaten_not_rotten');
    const eng = stamped(calc.settle(S, '5', { rules: undefined }).state);
    const ref = oracle.settle(
      oracle.makeState([['food', 0], ['meal_order', 1]]), 5, { rules }).state;
    const refMap = {};
    for (const c of ref.values()) refMap[`${c.atom}@${oracle.rstr(c.stamp)}`] = c.count;
    // spec file also carries the bakery rule — restrict to eat/spoil facts
    delete eng['bakery@0'];
    assert.deepEqual(eng, refMap);
  });
});

describe('till timedSubset (runner semantics)', () => {
  it('unstamped pattern facts are stamp wildcards; stamped are exact', () => {
    const wood = Store.put('atom', ['wood']);
    const w2 = Store.put('at', [wood, Store.put1('binlit', 2n)]);
    const w5 = Store.put('at', [wood, Store.put1('binlit', 5n)]);
    const state = { linear: { [w2]: 1, [w5]: 2 }, persistent: {} };
    assert.ok(timedSubset({ linear: { [wood]: 3 }, persistent: {} }, state));
    assert.ok(!timedSubset({ linear: { [wood]: 4 }, persistent: {} }, state));
    assert.ok(timedSubset({ linear: { [w5]: 2 }, persistent: {} }, state));
    assert.ok(!timedSubset({ linear: { [w2]: 2 }, persistent: {} }, state));
  });

  it('timedExact demands a full cover: extra facts fail (Phase 5.5)', () => {
    const wood = Store.put('atom', ['wood']);
    const plank = Store.put('atom', ['plank']);
    const w2 = Store.put('at', [wood, Store.put1('binlit', 2n)]);
    const w5 = Store.put('at', [wood, Store.put1('binlit', 5n)]);
    const p0 = Store.put('at', [plank, Store.put1('binlit', 0n)]);
    const state = { linear: { [w2]: 1, [w5]: 2, [p0]: 1 }, persistent: {} };
    // full cover: exact + wildcard mix, totals match per group
    assert.ok(timedExact({ linear: { [w2]: 1, [wood]: 2, [p0]: 1 }, persistent: {} }, state));
    // subset passes but exact fails: plank unaccounted
    assert.ok(timedSubset({ linear: { [wood]: 3 }, persistent: {} }, state));
    assert.ok(!timedExact({ linear: { [wood]: 3 }, persistent: {} }, state));
    // over-demand and wrong stamps fail
    assert.ok(!timedExact({ linear: { [wood]: 4, [p0]: 1 }, persistent: {} }, state));
    assert.ok(!timedExact({ linear: { [w2]: 2, [wood]: 1, [p0]: 1 }, persistent: {} }, state));
    // wildcard cannot double-count an exact demand (disjoint accounting)
    assert.ok(!timedExact({ linear: { [w5]: 2, [wood]: 2, [p0]: 1 }, persistent: {} }, state));
  });
});

describe('till grade algebra unit checks', () => {
  it('parseStamp: exact strings, integer numbers, hash passthrough; floats rejected', () => {
    const p = tillGrades.parseStamp;
    assert.deepEqual(ratParts(p('0.7')), [7n, 10n]);
    assert.deepEqual(ratParts(p('1/2')), [1n, 2n]);
    assert.deepEqual(ratParts(p('3')), [3n, 1n]);
    assert.deepEqual(ratParts(p(3)), [3n, 1n]);
    // numbers are VALUES; an existing stamp hash needs the explicit wrapper
    assert.equal(p({ stamp: p('1/2') }), p('1/2'));
    assert.throws(() => p(0.7), /non-integer Number/);
  });
});

describe('till settleExplore — instant-feeding completeness (round 13)', () => {
  const atom = (n) => Store.put('atom', [n]);
  /** Every exec outcome across seeds must be an explore leaf (containment). */
  const containment = (calc, S, expectDistinct) => {
    const execBags = new Set();
    for (let seed = 0; seed < 40; seed++) execBags.add(bagStr(calc.settle(S, '0', { seed }).state));
    const leafBags = new Set(calc.settleExplore(S, '0').leaves.map(l => bagStr(l.state)));
    assert.equal(execBags.size, expectDistinct, 'exec reaches both worlds across seeds');
    for (const b of execBags) assert.ok(leafBags.has(b), `exec outcome ${b} missing from explore`);
  };

  it('plain arcs: zero-delay production enabling a competitor forks (ample set)', () => {
    // make: a -o {b}.  eat: c -o {d}.  use: b * c -o {prize}.
    // {make, eat} share no cohort, but make's instant b enables use vs eat.
    const calc = load(FIX('till-instant-enable.ill'));
    containment(calc, { linear: { [atom('a')]: 1, [atom('c')]: 1 }, persistent: {} }, 2);
  });

  it('transfer arcs: zero-delay production into a !_W cohort forks (W is order-sensitive)', () => {
    // grow: seed -o {wood}.  mill: !_W wood * !mul W W S -o {!_S plank}.
    // mill-first: 2²+1² = 5 planks; grow-first: 3² = 9 planks.
    const calc = load(FIX('till-instant-transfer.ill'));
    containment(calc, { linear: { [atom('seed')]: 1, [atom('wood')]: 2 }, persistent: {} }, 2);
  });

  it('future-delay production does not fork (outputs cannot join the instant)', () => {
    // chopbuild: chop produces wood@+4 — no same-instant enablement anywhere,
    // and every activation instant has a single candidate: exactly one leaf.
    const calc = load(path.join(import.meta.dirname, '../../calculus/till/tests/debug/chopbuild.ill'));
    const S = convert.decomposeQuery(calc.queries.get('run'));
    assert.equal(calc.settleExplore(S, '10').leaves.length, 1);
  });
});

describe('till fused ≡ fissioned (E7.3 theorem, round-13 residue v)', () => {
  it('{b}@5 lands at the same stamp as an explicit 2+3 intermediate chain', () => {
    const calc = load(FIX('till-fission.ill'));
    const fused = calc.settle({ linear: { [Store.put('atom', ['a'])]: 1 }, persistent: {} }, '5').state;
    const fiss = calc.settle({ linear: { [Store.put('atom', ['a2'])]: 1 }, persistent: {} }, '5').state;
    assert.deepEqual(stamped(fused), { 'b@5': 1 });
    assert.deepEqual(stamped(fiss), { 'b2@5': 1 });     // same stamp, no residual m
  });

  it('fission is observable mid-flight, fusion is not (the E7.3 trade)', () => {
    const calc = load(FIX('till-fission.ill'));
    // horizon 1: fiss1 fired (a=0), m stamped 2 in flight; fiss2 (a=2) pending
    const mid = calc.settle({ linear: { [Store.put('atom', ['a2'])]: 1 }, persistent: {} }, '1').state;
    assert.deepEqual(stamped(mid), { 'm@2': 1 });
  });
});

describe('till settle onStep hook (round-13 residue vi)', () => {
  it('emits one record per firing with activation/delay/live state', () => {
    const calc = load(SPEC('schedule.ill'));
    const S = init(calc, 'expect_two_jobs');
    const seen = [];
    calc.settle(S, '1', { onStep: (e) => seen.push(e) });
    assert.equal(seen.length, 2);
    assert.deepEqual(seen.map(e => e.step), [1, 2]);
    assert.deepEqual(seen.map(e => e.rule.name), ['sawmill_rule', 'sawmill_rule']);
    assert.deepEqual(seen.map(e => ratParts(e.activation)), [[0n, 1n], [1n, 2n]]);
    assert.deepEqual(seen.map(e => ratParts(e.delay)), [[1n, 2n], [1n, 2n]]);
    for (const e of seen) {
      assert.equal(typeof e.consumed, 'object');
      assert.ok(Array.isArray(e.theta));
      assert.ok(e.state.linear.group, 'state is the live State object');
    }
  });
});

describe('till error contracts (round 13 pins)', () => {
  it('rejects woplus in antecedents — bare and at-wrapped', () => {
    assert.throws(() => load(FIX('till-woplus-ante.ill')), /not allowed in antecedents/);
    assert.throws(() => load(FIX('till-woplus-ante-at.ill')), /not allowed in antecedents/);
  });

  it('rejects wrong-arity woplus (application parse admits any arity)', () => {
    assert.throws(() => load(FIX('till-woplus-arity.ill')), /woplus requires exactly 3 arguments/);
  });

  it('rejects nested graded monads in consequents (no runtime graded-μ)', () => {
    assert.throws(() => load(FIX('till-nested-gmonad.ill')), /nested graded monad/);
  });

  it('rejects dynamic rules (lolis) in timed consequents at fire time', () => {
    const calc = load(FIX('till-loli-conseq.ill'));
    const S = { linear: { [Store.put('atom', ['a'])]: 1 }, persistent: {} };
    assert.throws(() => calc.settle(S, '0'), /lolis.*not supported/);
  });

  it('parseStamp rejects negative stamps (ℚ≥0 in v1)', () => {
    const p = tillGrades.parseStamp;
    assert.throws(() => p('-1'), /non-negative/);
    assert.throws(() => p('-1/2'), /non-negative/);
    assert.throws(() => p(-3), /non-negative/);
  });
});
