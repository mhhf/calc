// till-oracle.test.js — the till reference semantics against hand-computed scenarios
// (todo 0265 Phase 0.5). Every expected value here is derived by hand from the spec;
// the engine (Phases 3-4) is later differentially tested against this oracle.
import { describe, it } from 'node:test';
import assert from 'node:assert';
import { rat, radd, rcmp, rstr, makeState, settle, stateEq, observable, inFlight, nextActivation, bestMatch }
  from '../../tools/till-oracle.mjs';

const R = (rules) => rules;

describe('till oracle: 10/10/10 scenario (time.mjs ground truth)', () => {
  const rules = R([
    { name: 'sawmill', inputs: [{ atom: 'sawmill' }, { atom: 'wood' }],
      delay: '0.5', outputs: [['sawmill'], ['plank']] },
    { name: 'smith', inputs: [{ atom: 'smith' }, { atom: 'plank' }, { atom: 'stone' }],
      delay: '0.3', outputs: [['smith'], ['tool']] },
  ]);
  const init = makeState([['wood', 0, 10], ['plank', 0, 10], ['stone', 0, 10], ['sawmill', 0], ['smith', 0]]);

  it('observable slice at T=1.0 is {wood:7, plank:8, stone:6, tool:3}, both buildings in flight', () => {
    const { state, log } = settle(init, 1, { rules });
    assert.deepStrictEqual(observable(state, 1), { wood: 7, plank: 8, stone: 6, tool: 3 });
    const busy = inFlight(log, 1).map(e => e.rule).sort();
    assert.deepStrictEqual(busy, ['sawmill', 'smith']);
  });

  it('settle composability: settle(settle(S,T1),T2) = settle(S,T2)', () => {
    for (const t1 of ['0.3', '0.55', '0.7', '1']) {
      const oneShot = settle(init, 1, { rules }).state;
      const twoShot = settle(settle(init, t1, { rules }).state, 1, { rules }).state;
      assert.ok(stateEq(oneShot, twoShot), `split at T1=${t1} diverged`);
    }
  });

  it('settle idempotence at equal horizon', () => {
    const s1 = settle(init, 1, { rules }).state;
    assert.ok(stateEq(s1, settle(s1, 1, { rules }).state));
  });
});

describe('till oracle: min-activation matching (P1), not lexicographic-first', () => {
  // State A@0, A@3, B@3, B@9; guard rejects the (A@0,B@3) pair (stamp gap != 3).
  // Lexicographic-first-with-backtracking finds (A@0,B@9) at a=9;
  // the true minimal-activation match is (A@3,B@3) at a=3.
  const rule = {
    name: 'r',
    inputs: [{ atom: 'A', stampVar: 'P' }, { atom: 'B', stampVar: 'Q' }],
    guards: [th => { const gap = rcmp(th.stamps.Q, th.stamps.P); // reject exactly gap "3-0"
      return !(rstr(th.stamps.P) === '0' && rstr(th.stamps.Q) === '3'); }],
    delay: 0, outputs: [['done']],
  };
  const st = makeState([['A', 0], ['A', 3], ['B', 3], ['B', 9]]);

  it('bestMatch activation is 3 (the branch-and-bound minimum)', () => {
    const m = bestMatch(rule, st);
    assert.strictEqual(rstr(m.a), '3');
    assert.strictEqual(rstr(m.sel[0].stamp), '3');
    assert.strictEqual(rstr(m.sel[1].stamp), '3');
  });
});

describe('till oracle: windows and spoilage on one timeline (worked example, D8/E5)', () => {
  const eat = { name: 'eat', inputs: [{ atom: 'food' }, { atom: 'meal_order' }], delay: 0, outputs: [['eaten']] };
  const spoil = { name: 'spoil', inputs: [{ atom: 'food', stampVar: 'Q' }],
    after: [th => radd(th.stamps.Q, rat(2))],
    delay: 0, outputs: [['rotten']] };

  it('horizon jump to T=5: eat fires at a=1, spoil never gets the food', () => {
    const { state, log } = settle(makeState([['food', 0], ['meal_order', 1]]), 5, { rules: [eat, spoil] });
    assert.deepStrictEqual(log.map(e => [e.rule, rstr(e.a)]), [['eat', '1']]);
    assert.strictEqual(observable(state, 5).rotten, undefined);
  });

  it('no order: spoil fires at exactly Q+2', () => {
    const { log } = settle(makeState([['food', 0]]), 5, { rules: [eat, spoil] });
    assert.deepStrictEqual(log.map(e => [e.rule, rstr(e.a)]), [['spoil', '2']]);
  });

  it('FIFO: consumption drains the oldest cohort first', () => {
    const { state } = settle(makeState([['food', 0], ['food', 1], ['meal_order', 0]]), 5,
      { rules: [eat] });
    assert.strictEqual(state.has('food@0'), false);
    assert.strictEqual(state.get('food@1').count, 1);
  });

  it('hard expiry (C2): before-window consumer skips stale cohorts', () => {
    // bakery eats only fresh food (before Q+2); stale food can only rot.
    const bakery = { name: 'bakery', inputs: [{ atom: 'bakery' }, { atom: 'food', stampVar: 'Q' }],
      before: [th => radd(th.stamps.Q, rat(2))],
      after: [() => rat(3)],                    // bakery only starts baking at t=3
      delay: 1, outputs: [['bakery'], ['bread']] };
    // food@0 is stale at t=3 (deadline 2); food@2 is fresh until 4.
    const { state, log } = settle(makeState([['bakery', 0], ['food', 0], ['food', 2]]), 10,
      { rules: [bakery, spoil] });
    const bakes = log.filter(e => e.rule === 'bakery');
    assert.strictEqual(bakes.length, 1);
    assert.strictEqual(rstr(bakes[0].sel[1].stamp), '2');   // took the FRESH cohort, not the oldest
    assert.strictEqual(observable(state, 10).bread, 1);
    assert.strictEqual(observable(state, 10).rotten, 1);    // the stale one rotted (at 2)
  });
});

describe('till oracle: count grades (D4, revised — binding decides cohort discipline)', () => {
  it('!_k splits k off, leaving the residual (single cohort)', () => {
    const r = { name: 'pair', inputs: [{ atom: 'wood', count: 2 }], delay: 0, outputs: [['bundle']] };
    const { state } = settle(makeState([['wood', 0, 5]]), 0, { rules: [r], maxSteps: 10 });
    assert.strictEqual(observable(state, 0).wood, 1);       // 5 -> 3 -> 1, then quiescent
    assert.strictEqual(observable(state, 0).bundle, 2);
  });

  it('unstamped !_k spreads across cohorts oldest-first; activation = newest taken', () => {
    const r = { name: 'pair', inputs: [{ atom: 'log', count: 2 }], delay: 0, outputs: [['bundle']] };
    // log@0 x1, log@1 x2, log@3 x1: fires at a=1 (0+1), then a=3 (1+3)
    const { state, log } = settle(makeState([['log', 0, 1], ['log', 1, 2], ['log', 3, 1]]), 5,
      { rules: [r] });
    assert.deepStrictEqual(log.map(e => rstr(e.a)), ['1', '3']);
    assert.strictEqual(observable(state, 5).log, undefined); // all consumed
    assert.strictEqual(observable(state, 5).bundle, 2);
  });

  it('stamped !_W A@T binds ONE cohort at firing time; sawmill floor(1.5W)', () => {
    const sawmill = { name: 'sawmill',
      inputs: [{ atom: 'sawmill' }, { atom: 'wood', countVar: 'W', stampVar: 'T' }],
      delay: 10,
      outputs: th => [['sawmill'], ['plank', Math.floor(th.counts.W * 3 / 2)]] };
    // two cohorts: 3 wood at 0 and 5 wood at 1 -> two firings, W=3 then W=5
    const { state, log } = settle(makeState([['sawmill', 0], ['wood', 0, 3], ['wood', 1, 5]]), 20,
      { rules: [sawmill] });
    assert.deepStrictEqual(log.map(e => [rstr(e.a), e.sel[1].take]), [['0', 3], ['10', 5]]);
    assert.strictEqual(observable(state, 30).plank, 4 + 7); // floor(4.5) + floor(7.5)
  });

  it('unstamped !_W binds the TOTAL across cohorts and drains them all', () => {
    const mill = { name: 'mill',
      inputs: [{ atom: 'wood', countVar: 'W' }],
      delay: 0,
      outputs: th => [['plank', th.counts.W]] };
    const { state, log } = settle(makeState([['wood', 0, 3], ['wood', 1, 5]]), 5, { rules: [mill] });
    assert.strictEqual(log.length, 1);                       // ONE firing takes everything
    assert.strictEqual(log[0].sel[0].take, 8);
    assert.strictEqual(rstr(log[0].a), '1');                 // newest taken stamp
    assert.strictEqual(observable(state, 5).plank, 8);
    assert.strictEqual(observable(state, 5).wood, undefined);
  });
});

describe('till oracle: read arcs (E7.2)', () => {
  it('concurrent reads do not conflict; the token keeps its original stamp', () => {
    const chop = { name: 'chop', inputs: [{ atom: 'chopper' }, { atom: 'manual', mode: 'read' }],
      delay: 4, outputs: [['chopper'], ['wood']] };
    const { state, log } = settle(makeState([['chopper', 0, 2], ['manual', 0]]), 0, { rules: [chop] });
    assert.deepStrictEqual(log.map(e => rstr(e.a)), ['0', '0']);   // both jobs start at 0
    assert.strictEqual(state.get('manual@0').count, 1);            // never consumed, stamp intact
    assert.strictEqual(observable(state, 4).wood, 2);
  });

  it("read stamp joins the activation max (can't read before it exists)", () => {
    const r = { name: 'r', inputs: [{ atom: 'x' }, { atom: 'late', mode: 'read' }], delay: 0, outputs: [['y']] };
    const { log } = settle(makeState([['x', 0], ['late', 7]]), 10, { rules: [r] });
    assert.strictEqual(rstr(log[0].a), '7');
  });
});

describe('till oracle: in-flight atomicity (E7.3) and productivity (D16)', () => {
  it('a consumer of a fused job\'s output activates at >= completion', () => {
    const chop = { name: 'chop', inputs: [{ atom: 'chopper' }], delay: 4, outputs: [['chopper'], ['wood']] };
    const eat = { name: 'eat', inputs: [{ atom: 'wood' }], delay: 0, outputs: [] };
    const { log } = settle(makeState([['chopper', 0]]), 4, { rules: [chop, eat], maxSteps: 4 });
    const eats = log.filter(e => e.rule === 'eat');
    assert.strictEqual(rstr(eats[0].a), '4');               // not one instant earlier
  });

  it('positive-delay self-loop is productive: events at 0,1,2,3', () => {
    const ping = { name: 'ping', inputs: [{ atom: 'a' }], delay: 1, outputs: [['a']] };
    const { state, log } = settle(makeState([['a', 0]]), 3, { rules: [ping] });
    assert.deepStrictEqual(log.map(e => rstr(e.a)), ['0', '1', '2', '3']);
    assert.ok(state.has('a@4'));
  });

  it('zero-delay self-loop trips the Zeno guard', () => {
    const ping0 = { name: 'ping0', inputs: [{ atom: 'a' }], delay: 0, outputs: [['a']] };
    assert.throws(() => settle(makeState([['a', 0]]), 3, { rules: [ping0], maxSteps: 50 }),
      /Zeno/);
  });
});

describe('till oracle: PRF chooser (D17/P5)', () => {
  const mk = () => makeState([['token', 0]]);
  const left = { name: 'left', inputs: [{ atom: 'token' }], delay: 0, outputs: [['L']] };
  const right = { name: 'right', inputs: [{ atom: 'token' }], delay: 0, outputs: [['R']] };

  it('same seed => same choice, every run and under horizon splits', () => {
    const a = settle(mk(), 5, { rules: [left, right], seed: 42 }).state;
    const b = settle(mk(), 5, { rules: [left, right], seed: 42 }).state;
    const c = settle(settle(mk(), 0, { rules: [left, right], seed: 42 }).state, 5,
      { rules: [left, right], seed: 42 }).state;
    assert.ok(stateEq(a, b) && stateEq(a, c));
  });

  it('some seed picks the other branch (the choice is real)', () => {
    const outcomes = new Set();
    for (let s = 0; s < 32; s++)
      outcomes.add(Object.keys(observable(settle(mk(), 5, { rules: [left, right], seed: s }).state, 5))[0]);
    assert.deepStrictEqual([...outcomes].sort(), ['L', 'R']);
  });
});

describe('till oracle: nextActivation', () => {
  it('peeks the earliest pending activation without firing', () => {
    const r = { name: 'r', inputs: [{ atom: 'x' }], delay: 1, outputs: [] };
    const st = makeState([['x', '3/2']]);
    assert.strictEqual(rstr(nextActivation(st, [r])), '3/2');
    assert.strictEqual(nextActivation(makeState([]), [r]), null);
  });
});
