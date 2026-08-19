/**
 * till settle determinism gates — TODO_0265 Phase 5 (infrastructure map:
 * settle-determinism; the D13 "index is optimization" and FFI-principle
 * gates at TRACE granularity, plus rule-declaration-order confluence).
 *
 *   - same seed ⇒ trace-identical (rule, activation, alt) — economy + duel
 *   - FFI on ≡ off: identical traces AND final states (not just outcomes)
 *   - index policy on ≡ off: the stamp-sorted FactSet policy may change
 *     candidate ENUMERATION only, never which events fire (confluent specs)
 *   - rule declaration order is not semantics: permuted program ⇒ identical
 *     trace and final multiset (D12 fixes firing order)
 *   - literal-fact programs: dirty ≡ rescan (round-14 regression — predHead
 *     has no name for sub-boundary tags; see till-litfact.ill)
 *   - economy views: observable slice / in-flight at T=1 match the oracle
 *     acceptance numbers (time.mjs ground truth)
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
const FIX = (f) => path.join(import.meta.dirname, '../fixtures', f);
const load = (p, cfg = tillConfig) => mde.load(p, { calculusConfig: cfg, cache: false });
const init = (calc, kind) => convert.decomposeQuery(calc.splitQueries.get(kind).lhsHash);
const atom = (n) => Store.put('atom', [n]);

const traceKey = (events) =>
  events.map(e => `${e.rule}@${ratParts(e.activation).join('/')}:${e.alt ?? ''}`).join(' ');

/** Canonical 'inner@n/d'×count string of a timed state. */
function stamped(state) {
  const out = {};
  for (const [hStr, c] of Object.entries(state.linear)) {
    const h = Number(hStr);
    const isAt = Store.tag(h) === 'at';
    const inner = isAt ? Store.child(h, 0) : h;
    const [n, d] = isAt ? ratParts(Store.child(h, 1)) : [0n, 1n];
    const key = `${Store.tag(inner) === 'atom' ? Store.child(inner, 0) : Store.tag(inner)}@${n}/${d}`;
    out[key] = (out[key] || 0) + c;
  }
  return Object.entries(out).sort().map(([k, v]) => `${k}x${v}`).join(',');
}

describe('till determinism: same seed ⇒ trace-identical', () => {
  it('economy: replay across seeds', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_economy');
    for (const seed of [0, 1, 7, 42]) {
      const a = calc.settle(S, '1', { seed });
      const b = calc.settle(S, '1', { seed });
      assert.equal(traceKey(b.events), traceKey(a.events), `seed ${seed}`);
      assert.equal(stamped(b.state), stamped(a.state), `seed ${seed}`);
    }
  });

  it('duel (weighted choice): replay across seeds', () => {
    const calc = load(FIX('till-duel.ill'));
    const S = { linear: { [atom('rock')]: 3, [atom('sci')]: 3 }, persistent: {} };
    for (const seed of [0, 5, 11]) {
      const a = calc.settle(S, '0', { seed });
      const b = calc.settle(S, '0', { seed });
      assert.equal(traceKey(b.events), traceKey(a.events), `seed ${seed}`);
    }
  });
});

describe('till determinism: FFI on ≡ off at trace granularity', () => {
  for (const [file, kind, T] of [
    ['grades.ill', 'expect_whole_cohort', '20'],      // !mul/!div goals
    ['spoilage.ill', 'expect_fresh_only', '10'],      // window arithmetic
    ['economy.ill', 'expect_economy', '1'],
  ]) {
    it(`${file} ${kind}`, () => {
      const calc = load(SPEC(file));
      const S = init(calc, kind);
      const on = calc.settle(S, T);
      const off = calc.settle(S, T, { useFFI: false });
      assert.equal(traceKey(off.events), traceKey(on.events));
      assert.equal(stamped(off.state), stamped(on.state));
    });
  }
});

describe('till determinism: index ORDER is optimization (D13)', () => {
  // The policy's groupKey (file at(A,t) under A's predicate) is contract —
  // without it stamped facts are invisible to the matcher. What IS mere
  // optimization is the intra-group ORDER: scrambling the comparator from
  // stamp-sorted to arena-hash order may change candidate enumeration only,
  // never which events fire. Confluent scenarios only — equal-activation
  // cohort ties are policy by design (D12: fifo/lifo).
  const scrambled = {
    ...tillConfig,
    factSetPolicy: { groupKey: tillConfig.factSetPolicy.groupKey, cmp: (a, b) => a - b },
  };
  for (const [file, kind, T] of [
    ['schedule.ill', 'expect_two_jobs', '1'],
    ['spoilage.ill', 'expect_eaten_not_rotten', '5'],
    ['read.ill', 'expect_atomic', '10'],
  ]) {
    it(`${file} ${kind}: trace-identical under a scrambled index order`, () => {
      const a = (() => { const c = load(SPEC(file)); return c.settle(init(c, kind), T); })();
      const b = (() => { const c = load(SPEC(file), scrambled); return c.settle(init(c, kind), T); })();
      assert.equal(traceKey(b.events), traceKey(a.events));
      assert.equal(stamped(b.state), stamped(a.state));
    });
  }

  it('economy: equal-activation cohort ties are policy (D12), aggregates are not', () => {
    // At a=9/10 the smith can take plank@0 or plank@1/2 — equal activation,
    // so WHICH cohort is the sampler's call (fifo = index order; scrambling
    // the index legitimately changes it). The rule/activation trace and the
    // observable aggregate at T=1 are invariant; only leftover stamps move.
    const a = (() => { const c = load(SPEC('economy.ill')); return { c, r: c.settle(init(c, 'expect_economy'), '1') }; })();
    const b = (() => { const c = load(SPEC('economy.ill'), scrambled); return { c, r: c.settle(init(c, 'expect_economy'), '1') }; })();
    const ruleActs = (r) => r.events.map(e => `${e.rule}@${ratParts(e.activation).join('/')}`).join(' ');
    assert.equal(ruleActs(b.r), ruleActs(a.r));
    for (const n of ['wood', 'plank', 'stone', 'tool']) {
      assert.equal(b.c.observable(b.r.state, '1')[atom(n)] || 0,
        a.c.observable(a.r.state, '1')[atom(n)] || 0, n);
    }
  });
});

describe('till confluence: rule declaration order is not semantics', () => {
  it('permuted pipeline: identical trace and final multiset', () => {
    const S = {
      linear: {
        [atom('mill')]: 1, [atom('oven')]: 1,
        [atom('cust')]: 2, [atom('wood')]: 3,
      }, persistent: {},
    };
    const a = load(FIX('till-perm-a.ill')).settle(S, '10');
    const b = load(FIX('till-perm-b.ill')).settle(S, '10');
    assert.equal(traceKey(b.events), traceKey(a.events));
    assert.equal(stamped(b.state), stamped(a.state));
    // sanity: the pipeline actually ran to depth 3
    assert.match(stamped(a.state), /fed@/);
  });
});

describe('till determinism: literal-fact dirty ≡ rescan (round-14 regression)', () => {
  it('a produced binary literal wakes its consumer under dirty tracking', () => {
    const calc = load(FIX('till-litfact.ill'));
    const e = Store.put1('binlit', 0n);   // `e` = empty binary literal
    const S = { linear: { [atom('src')]: 1, [e]: 1 }, persistent: {} };
    const a = calc.settle(S, '2');
    const b = calc.settle(S, '2', { scheduler: 'dirty' });
    assert.equal(traceKey(a.events), 'gen@0/1: pair2@0/1:');
    assert.equal(traceKey(b.events), traceKey(a.events));
    assert.equal(stamped(b.state), stamped(a.state));
  });
});

describe('till economy views ≡ oracle acceptance (time.mjs)', () => {
  it('observable slice at T=1 is {wood:7, plank:8, stone:6, tool:3}; both buildings in flight', () => {
    const calc = load(SPEC('economy.ill'));
    const res = calc.settle(init(calc, 'expect_economy'), '1');
    const obs = calc.observable(res.state, '1');
    const byName = (n) => obs[atom(n)] || 0;
    assert.deepEqual(
      { wood: byName('wood'), plank: byName('plank'), stone: byName('stone'), tool: byName('tool') },
      { wood: 7, plank: 8, stone: 6, tool: 3 });
    const busy = calc.inFlight(res.events, '1').map(j => j.rule).sort();
    assert.deepEqual(busy, ['forge', 'saw']);
  });

  it('differential vs the reference scheduler across horizons', async () => {
    const oracle = await import('../../tools/till-oracle.mjs');
    const rules = [
      { name: 'saw', inputs: [{ atom: 'sawmill' }, { atom: 'wood' }],
        delay: '1/2', outputs: [['sawmill'], ['plank']] },
      { name: 'forge', inputs: [{ atom: 'smith' }, { atom: 'plank' }, { atom: 'stone' }],
        delay: '3/10', outputs: [['smith'], ['tool']] },
    ];
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_economy');
    for (const T of ['0', '0.3', '0.55', '1', '2', '5']) {
      const eng = stamped(calc.settle(S, T).state);
      const ref = oracle.settle(oracle.makeState([
        ['wood', 0, 10], ['plank', 0, 10], ['stone', 0, 10], ['sawmill', 0], ['smith', 0],
      ]), T, { rules }).state;
      const refMap = {};
      for (const c of ref.values()) {
        const r = oracle.rstr(c.stamp);
        const key = `${c.atom}@${r.includes('/') ? r : `${r}/1`}`;
        refMap[key] = (refMap[key] || 0) + c.count;
      }
      const refStr = Object.entries(refMap).sort().map(([k, v]) => `${k}x${v}`).join(',');
      assert.equal(eng, refStr, `horizon ${T}`);
    }
  });
});
