/**
 * Raw-mode settle pipelines (TODO_0277 audit — the scheduler cross-call
 * cache `_schedCache` and the normalizeTimedState passthrough had ZERO
 * test coverage; they were exercised only by benchmarks).
 *
 * Pins:
 *   - a chained raw pipeline is trace- and state-identical to a single
 *     settle (the cached dirty scheduler resumes exactly)
 *   - external mutation of the raw State between ticks invalidates the
 *     cached scheduler (mutation counters), never silently
 *   - a rebase shift drops the cached scheduler (old-frame activations)
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { packRef, refInner } from '../../lib/engine/labels.js';
import { ratParts } from '../../lib/kernel/rat-term.js';
import { SPEC, loadTill as load, initQuery as init, bagStr, stampedStr, traceKey } from './till-helpers.js';

const plainOf = (s) => (s.linear && s.linear.group ? toObject(s) : s);

describe('raw settle pipelines — scheduler cache reuse', () => {
  it('chained raw ticks are trace- and state-identical to one settle', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const single = calc.settle(S, '100', { seed: 3 });
    let state = S;
    const events = [];
    for (const T of ['10', '25', '40', '77', '100']) {
      const r = calc.settle(state, T, { seed: 3, raw: true });
      events.push(...r.events);
      state = r.state;
    }
    assert.equal(traceKey(events), traceKey(single.events));
    assert.equal(stampedStr(plainOf(state)), stampedStr(single.state));
  });

  it('external mutation between raw ticks invalidates the cached scheduler', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const r1 = calc.settle(S, '10', { seed: 3, raw: true });
    // Inject one extra copy of an existing token at a fresh stamp, OUTSIDE
    // settle — the cached scheduler's activations are now stale and the
    // mutation counter must force a rebuild. Labelled state (THY_0024):
    // external mutation goes through packed refs + the stamp table.
    let anyRef = null;
    r1.state.linear.forEach((ref) => { if (anyRef === null) anyRef = ref; });
    assert.ok(anyRef !== null);
    const inner = refInner(anyRef);
    const sid12 = r1.state.linear.stamps.internTerm(Store.put1('binlit', 12n));
    r1.state.linear.insert(Store.tagId(inner), packRef(inner, sid12), null, 1);
    const extra = Store.put('at', [inner, Store.put1('binlit', 12n)]);
    const cont = calc.settle(r1.state, '100', { seed: 3, raw: true });
    // Oracle: the identical mutated state as a fresh plain object.
    const o1 = calc.settle(S, '10', { seed: 3 });
    o1.state.linear[extra] = (o1.state.linear[extra] || 0) + 1;
    const oracle = calc.settle(o1.state, '100', { seed: 3 });
    assert.equal(stampedStr(plainOf(cont.state)), stampedStr(oracle.state));
  });

  it('raw + rebase: continuation in the shifted frame matches direct settle', () => {
    const calc = load(SPEC('economy.ill'));
    const S = init(calc, 'expect_settled');
    const direct = calc.settle(S, '100', { coalesce: true }).state;
    const r1 = calc.settle(S, '40', { coalesce: true, rebase: true, raw: true });
    const [bn, bd] = ratParts(r1.rebase);
    assert.equal(bd, 1n);
    const r2 = calc.settle(r1.state, String(100 - Number(bn)), { coalesce: true, raw: true });
    assert.equal(bagStr(plainOf(r2.state)), bagStr(direct));
  });
});
