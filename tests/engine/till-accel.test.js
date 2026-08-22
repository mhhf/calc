/**
 * Periodic-orbit acceleration (TODO_0277 approach 4) — accel.js.
 *
 * Pins:
 *   - exact-state equivalence: settle with accelerate reaches the SAME
 *     stamped multiset as plain settle (coalesce-normalized) on producer
 *     economies, capped-stock economies, and the full PP2 shell state
 *   - event accounting: real events + skipped events = plain event count
 *   - deep time is O(1): a 10^6 horizon settles without firing 10^6-order
 *     events (skipped dominates)
 *   - windows (spoilage) and frozen fixtures (red hero, space) survive
 *     jumps in place
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import convert from '../../lib/engine/convert.js';
import { loadTill as load, atom, stampedStr } from './till-helpers.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');

function run(calc, mkState, T) {
  const plain = calc.settle(mkState(), T, { coalesce: true, maxSteps: 10000000 });
  const fast = calc.settle(mkState(), T, { accelerate: true, maxSteps: 10000000 });
  const skipped = (fast.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
  return { plain, fast, skipped };
}

describe('till acceleration — exact-orbit jumps', () => {
  const calc = load(PP2);

  it('producer economy: identical state, events fully accounted', () => {
    const mk = () => ({ linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} });
    const { plain, fast, skipped } = run(calc, mk, '1000');
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
    assert.equal(fast.events.length + skipped, plain.events.length);
    assert.ok(skipped > 0, 'expected an actual jump');
  });

  it('capped-stock economy (sawmill+smith on growing surplus): identical state', () => {
    const mk = () => ({
      linear: {
        [atom('lumberjack')]: 1, [atom('quarry')]: 1,
        [atom('sawmill')]: 1, [atom('smith')]: 1,
      }, persistent: {},
    });
    const { plain, fast, skipped } = run(calc, mk, '2000');
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
    assert.equal(fast.events.length + skipped, plain.events.length);
    assert.ok(skipped > 0, 'expected an actual jump');
  });

  it('full PP2 shell state (menus, spoilage, frozen hero): identical state', () => {
    const mk = () => convert.decomposeQuery(calc.splitQueries.get('expect_shell_start').lhsHash);
    const { plain, fast, skipped } = run(calc, mk, '3000');
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
    assert.equal(fast.events.length + skipped, plain.events.length);
    assert.ok(skipped > 0, 'expected an actual jump');
  });

  it('deep time is O(1): 10^6 horizon without 10^6-order firings', () => {
    const mk = () => ({ linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} });
    const r = calc.settle(mk(), '1000000', { accelerate: true, maxSteps: 10000000 });
    const skipped = (r.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
    assert.ok(r.events.length < 100000, `fired ${r.events.length} events — acceleration failed`);
    assert.ok(skipped > 5000000, `skipped only ${skipped}`);
    assert.equal(Object.keys(r.state.linear).length, 6);   // flat live state
  });
});
