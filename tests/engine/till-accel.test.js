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
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import convert from '../../lib/engine/convert.js';
import { loadTill as load, atom, stampedStr } from './till-helpers.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');

let _dir = null;
function prog(text) {
  if (!_dir) _dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-accel-'));
  const f = path.join(_dir, `p${fs.readdirSync(_dir).length}.ill`);
  fs.writeFileSync(f, text);
  return load(f);
}

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

describe('till acceleration — deadline and nondeterminism guards (audit)', () => {
  it('ground before-deadline: jump capped below it, state identical (audit repro: 96 vs 50)', () => {
    // The cycle recurs exactly while the absolute deadline approaches; an
    // uncapped jump replayed wood-destruction past t=200. The cap jumps to
    // just below the deadline, normal firing carries the crossing.
    const calc = prog('lumber: type.\nwood: type.\n' +
      'lj: lumber -o { lumber * wood }@1.\n' +
      'mk: wood * before 200 -o { I }.\n');
    const mk = () => ({ linear: { [atom('lumber')]: 1 }, persistent: {} });
    const plain = calc.settle(mk(), '1000', { coalesce: true, maxSteps: 10000000 });
    const fast = calc.settle(mk(), '1000', { accelerate: true, maxSteps: 10000000 });
    const skipped = (fast.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
    assert.equal(fast.events.length + skipped, plain.events.length);
    assert.ok(skipped > 0, 'pre-deadline orbit must still accelerate');
  });

  it('covariant before-window (Q+c): moves with the cycle, still accelerates', () => {
    const calc = prog('#import(' + path.resolve('calculus/till/prelude/rat.ill') + ')\n\n' +
      'aa: type.\nbb: type.\n' +
      'spawn: aa -o { aa * bb }@1.\n' +
      'use: bb@Q * before (Q + 2) -o { I }.\n');
    const mk = () => ({ linear: { [atom('aa')]: 1 }, persistent: {} });
    const plain = calc.settle(mk(), '500', { coalesce: true, maxSteps: 10000000 });
    const fast = calc.settle(mk(), '500', { accelerate: true, maxSteps: 10000000 });
    const skipped = (fast.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
    assert.ok(skipped > 0, 'covariant deadlines must not block certification');
  });

  it('active woplus program: certification refused (nondet guard), state identical per seed', () => {
    const calc = prog('wa: type.\nwb: type.\nwc: type.\n' +
      'flip: wa -o { woplus 1/2 wb wc }@1.\n' +
      'rb: wb -o { wa }@1.\n' +
      'rc: wc -o { wa }@1.\n');
    const mk = () => ({ linear: { [atom('wa')]: 1 }, persistent: {} });
    const plain = calc.settle(mk(), '300', { coalesce: true, seed: 7, maxSteps: 10000000 });
    const fast = calc.settle(mk(), '300', { accelerate: true, seed: 7, maxSteps: 10000000 });
    const skipped = (fast.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
    assert.equal(skipped, 0, 'woplus draws must suppress every orbit certification');
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
  });
});
