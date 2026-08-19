/**
 * D16 productivity lint — TODO_0265 Phase 5 (round-13 residue).
 *
 * Conservative load-time WARNING on zero-delay rule cycles: sound as a
 * warning (self-covering rules and token-non-decreasing pred cycles), NOT
 * complete (windows/depletion can break a flagged cycle — the runtime
 * Zeno guard stays). Precision pins: token-DECREASING programs (the duel),
 * positive-delay self-loops (productivity.ill), instant-feeding DAGs and
 * unknowable counts (!_W) must all stay QUIET.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';

const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
const FIX = (f) => path.join(import.meta.dirname, '../fixtures', f);
const load = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });

describe('till D16 productivity lint', () => {
  it('flags a zero-delay self-cycle (till-zeno)', () => {
    const calc = load(FIX('till-zeno.ill'));
    assert.equal(calc.timedLint.length, 1);
    assert.deepEqual(calc.timedLint[0], { kind: 'self-cycle', rule: 'ping0' });
  });

  it('flags a two-rule zero-delay cycle via the pred graph', () => {
    const calc = load(FIX('till-cycle2.ill'));
    assert.equal(calc.timedLint.length, 1);
    assert.equal(calc.timedLint[0].kind, 'cycle');
    assert.deepEqual([...calc.timedLint[0].rules].sort(), ['r1', 'r2']);
  });

  it('stays quiet on token-decreasing races (the duel depletes)', () => {
    // fight consumes {rock, sci}, produces one of them — every alternative
    // is token-decreasing, so the "cycle" rock→rock terminates by depletion.
    assert.deepEqual(load(FIX('till-duel.ill')).timedLint, []);
  });

  it('stays quiet on positive-delay self-loops (productive, D16)', () => {
    assert.deepEqual(load(SPEC('productivity.ill')).timedLint, []);
  });

  it('stays quiet on zero-delay DAGs and !_W cohort binds', () => {
    assert.deepEqual(load(FIX('till-instant-enable.ill')).timedLint, []);
    assert.deepEqual(load(FIX('till-instant-transfer.ill')).timedLint, []);
  });

  it('stays quiet on the spec programs (economy, schedule, spoilage, read, grades)', () => {
    for (const f of ['economy.ill', 'schedule.ill', 'spoilage.ill', 'read.ill', 'grades.ill']) {
      assert.deepEqual(load(SPEC(f)).timedLint, [], f);
    }
  });
});
