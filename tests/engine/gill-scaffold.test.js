/**
 * gill scaffold (TODO_0284 P2) — fast-suite guard for the new calculus.
 *
 * Pins:
 *   - gill.calc declares the dist grade sort; its value fence is ℚ≥0
 *   - the FFI meta completes the tower collapse for min/max (num.min/
 *     num.max dispatch; rat.qmin/rat.qmax registered)
 *   - a forward rule with a `!min` theory premise settles to the lesser
 *     argument, FFI face and clause face agreeing hash-for-hash (the
 *     FFI-principle gate in miniature; the full spec suite is test:gill)
 *   - the theory engine speaks min/max (loud-typo rejection stays sound)
 *   - the sequent calculus loads with the gill theory attached
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import * as ffi from '../../calculus/ill/lib/ffi/index.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { timedSubset } from '../../lib/engine/timed/timed-views.js';
import gillConfig, { gillTheory, loadGillSequent } from '../../calculus/gill/calculus-config.js';

const SPEC = path.join(import.meta.dirname, '../../calculus/gill/tests/forward/minmax.gill');
const bin = (n) => Store.put1('binlit', n);
const mv = (name) => Store.put('metavar', [name]);

describe('gill scaffold (P2)', () => {
  let calc;
  before(() => {
    calc = mde.load(SPEC, { calculusConfig: gillConfig, cache: false });
  });

  it('gill.calc declares dist <: grade with a ℚ≥0 value fence', () => {
    const sorts = gillConfig.sorts;
    assert.ok(sorts.calc.edges.some(([a, b]) => a === 'dist' && b === 'grade'));
    assert.ok(sorts.lit.fences.dist(putRat(3n, 2n)));
    assert.ok(sorts.lit.fences.dist(bin(0n)));
    assert.ok(!sorts.lit.fences.dist(putRat(-1n, 2n)));
  });

  it('FFI meta routes the collapsed min/max onto the tower dispatchers', () => {
    assert.equal(gillConfig.ffi.meta.min.ffi, 'num.min');
    assert.equal(gillConfig.ffi.meta.max.ffi, 'num.max');
    for (const p of ['num.min', 'num.max', 'rat.qmin', 'rat.qmax']) {
      assert.equal(typeof ffi.get(p), 'function', p);
    }
    // ILL's shared defaults are untouched: bin-only min/max stay
    assert.equal(ffi.defaultMeta.min.ffi, 'arithmetic.min');
  });

  it('!min theory premise settles to the lesser argument — FFI ∥ clause agreement', () => {
    const entry = calc.splitQueries.get('expect_pick_min');
    const pattern = convert.decomposeQuery(entry.rhsHash);
    for (const useFFI of [true, false]) {
      const res = calc.settle(convert.decomposeQuery(entry.lhsHash), 0, { maxSteps: 100, useFFI });
      assert.ok(timedSubset(pattern, res.state), `useFFI: ${useFFI}`);
    }
  });

  it('theory engine: min/max derivable over prelude/num.gill, typos rejected', () => {
    const theta = gillTheory.prove(Store.put('min', [bin(7n), putRat(13n, 2n), mv('M')]));
    assert.ok(theta);
    assert.equal(theta[0][1], putRat(13n, 2n));
    assert.ok(gillTheory.has('min'));
    assert.ok(gillTheory.has('max'));
    assert.ok(!gillTheory.has('mni'));
  });

  it('sequent calculus loads with the gill theory attached', () => {
    const seq = loadGillSequent();
    assert.strictEqual(seq.theory, gillTheory);
    assert.ok(seq.parse('{ a }@3'));
  });
});
