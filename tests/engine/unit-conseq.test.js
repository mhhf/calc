/**
 * Multiplicative unit in forward-rule bodies (TODO_0265 Phase 6): `I`
 * decomposes to nothing in BOTH zones — affine discard `A -o { I }` is the
 * empty consequent, and an antecedent `I` is a no-op pattern. Before the
 * fix, expandChoice/flattenAnte fell through to the default branch and the
 * unit leaked into the state as a literal linear fact (`1@0`), polluting
 * exact-cover checks and observables.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import mde from '../../lib/engine/index.js';
import { FIX, loadTill, atom, stampedStr, bagStr } from './till-helpers.js';

const S = (facts) => ({
  linear: Object.fromEntries(facts.map(n => [atom(n), 1])),
  persistent: {},
});

describe('unit consequent — timed engine', () => {
  it('A -o { I } discards without leaking a unit fact', () => {
    const calc = loadTill(FIX('till-unit-conseq.ill'));
    const r = calc.settle(S(['junk']), '10');
    assert.equal(stampedStr(r.state), '');
  });

  it('tensored unit in a consequent contributes nothing', () => {
    const calc = loadTill(FIX('till-unit-conseq.ill'));
    const r = calc.settle(S(['src']), '10');
    assert.equal(stampedStr(r.state), 'out@0x1');
  });

  it('antecedent I is a no-op pattern', () => {
    const calc = loadTill(FIX('till-unit-conseq.ill'));
    const r = calc.settle(S(['pulse']), '10');
    assert.equal(stampedStr(r.state), 'done@0x1');
  });
});

describe('unit consequent — untimed engine', () => {
  it('A -o { I } discards without leaking a unit fact', () => {
    const calc = mde.load(FIX('till-unit-conseq.ill'), { cache: false });
    const r = calc.exec(S(['junk', 'src', 'pulse']));
    assert.equal(bagStr(r.state), 'donex1,outx1');
  });
});
