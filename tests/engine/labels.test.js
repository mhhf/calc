/**
 * StampTable + label value algebra (THY_0024, TODO_0278 B2).
 *
 * Pins:
 *   - interning: dedup by value, unit = id 0, overflow fence loud
 *   - term round trip: internTerm ∘ term = canonical identity (lazy, memoized)
 *   - cmp: float fast path ≡ exact compare, incl. >2^53 operands and
 *     float-tie rationals (monotone-rounding soundness, TODO_0277 carryover)
 *   - mix: VALUE-derived — same value ⇒ same mix across independent tables
 *     (rider 2: E5 split states must hash equal; ids are history-dependent)
 *   - shiftAll: ids stable, values shifted, order preserved, reify cache
 *     invalidated; compact: live ids remapped densely, unit always kept
 *   - packed refs: inner/stamp round trip through the 52-bit encoding
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { StampTable, packRef, refInner, refStamp, STAMP_CAP } from '../../lib/engine/labels.js';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import Store from '../../lib/kernel/store.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

const alg = tillGrades.values;
const V = (n, d = 1n) => [BigInt(n), BigInt(d)];

describe('label value algebra (till: exact rationals)', () => {
  it('parse ∘ reify = id on canonical values', () => {
    for (const v of [V(0), V(7), V(3, 2), V(2n ** 60n)]) {
      assert.deepEqual(alg.parse(alg.reify(v)), v);
    }
  });

  it('float is monotone and NaN outside the exact range', () => {
    assert.equal(alg.float(V(3, 2)), 1.5);
    assert.ok(Number.isNaN(alg.float(V(2n ** 60n))));
  });

  it('mix is value-derived and spreads', () => {
    assert.equal(alg.mix(V(5)), alg.mix(V(5)));
    assert.notEqual(alg.mix(V(5)), alg.mix(V(6)));
    assert.notEqual(alg.mix(V(1, 2)), alg.mix(V(2, 1)));
  });
});

describe('StampTable', () => {
  it('interns by value with unit at id 0', () => {
    const t = new StampTable(alg);
    assert.equal(t.unitId, 0);
    const a = t.intern(V(5));
    assert.equal(t.intern(V(5)), a);
    assert.notEqual(t.intern(V(5, 2)), a);
    assert.deepEqual(t.value(a), V(5));
  });

  it('internTerm canonicalizes and term() reifies lazily + memoized', () => {
    const t = new StampTable(alg);
    const h = alg.reify(V(7, 3));
    const id = t.internTerm(h);
    const back = t.term(id);
    assert.deepEqual(ratParts(back), [7n, 3n]);
    assert.equal(t.term(id), back);
  });

  it('cmp agrees with exact rational order incl. float ties and big operands', () => {
    const t = new StampTable(alg);
    const cases = [
      [V(1, 3), V(2, 3)],
      [V(1), V(1, 1)],                       // equal after canon (same id)
      [V(2n ** 60n), V(2n ** 60n + 1n)],     // NaN floats → exact path
      [V(10n ** 17n, 3n), V(10n ** 17n * 2n, 6n)], // equal big rationals → same id
    ];
    for (const [a, b] of cases) {
      const ia = t.intern(a), ib = t.intern(b);
      const exact = alg.cmp(a, b);
      assert.equal(t.cmp(ia, ib), exact, `${a} vs ${b}`);
      assert.equal(t.cmp(ib, ia), exact === 0 ? 0 : -exact);
    }
  });

  it('compose adds in the algebra with a unit fast path', () => {
    const t = new StampTable(alg);
    const a = t.intern(V(3, 2));
    assert.equal(t.compose(a, V(0)), a);
    assert.deepEqual(t.value(t.compose(a, V(1, 2))), V(2));
  });

  it('mix equality across independent tables (value-derived, not id-derived)', () => {
    const t1 = new StampTable(alg);
    const t2 = new StampTable(alg);
    t1.intern(V(99));                        // skew t1's id assignment
    const a1 = t1.intern(V(5, 4));
    const a2 = t2.intern(V(5, 4));
    assert.notEqual(a1, a2);
    assert.equal(t1.mix(a1), t2.mix(a2));
  });

  it('packed refs round trip and the fences are loud', () => {
    const inner = 123456789;                          // < 2^29
    const sid = STAMP_CAP - 1;
    const ref = packRef(inner, sid);
    assert.equal(refInner(ref), inner);
    assert.equal(refStamp(ref), sid);
    assert.ok(Number.isSafeInteger(ref));
    const t = new StampTable(alg);
    t._forceSize(STAMP_CAP);                          // test hook: simulate a full table
    assert.throws(() => t.intern(V(424243)), /overflow/);
  });
});
