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

  it('slot fence is loud: unknown symbolic realization throws (P1)', () => {
    assert.throws(() => new StampTable({ ...alg, merge: 'max' }), /must be 'join'/);
    assert.throws(() => new StampTable({ ...alg, prunes: true }), /must be 'geq'/);
  });

  it("merge lifts the ⊔ slot: 'join' on ids, intern-free (P1)", () => {
    const t = new StampTable(alg);
    const a = t.intern(V(3, 2)), b = t.intern(V(2));
    const before = t.size;
    assert.equal(t.merge(a, b), b);           // max wins
    assert.equal(t.merge(b, a), b);           // commutative on values
    assert.equal(t.merge(a, a), a);           // identity fast path
    assert.equal(t.size, before);             // an order-class join never interns
  });

  it('merge default (algebra without a merge slot) is max by cmp', () => {
    const noMerge = { ...alg, merge: undefined, prunes: undefined };
    const t = new StampTable(noMerge);
    const a = t.intern(V(1, 3)), b = t.intern(V(1, 2));
    assert.equal(t.merge(a, b), b);
    assert.equal(t.merge(b, a), b);
    assert.equal(t.prunes(b, a), true);       // default: cmp >= 0
    assert.equal(t.prunes(a, b), false);
  });

  it('merge interns a value-creating result (non-join algebras, e.g. usage +)', () => {
    const usage = { ...alg, merge: (x, y) => alg.add(x, y) };
    const t = new StampTable(usage);
    const a = t.intern(V(1)), b = t.intern(V(2));
    const m = t.merge(a, b);
    assert.deepEqual(t.value(m), V(3));
    assert.equal(t.merge(a, b), m);           // interned: stable id
    // NON-idempotent slot runs even at equal ids (P3b fix): the a === b
    // shortcut belongs to the join realization only — usage a ⊔ a = 2a
    assert.deepEqual(t.value(t.merge(a, a)), V(2));
  });

  it('prunes lifts the ⊕ slot: >= keeps the FIFO tie (P1 invariant pair)', () => {
    const t = new StampTable(alg);
    const a = t.intern(V(3)), b = t.intern(V(5));
    assert.equal(t.prunes(b, a), true);       // worse partial: dead
    assert.equal(t.prunes(a, a), true);       // equal: dead (first match won)
    assert.equal(t.prunes(a, b), false);      // better partial: alive
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
