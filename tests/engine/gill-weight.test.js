/**
 * gill weight axis (TODO_0284 P3b) — the measure-class instance as
 * SHIPPED data: registry routing, the scheduler fence, and the
 * StampTable running a non-idempotent value-level merge slot.
 *
 * weightGrades is the 0292/will handoff: will's decimation loop consumes
 * exactly this record (⊗ = ·, ⊖ = ÷, ⊔ = ·, ⊕ = sum|sample via
 * prf.js sampleIndex). Here we pin what must be true BEFORE will exists:
 *   - the by-sort registry routes woplus (weight) → weightGrades
 *   - buildTimedConfig rejects a weight-axis run (P1b: settle commits
 *     one alternative per instant — mass would be silently discarded)
 *   - the StampTable's function-slot path is exact and non-idempotent:
 *     w ⊔ w = w² (the a === b join shortcut must NOT apply — the bug
 *     this instance caught)
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { StampTable } from '../../lib/timed/labels.js';
import { buildTimedConfig } from '../../lib/timed/timed.js';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import gillConfig, { weightGrades, distGrades, gillGradeRegistry, gradeAlgebraFor } from '../../calculus/gill/calculus-config.js';

const V = (n, d = 1n) => [BigInt(n), BigInt(d)];

describe('gill weight axis (P3b)', () => {
  it('registry: woplus routes to weightGrades; order axes unaffected', () => {
    assert.strictEqual(gradeAlgebraFor('woplus'), weightGrades);
    assert.strictEqual(gillGradeRegistry.bySort.weight, weightGrades);
    assert.strictEqual(gradeAlgebraFor('haul'), distGrades);
    assert.strictEqual(gradeAlgebraFor('monad'), tillGrades);
  });

  it('the instance is the measure record: ⊗=·, ⊖=÷ (null at 0), no prunes', () => {
    const w = weightGrades.values;
    assert.deepEqual(w.add(V(1, 2n), V(1, 3n)), V(1, 6n));
    assert.deepEqual(w.sub(V(1, 6n), V(1, 3n)), V(1, 2n));   // residual: compose(b, r) = a
    assert.equal(w.sub(V(1, 2n), V(0)), null);               // mass-0 fence
    assert.deepEqual(w.unit, V(1));
    assert.ok(!('prunes' in w));
    assert.ok(!('scale' in w) && !('floorDiv' in w));         // time-only slots absent, loudly
    assert.deepEqual(weightGrades.aggregate, { class: 'measure', realizations: ['sum', 'sample'] });
    assert.ok(Object.isFrozen(weightGrades) && Object.isFrozen(weightGrades.values));
  });

  it('scheduler fence: buildTimedConfig rejects the weight axis (P1b)', () => {
    assert.throws(() => buildTimedConfig({ ...gillConfig, grades: weightGrades }),
      /measure-class aggregation is an execution mode/);
  });

  describe('StampTable over weightGrades.values (the function-slot path)', () => {
    it('compose multiplies through the ⊗ slot', () => {
      const t = new StampTable(weightGrades.values);
      assert.equal(t.unitId, 0);
      assert.deepEqual(t.value(t.unitId), V(1));
      const half = t.intern(V(1, 2n));
      assert.deepEqual(t.value(t.compose(half, V(1, 3n))), V(1, 6n));
      assert.equal(t.compose(half, V(1)), half);              // unit fast path
    });

    it('merge is · on values: value-creating, interned, deduped', () => {
      const t = new StampTable(weightGrades.values);
      const half = t.intern(V(1, 2n)), third = t.intern(V(1, 3n));
      const m = t.merge(half, third);
      assert.deepEqual(t.value(m), V(1, 6n));
      assert.equal(t.merge(half, third), m);                  // stable id
      assert.equal(t.merge(third, half), m);                  // commutative
    });

    it('NON-idempotent: w ⊔ w = w² even at equal ids (the P3b fix)', () => {
      const t = new StampTable(weightGrades.values);
      const half = t.intern(V(1, 2n));
      const sq = t.merge(half, half);
      assert.notEqual(sq, half);
      assert.deepEqual(t.value(sq), V(1, 4n));
      // and merging with the unit dedups back to the same id (no new entry)
      const before = t.size;
      assert.equal(t.merge(half, t.unitId), half);
      assert.equal(t.size, before);
    });
  });
});
