/**
 * TODO_0216 Phase 0 H5 — Store ground-bit unit test matrix (deferred-GREEN)
 *
 * On HEAD this suite is SKIPPED: `Store.isGround` does not exist yet. When
 * Phase 1 (idea D — ground-bit in Store) lands, every test below starts
 * running automatically — no flag, no opt-in. The test matrix pre-locks the
 * contract we'll build against:
 *
 *   • atom                      → ground
 *   • metavar                   → NOT ground
 *   • nested w/o metavar        → ground
 *   • nested w/ metavar         → NOT ground
 *   • arrlit w/ metavar child   → NOT ground
 *   • acons-normalized cell     → ground iff both parts ground
 *   • post-collision rehash     → classification must match canonical form
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const Store = require('../lib/kernel/store');

const HAS_GROUND = typeof Store.isGround === 'function';
const skip = !HAS_GROUND;

describe('TODO_0216 H5 — Store.isGround matrix (deferred-GREEN)', { skip }, () => {
  let atomP, atomQ, mvX;

  before(() => {
    if (skip) return;
    Store.clear();
    atomP = Store.put('atom', ['p']);
    atomQ = Store.put('atom', ['q']);
    mvX   = Store.put('metavar', ['X']);
  });

  it('atom is ground', () => {
    assert.strictEqual(Store.isGround(atomP), true);
  });

  it('metavar is NOT ground', () => {
    assert.strictEqual(Store.isGround(mvX), false);
  });

  it('nested term without metavar is ground', () => {
    const t = Store.put('tensor', [atomP, atomQ]);
    assert.strictEqual(Store.isGround(t), true);
  });

  it('nested term with metavar is NOT ground', () => {
    const t = Store.put('tensor', [atomP, mvX]);
    assert.strictEqual(Store.isGround(t), false);
  });

  it('arrlit with a metavar child is NOT ground', () => {
    const arr = Store.putArray(new Uint32Array([atomP, mvX, atomQ]));
    assert.strictEqual(Store.isGround(arr), false);
  });

  it('arrlit with only ground children IS ground', () => {
    const arr = Store.putArray(new Uint32Array([atomP, atomQ]));
    assert.strictEqual(Store.isGround(arr), true);
  });

  it('acons-normalized cell is ground iff both head and tail are ground', () => {
    // acons is ILL's list-cons; it's a binary term.
    const aconsGG = Store.put('acons', [atomP, atomQ]);
    const aconsGM = Store.put('acons', [atomP, mvX]);
    const aconsMG = Store.put('acons', [mvX,   atomQ]);
    assert.strictEqual(Store.isGround(aconsGG), true);
    assert.strictEqual(Store.isGround(aconsGM), false);
    assert.strictEqual(Store.isGround(aconsMG), false);
  });

  it('post-collision rehash: ground classification is structure-determined', () => {
    // Build the same structure twice — content-addressed, so the second put
    // returns the identical hash. The ground bit must be stable across the
    // rehash (no stale-cache hazard).
    const t1 = Store.put('tensor', [atomP, atomQ]);
    const t2 = Store.put('tensor', [atomP, atomQ]);
    assert.strictEqual(t1, t2, 'content-addressed store must dedupe');
    assert.strictEqual(Store.isGround(t1), Store.isGround(t2));
    assert.strictEqual(Store.isGround(t1), true);

    // Insert a metavar-bearing sibling and re-check ground bit on t1.
    const t3 = Store.put('tensor', [atomP, mvX]);
    assert.notStrictEqual(t1, t3);
    assert.strictEqual(Store.isGround(t1), true, 'unrelated put must not flip bit');
    assert.strictEqual(Store.isGround(t3), false);
  });

  it('deep nested (depth 5) propagates non-ground upward', () => {
    let acc = mvX;
    for (let i = 0; i < 5; i++) {
      acc = Store.put('tensor', [atomP, acc]);
    }
    assert.strictEqual(Store.isGround(acc), false);
  });
});
