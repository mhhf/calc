/**
 * TODO_0216 Phase 0 H6 — ground-bit survives snapshot/restore + binary bundle
 * (deferred-GREEN)
 *
 * Phase 1 adds an `isGround` side-table to Store. That side-table MUST be
 * serialised by snapshot() and rebuilt by restore()/store-binary, otherwise
 * a precompiled .ill.bin loaded through store-binary.js would return undefined
 * for every ground query. This test locks that contract.
 *
 * On HEAD it's skipped; when Phase 1 exports Store.isGround it starts running
 * automatically.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const Store = require('../lib/kernel/store');
const StoreBinary = require('../lib/engine/store-binary');

const HAS_GROUND = typeof Store.isGround === 'function';
const skip = !HAS_GROUND;

describe('TODO_0216 H6 — ground-bit survives snapshot/restore (deferred-GREEN)',
  { skip }, () => {
  let atomP, mvX, tGround, tOpen;

  before(() => {
    if (skip) return;
    Store.clear();
    atomP   = Store.put('atom', ['p']);
    mvX     = Store.put('metavar', ['X']);
    tGround = Store.put('tensor', [atomP, atomP]);
    tOpen   = Store.put('tensor', [atomP, mvX]);
  });

  it('after snapshot + restore, ground bit matches pre-snapshot classification', () => {
    const beforeG = Store.isGround(tGround);
    const beforeO = Store.isGround(tOpen);
    assert.strictEqual(beforeG, true);
    assert.strictEqual(beforeO, false);

    const snap = Store.snapshot();
    Store.clear();
    Store.restore(snap);

    assert.strictEqual(Store.isGround(tGround), true,
      'ground bit for a ground term lost across snapshot/restore');
    assert.strictEqual(Store.isGround(tOpen), false,
      'ground bit for an open term flipped after restore');
  });

  it('after binary serialize + deserialize, ground bit survives', () => {
    // Rebuild clean state because prior `it` mutated the store.
    Store.clear();
    const p = Store.put('atom', ['p']);
    const m = Store.put('metavar', ['X']);
    const g = Store.put('tensor', [p, p]);
    const o = Store.put('tensor', [p, m]);

    // Content-addressed allocation is stable across clear/re-put, so the
    // same hashes return after Store.restore(deserialize(buf)).
    const snap = Store.snapshot({ roots: { g, o } });
    const buf = StoreBinary.serialize(snap);
    Store.clear();
    Store.restore(StoreBinary.deserialize(buf));

    assert.strictEqual(Store.isGround(g), true,
      'ground term lost ground-bit through binary round-trip');
    assert.strictEqual(Store.isGround(o), false,
      'open term became "ground" after binary round-trip (would corrupt matching)');
  });
});
