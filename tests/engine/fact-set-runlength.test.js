/**
 * Run-length FactSet unit tests (TODO_0277 audit — the representation was
 * only covered transitively through the till suites).
 *
 * Pins the representation contract directly:
 *   - multiplicity lives in the parallel counts array: one entry per
 *     distinct hash, O(distinct) ops
 *   - Zobrist hashes are bit-identical to the classic representation
 *   - the arena records counted ops (4th field) and undo restores exactly
 *   - snapshots (single and bulk) are count-independent of the original
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { FactSet, Arena } from '../../lib/engine/fact-set.js';

const RL = { runLength: true };
const TAG = 3;
const H1 = 1001, H2 = 1002;

describe('FactSet run-length representation', () => {
  it('n-insert lands as ONE entry with count n; hash matches classic', () => {
    const rl = new FactSet(8, RL);
    rl.insert(TAG, H1, null, 5);
    assert.equal(rl.count(TAG, H1), 5);
    assert.equal(rl.lens[TAG], 1, 'one entry, not five');
    assert.equal(rl.total, 5);
    const classic = new FactSet(8);
    for (let i = 0; i < 5; i++) classic.insert(TAG, H1, null);
    assert.equal(rl.hash, classic.hash, 'Zobrist bit-identical across representations');
  });

  it('partial remove decrements the count in place', () => {
    const rl = new FactSet(8, RL);
    rl.insert(TAG, H1, null, 5);
    rl.remove(TAG, H1, null, 3);
    assert.equal(rl.count(TAG, H1), 2);
    assert.equal(rl.lens[TAG], 1);
    assert.equal(rl.total, 2);
    const classic = new FactSet(8);
    classic.insert(TAG, H1, null, 2);
    assert.equal(rl.hash, classic.hash);
  });

  it('full remove deletes the entry; empty set hashes to 0', () => {
    const rl = new FactSet(8, RL);
    rl.insert(TAG, H1, null, 5);
    rl.remove(TAG, H1, null, 5);
    assert.equal(rl.lens[TAG], 0);
    assert.equal(rl.total, 0);
    assert.equal(rl.hash, 0);
  });

  it('arena undo restores counted inserts and removes exactly', () => {
    const rl = new FactSet(8, RL);
    const arena = new Arena(64);
    rl.insert(TAG, H1, null, 2);
    const h0 = rl.hash, t0 = rl.total;
    const cp = arena.checkpoint();
    rl.insert(TAG, H2, arena, 5);
    rl.remove(TAG, H1, arena, 1);
    rl.undo(arena, cp);
    assert.equal(rl.count(TAG, H2), 0, '5-insert undone');
    assert.equal(rl.count(TAG, H1), 2, '1-remove undone');
    assert.equal(rl.hash, h0);
    assert.equal(rl.total, t0);
  });

  it('mutation counter bumps on every counted op (cache-invalidation contract)', () => {
    const rl = new FactSet(8, RL);
    const m0 = rl.mut;
    rl.insert(TAG, H1, null, 5);
    assert.ok(rl.mut > m0);
    const m1 = rl.mut;
    rl.remove(TAG, H1, null, 2);
    assert.ok(rl.mut > m1);
  });

  it('snapshot: counts are independent of the original', () => {
    const rl = new FactSet(8, RL);
    rl.insert(TAG, H1, null, 7);
    rl.insert(TAG, H2, null, 3);
    const snap = rl.snapshot();
    rl.remove(TAG, H1, null, 4);
    assert.equal(rl.count(TAG, H1), 3);
    assert.equal(snap.count(TAG, H1), 7, 'snapshot count untouched by later mutation');
    assert.equal(snap.count(TAG, H2), 3);
  });

  it('snapshotBulk: shared-buffer views stay isolated from later mutations', () => {
    const rl = new FactSet(8, RL);
    rl.insert(TAG, H1, null, 7);
    rl.insert(TAG, H2, null, 3);
    const snap = rl.snapshotBulk();
    rl.remove(TAG, H1, null, 4);
    rl.insert(TAG, H2, null, 9);
    assert.equal(snap.count(TAG, H1), 7);
    assert.equal(snap.count(TAG, H2), 3);
    assert.equal(rl.count(TAG, H2), 12);
  });
});
