const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { FactSet, Arena, State, hashFactEntry, lowerBound, fromObject, toObject } = require('../../lib/engine/fact-set');

describe('lowerBound', () => {
  it('returns 0 for empty range', () => {
    const buf = new Int32Array(0);
    assert.equal(lowerBound(buf, 0, 0, 42), 0);
  });

  it('returns 0 when val is less than all elements', () => {
    const buf = new Int32Array([10, 20, 30]);
    assert.equal(lowerBound(buf, 0, 3, 5), 0);
  });

  it('returns length when val is greater than all elements', () => {
    const buf = new Int32Array([10, 20, 30]);
    assert.equal(lowerBound(buf, 0, 3, 35), 3);
  });

  it('finds exact match position', () => {
    const buf = new Int32Array([10, 20, 30]);
    assert.equal(lowerBound(buf, 0, 3, 20), 1);
  });

  it('finds leftmost position for duplicates', () => {
    const buf = new Int32Array([10, 20, 20, 20, 30]);
    assert.equal(lowerBound(buf, 0, 5, 20), 1);
  });

  it('returns insertion point for missing values', () => {
    const buf = new Int32Array([10, 30, 50]);
    assert.equal(lowerBound(buf, 0, 3, 20), 1);
    assert.equal(lowerBound(buf, 0, 3, 40), 2);
  });

  it('respects lo/hi bounds', () => {
    const buf = new Int32Array([5, 10, 20, 30, 40]);
    assert.equal(lowerBound(buf, 1, 4, 15), 2);
    assert.equal(lowerBound(buf, 2, 4, 20), 2);
  });
});

describe('hashFactEntry', () => {
  it('returns different values for different counts', () => {
    const h1 = hashFactEntry(42, 1);
    const h2 = hashFactEntry(42, 2);
    assert.notEqual(h1, h2);
  });

  it('returns different values for different hashes', () => {
    const h1 = hashFactEntry(42, 1);
    const h2 = hashFactEntry(43, 1);
    assert.notEqual(h1, h2);
  });

  it('returns unsigned 32-bit value', () => {
    const h = hashFactEntry(999999, 5);
    assert.ok(h >= 0 && h <= 0xFFFFFFFF);
  });
});

describe('Arena', () => {
  it('checkpoint returns cursor position', () => {
    const arena = new Arena(32);
    assert.equal(arena.checkpoint(), 0);
    arena.push4(1, 2, 3, 4);
    assert.equal(arena.checkpoint(), 4);
  });

  it('push4 writes 4 values', () => {
    const arena = new Arena(32);
    arena.push4(10, 20, 30, 40);
    assert.equal(arena.buf[0], 10);
    assert.equal(arena.buf[1], 20);
    assert.equal(arena.buf[2], 30);
    assert.equal(arena.buf[3], 40);
  });

  it('restore resets cursor', () => {
    const arena = new Arena(32);
    const cp = arena.checkpoint();
    arena.push4(1, 2, 3, 4);
    arena.push4(5, 6, 7, 8);
    assert.equal(arena.cursor, 8);
    arena.restore(cp);
    assert.equal(arena.cursor, 0);
  });

  it('grows when capacity exceeded', () => {
    const arena = new Arena(8); // 8 ints = 2 records
    arena.push4(1, 2, 3, 4);
    arena.push4(5, 6, 7, 8);
    arena.push4(9, 10, 11, 12); // triggers grow
    assert.equal(arena.cursor, 12);
    assert.equal(arena.buf[8], 9);
  });
});

describe('FactSet', () => {
  let fs;

  beforeEach(() => {
    fs = new FactSet(32);
  });

  it('starts empty', () => {
    assert.equal(fs.total, 0);
    assert.equal(fs.hash, 0);
    assert.equal(fs.groupLen(5), 0);
    assert.equal(fs.has(5, 42), false);
    assert.equal(fs.count(5, 42), 0);
  });

  it('insert adds fact to correct group', () => {
    fs.insert(5, 100, null);
    assert.equal(fs.total, 1);
    assert.equal(fs.groupLen(5), 1);
    assert.equal(fs.has(5, 100), true);
    assert.equal(fs.count(5, 100), 1);
  });

  it('insert maintains sorted order', () => {
    fs.insert(3, 30, null);
    fs.insert(3, 10, null);
    fs.insert(3, 20, null);
    const g = fs.group(3);
    assert.deepEqual([...g], [10, 20, 30]);
  });

  it('insert handles duplicates (multiset)', () => {
    fs.insert(3, 42, null);
    fs.insert(3, 42, null);
    fs.insert(3, 42, null);
    assert.equal(fs.count(3, 42), 3);
    assert.equal(fs.groupLen(3), 3);
    assert.equal(fs.total, 3);
  });

  it('remove removes one instance', () => {
    fs.insert(3, 42, null);
    fs.insert(3, 42, null);
    fs.remove(3, 42, null);
    assert.equal(fs.count(3, 42), 1);
    assert.equal(fs.groupLen(3), 1);
    assert.equal(fs.total, 1);
  });

  it('remove last instance leaves group empty', () => {
    fs.insert(3, 42, null);
    fs.remove(3, 42, null);
    assert.equal(fs.count(3, 42), 0);
    assert.equal(fs.groupLen(3), 0);
    assert.equal(fs.total, 0);
    assert.equal(fs.hash, 0);
  });

  it('remove of non-existent fact is no-op', () => {
    fs.insert(3, 10, null);
    fs.remove(3, 999, null);
    assert.equal(fs.total, 1);
    assert.equal(fs.groupLen(3), 1);
  });

  it('remove maintains sorted order', () => {
    fs.insert(3, 10, null);
    fs.insert(3, 20, null);
    fs.insert(3, 30, null);
    fs.remove(3, 20, null);
    assert.deepEqual([...fs.group(3)], [10, 30]);
  });

  it('Zobrist hash is order-independent', () => {
    const fs1 = new FactSet(32);
    const fs2 = new FactSet(32);
    fs1.insert(3, 10, null);
    fs1.insert(3, 20, null);
    fs2.insert(3, 20, null);
    fs2.insert(3, 10, null);
    assert.equal(fs1.hash, fs2.hash);
  });

  it('Zobrist hash is multiset-safe (add twice != XOR cancel)', () => {
    const fs1 = new FactSet(32);
    fs1.insert(3, 42, null);
    const h1 = fs1.hash;
    fs1.insert(3, 42, null);
    const h2 = fs1.hash;
    assert.notEqual(h1, h2); // Adding second copy changes hash
    assert.notEqual(h2, 0);  // Two copies don't cancel to zero
  });

  it('Zobrist hash restores after insert+remove roundtrip', () => {
    fs.insert(3, 10, null);
    fs.insert(5, 20, null);
    const h0 = fs.hash;
    fs.insert(3, 30, null);
    fs.remove(3, 30, null);
    assert.equal(fs.hash, h0);
  });

  it('insert+remove with arena undo roundtrip', () => {
    const arena = new Arena(256);
    fs.insert(3, 10, null);
    fs.insert(5, 20, null);
    const h0 = fs.hash;
    const t0 = fs.total;

    const cp = arena.checkpoint();
    fs.insert(3, 30, arena);
    fs.insert(3, 40, arena);
    fs.remove(5, 20, arena);

    assert.equal(fs.total, 3); // 10, 30, 40
    assert.notEqual(fs.hash, h0);

    fs.undo(arena, cp);
    assert.equal(fs.total, t0);
    assert.equal(fs.hash, h0);
    assert.deepEqual([...fs.group(3)], [10]);
    assert.deepEqual([...fs.group(5)], [20]);
  });

  it('snapshot is independent copy', () => {
    fs.insert(3, 10, null);
    fs.insert(3, 20, null);
    const snap = fs.snapshot();

    // Modify original
    fs.insert(3, 30, null);
    assert.equal(fs.groupLen(3), 3);
    assert.equal(snap.groupLen(3), 2); // snapshot unchanged

    // Modify snapshot
    snap.insert(5, 99, null);
    assert.equal(snap.groupLen(5), 1);
    assert.equal(fs.groupLen(5), 0); // original unchanged
  });

  it('group returns empty array for uninitialized group', () => {
    const g = fs.group(7);
    assert.equal(g.length, 0);
  });

  it('forEach iterates all facts', () => {
    fs.insert(3, 10, null);
    fs.insert(5, 20, null);
    fs.insert(3, 30, null);
    const collected = [];
    fs.forEach(h => collected.push(h));
    collected.sort((a, b) => a - b);
    assert.deepEqual(collected, [10, 20, 30]);
  });

  it('handles group growth', () => {
    // Insert more than DEFAULT_GROUP_CAP (8) entries
    for (let i = 0; i < 20; i++) {
      fs.insert(3, i + 100, null);
    }
    assert.equal(fs.groupLen(3), 20);
    for (let i = 0; i < 20; i++) {
      assert.ok(fs.has(3, i + 100));
    }
  });
});

describe('State', () => {
  it('stateHash combines linear and persistent', () => {
    const maxTag = Store.TAG_NAMES.length;
    const lin = new FactSet(maxTag);
    const per = new FactSet(maxTag);
    lin.insert(3, 42, null);
    per.insert(5, 99, null);
    const s = new State(lin, per);
    assert.ok(typeof s.stateHash === 'number');
    assert.ok(s.stateHash > 0);
  });

  it('snapshot produces independent copy', () => {
    const s = fromObject({ 42: 2, 99: 1 }, { 100: true });
    const snap = s.snapshot();
    assert.equal(snap.stateHash, s.stateHash);
    assert.equal(snap.linear.total, s.linear.total);
    assert.equal(snap.persistent.total, s.persistent.total);
  });
});

describe('fromObject / toObject roundtrip', () => {
  it('roundtrips simple state', () => {
    const linear = { 42: 2, 99: 1 };
    const persistent = { 100: true, 200: true };
    const state = fromObject(linear, persistent);
    const back = toObject(state);
    assert.deepEqual(back.linear, linear);
    assert.deepEqual(back.persistent, persistent);
  });

  it('roundtrips empty state', () => {
    const state = fromObject({}, {});
    const back = toObject(state);
    assert.deepEqual(back.linear, {});
    assert.deepEqual(back.persistent, {});
  });

  it('skips zero-count entries', () => {
    const state = fromObject({ 42: 0, 99: 1 }, {});
    const back = toObject(state);
    assert.deepEqual(back.linear, { 99: 1 });
  });

  it('works with real Store hashes', () => {
    const h1 = Store.put('pc', [Store.put('binlit', [5n])]);
    const h2 = Store.put('code', [Store.put('binlit', [5n]), Store.put('atom', ['PUSH1'])]);
    const h3 = Store.put('bang', [Store.put('eq', [Store.put('binlit', [1n]), Store.put('binlit', [2n])])]);
    const state = fromObject({ [h1]: 1, [h2]: 3 }, { [h3]: true });
    const back = toObject(state);
    assert.equal(back.linear[h1], 1);
    assert.equal(back.linear[h2], 3);
    assert.equal(back.persistent[h3], true);
  });
});

describe('FactSet multi-arena undo', () => {
  it('nested checkpoints undo correctly', () => {
    const fs = new FactSet(32);
    const arena = new Arena(256);

    fs.insert(3, 10, null);
    const h0 = fs.hash;

    const cp1 = arena.checkpoint();
    fs.insert(3, 20, arena);
    const h1 = fs.hash;

    const cp2 = arena.checkpoint();
    fs.insert(3, 30, arena);
    fs.remove(3, 10, arena);

    // Undo inner
    fs.undo(arena, cp2);
    assert.equal(fs.hash, h1);
    assert.deepEqual([...fs.group(3)], [10, 20]);

    // Undo outer
    fs.undo(arena, cp1);
    assert.equal(fs.hash, h0);
    assert.deepEqual([...fs.group(3)], [10]);
  });
});
