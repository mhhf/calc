/**
 * Tests for Store binary serialization/deserialization
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');
const os = require('os');
const Store = require('../../lib/kernel/store');
const { serialize, deserialize, crc32 } = require('../../lib/engine/store-binary');
const mde = require('../../lib/engine');

describe('Store Binary Format', () => {
  beforeEach(() => {
    Store.clear();
  });

  describe('snapshot/restore round-trip', () => {
    it('round-trips atoms', () => {
      const a = Store.put('atom', ['foo']);
      const b = Store.put('atom', ['bar']);

      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);

      assert.strictEqual(Store.tag(a), 'atom');
      assert.deepStrictEqual(Store.children(a), ['foo']);
      assert.strictEqual(Store.tag(b), 'atom');
      assert.deepStrictEqual(Store.children(b), ['bar']);
    });

    it('round-trips freevars', () => {
      const v = Store.put('freevar', ['_X']);
      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);
      assert.strictEqual(Store.tag(v), 'freevar');
      assert.deepStrictEqual(Store.children(v), ['_X']);
    });

    it('round-trips bigints (binlit)', () => {
      const b = Store.put('binlit', [42n]);
      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);
      assert.strictEqual(Store.tag(b), 'binlit');
      assert.deepStrictEqual(Store.children(b), [42n]);
    });

    it('round-trips compound terms (tensor)', () => {
      const a = Store.put('atom', ['foo']);
      const b = Store.put('atom', ['bar']);
      const t = Store.put('tensor', [a, b]);

      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);

      assert.strictEqual(Store.tag(t), 'tensor');
      const [c0, c1] = Store.children(t);
      assert.strictEqual(Store.tag(c0), 'atom');
      assert.strictEqual(Store.tag(c1), 'atom');
      assert.deepStrictEqual(Store.children(c0), ['foo']);
      assert.deepStrictEqual(Store.children(c1), ['bar']);
    });

    it('round-trips dynamic tags (predicates)', () => {
      const args = [Store.put('freevar', ['_X']), Store.put('freevar', ['_Y'])];
      const p = Store.put('myPredicate', args);

      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);

      assert.strictEqual(Store.tag(p), 'myPredicate');
      assert.strictEqual(Store.tagId(p) >= Store.PRED_BOUNDARY, true);
    });

    it('preserves content-addressing after restore', () => {
      const a = Store.put('atom', ['foo']);
      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);

      // Re-putting the same content should return the same ID
      const a2 = Store.put('atom', ['foo']);
      assert.strictEqual(a2, a);
    });

    it('supports incremental loading after restore', () => {
      const a = Store.put('atom', ['sdk_term']);
      const snap = Store.snapshot();
      Store.clear();
      Store.restore(snap);

      // New puts after restore should get new IDs
      const b = Store.put('atom', ['user_term']);
      assert.notStrictEqual(b, a);
      assert.strictEqual(Store.tag(b), 'atom');
      assert.deepStrictEqual(Store.children(b), ['user_term']);

      // Original term still accessible
      assert.strictEqual(Store.tag(a), 'atom');
      assert.deepStrictEqual(Store.children(a), ['sdk_term']);
    });
  });

  describe('binary serialize/deserialize', () => {
    it('round-trips through binary', () => {
      const a = Store.put('atom', ['hello']);
      const b = Store.put('binlit', [255n]);
      const t = Store.put('tensor', [a, b]);

      const snap = Store.snapshot({ version: '1.0' });
      const buf = serialize(snap);
      const restored = deserialize(buf);

      Store.clear();
      Store.restore(restored);

      assert.strictEqual(Store.tag(a), 'atom');
      assert.deepStrictEqual(Store.children(a), ['hello']);
      assert.strictEqual(Store.tag(b), 'binlit');
      assert.deepStrictEqual(Store.children(b), [255n]);
      assert.strictEqual(Store.tag(t), 'tensor');
      assert.deepStrictEqual(Store.children(t), [a, b]);
    });

    it('preserves metadata', () => {
      Store.put('atom', ['x']);
      const snap = Store.snapshot({ foo: 'bar', count: 42 });
      const buf = serialize(snap);
      const restored = deserialize(buf);
      assert.deepStrictEqual(restored.metadata, { foo: 'bar', count: 42 });
    });

    it('preserves negative bigints', () => {
      // Not currently used but test for completeness
      const b = Store.put('binlit', [-1n]);
      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);
      Store.clear();
      Store.restore(restored);
      assert.deepStrictEqual(Store.children(b), [-1n]);
    });

    it('preserves zero bigint', () => {
      const b = Store.put('binlit', [0n]);
      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);
      Store.clear();
      Store.restore(restored);
      assert.deepStrictEqual(Store.children(b), [0n]);
    });

    it('preserves large bigints', () => {
      const big = 2n ** 256n - 1n;
      const b = Store.put('binlit', [big]);
      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);
      Store.clear();
      Store.restore(restored);
      assert.deepStrictEqual(Store.children(b), [big]);
    });
  });

  describe('CRC32 corruption detection', () => {
    it('detects corrupted data', () => {
      Store.put('atom', ['test']);
      const snap = Store.snapshot();
      const buf = serialize(snap);

      // Corrupt a byte in the middle
      buf[30] ^= 0xFF;

      assert.throws(() => deserialize(buf), /CRC32 mismatch/);
    });

    it('detects corrupted footer', () => {
      Store.put('atom', ['test']);
      const snap = Store.snapshot();
      const buf = serialize(snap);

      // Corrupt the CRC itself
      buf[buf.length - 1] ^= 0x01;

      assert.throws(() => deserialize(buf), /CRC32 mismatch/);
    });
  });

  describe('header validation', () => {
    it('rejects invalid magic', () => {
      const buf = Buffer.alloc(24);
      buf.writeUInt32LE(0xDEADBEEF, 0);
      assert.throws(() => deserialize(buf), /Invalid magic/);
    });

    it('rejects unsupported version', () => {
      const buf = Buffer.alloc(24);
      buf.writeUInt32LE(0x43414C43, 0);
      buf.writeUInt16LE(99, 4); // version 99
      assert.throws(() => deserialize(buf), /Unsupported version/);
    });
  });

  describe('tag registry reset', () => {
    it('restore replaces dynamic tags from snapshot', () => {
      // Create snapshot with predC
      Store.put('predC', [Store.put('atom', ['z'])]);
      const snap = Store.snapshot();

      // Now register a different dynamic tag
      Store.put('predD', [Store.put('atom', ['w'])]);
      assert.strictEqual(Store.TAG['predD'] !== undefined, true);

      // Restore should remove predD (not in snapshot)
      Store.restore(snap);
      assert.strictEqual(Store.TAG['predC'] !== undefined, true);
      assert.strictEqual(Store.TAG['predD'], undefined);
    });
  });

  describe('alignment', () => {
    it('handles odd node counts (alignment padding)', () => {
      // 3 nodes → 6 bytes of tags+arities → needs 2 bytes padding to align
      Store.put('atom', ['a']);
      Store.put('atom', ['b']);
      Store.put('atom', ['c']);

      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);
      Store.clear();
      Store.restore(restored);

      assert.strictEqual(Store.size(), 3);
      assert.strictEqual(Store.tag(1), 'atom');
      assert.strictEqual(Store.tag(2), 'atom');
      assert.strictEqual(Store.tag(3), 'atom');
    });

    it('handles even node counts (no padding needed)', () => {
      Store.put('atom', ['a']);
      Store.put('atom', ['b']);

      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);
      Store.clear();
      Store.restore(restored);

      assert.strictEqual(Store.size(), 2);
    });
  });

  describe('CRC32 function', () => {
    it('produces consistent results', () => {
      const buf = Buffer.from('hello world');
      const c1 = crc32(buf);
      const c2 = crc32(buf);
      assert.strictEqual(c1, c2);
    });

    it('differs for different inputs', () => {
      const c1 = crc32(Buffer.from('hello'));
      const c2 = crc32(Buffer.from('world'));
      assert.notStrictEqual(c1, c2);
    });
  });

  describe('precompile/loadPrecompiled end-to-end', () => {
    it('precompiles bin.ill and loads it back', async () => {
      const tmpFile = path.join(os.tmpdir(), `store-binary-test-${Date.now()}.bin`);
      try {
        Store.clear();
        const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');
        await mde.precompile(binPath, tmpFile);

        // Record what the tree-sitter parse produced
        const origSize = Store.size();
        assert.ok(origSize > 0);

        // Load from binary
        Store.clear();
        const calc = mde.loadPrecompiled(tmpFile);

        assert.strictEqual(calc.types.size > 0, true);
        assert.strictEqual(calc.clauses.size > 0, true);

        // Verify a known type exists
        assert.ok(calc.types.has('nat'));
        const natHash = calc.types.get('nat');
        assert.ok(Store.isTerm(natHash));
      } finally {
        try { fs.unlinkSync(tmpFile); } catch {}
      }
    });

    it('load() auto-writes and re-uses cache', async () => {
      const tmpFile = path.join(os.tmpdir(), `store-cache-test-${Date.now()}.bin`);
      try {
        Store.clear();
        const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

        // First load: no cache exists, should parse and write cache
        const calc1 = await mde.load(binPath, { cache: tmpFile });
        assert.ok(fs.existsSync(tmpFile), 'Cache file should be written');
        const typeCount = calc1.types.size;

        // Second load: cache exists, should load from it
        Store.clear();
        const calc2 = await mde.load(binPath, { cache: tmpFile });
        assert.strictEqual(calc2.types.size, typeCount);
      } finally {
        try { fs.unlinkSync(tmpFile); } catch {}
      }
    });

    it('precompiled calc produces same results as tree-sitter load', async () => {
      const tmpFile = path.join(os.tmpdir(), `store-binary-test2-${Date.now()}.bin`);
      try {
        const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

        // Load via tree-sitter
        Store.clear();
        const calcTS = await mde.load(binPath);
        const tsTypes = new Map(calcTS.types);

        // Precompile and reload
        Store.clear();
        await mde.precompile(binPath, tmpFile);
        Store.clear();
        const calcBin = mde.loadPrecompiled(tmpFile);

        // Same type count
        assert.strictEqual(calcBin.types.size, tsTypes.size);
        // Same clause count
        assert.strictEqual(calcBin.clauses.size, calcTS.clauses.size);
      } finally {
        try { fs.unlinkSync(tmpFile); } catch {}
      }
    });
  });
});
