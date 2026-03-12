/**
 * Tests for Store binary serialization/deserialization and auto-caching
 */
const { describe, it, beforeEach, afterEach } = require('node:test');
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
    it('precompiles bin.ill and loads it back', () => {
      const tmpFile = path.join(os.tmpdir(), `store-binary-test-${Date.now()}.bin`);
      try {
        Store.clear();
        const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');
        mde.precompile(binPath, tmpFile);

        // Record what the parse produced
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

    it('precompiled calc produces same results as source load', () => {
      const tmpFile = path.join(os.tmpdir(), `store-binary-test2-${Date.now()}.bin`);
      try {
        const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

        // Load from source (no caching)
        Store.clear();
        const calcTS = mde.load(binPath, { cache: false });
        const tsTypes = new Map(calcTS.types);

        // Precompile and reload
        Store.clear();
        mde.precompile(binPath, tmpFile);
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

    it('precompiled explore produces same tree as source load', () => {
      const { explore } = require('../../lib/engine/explore');
      const treeUtils = require('../../lib/engine/tree-utils');
      const tmpFile = path.join(os.tmpdir(), `store-binary-explore-${Date.now()}.bin`);
      try {
        const msPath = path.join(__dirname, '../../calculus/ill/programs/multisig.ill');

        // Source load + explore (no caching)
        Store.clear();
        const calcSrc = mde.load(msPath, { cache: false });
        const stateSrc = mde.decomposeQuery(calcSrc.queries.get('symex'));
        const treeSrc = explore(stateSrc, calcSrc.forwardRules, {
          maxDepth: 200,
          calc: { clauses: calcSrc.clauses, types: calcSrc.types },
          dangerouslyUseFFI: true
        });

        // Precompile + load + explore
        Store.clear();
        mde.precompile(msPath, tmpFile);
        Store.clear();
        const calcBin = mde.loadPrecompiled(tmpFile);
        const stateBin = mde.decomposeQuery(calcBin.queries.get('symex'));
        const treeBin = explore(stateBin, calcBin.forwardRules, {
          maxDepth: 200,
          calc: { clauses: calcBin.clauses, types: calcBin.types },
          dangerouslyUseFFI: true
        });

        // Same tree structure
        assert.strictEqual(treeUtils.countNodes(treeBin), treeUtils.countNodes(treeSrc));
        assert.strictEqual(treeUtils.countLeaves(treeBin), treeUtils.countLeaves(treeSrc));
        assert.strictEqual(treeUtils.maxDepth(treeBin), treeUtils.maxDepth(treeSrc));
      } finally {
        try { fs.unlinkSync(tmpFile); } catch {}
      }
    });
  });

  describe('auto-cache', () => {
    let tmpDir;

    beforeEach(() => {
      Store.clear();
      tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-autocache-'));
    });

    afterEach(() => {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    });

    it('writes and reads full cache (load twice)', () => {
      const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

      // First load: miss, writes cache
      const calc1 = mde.load(binPath, { cacheDir: tmpDir });
      const typeCount = calc1.types.size;
      assert.ok(typeCount > 0);
      const cacheFiles = fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'));
      assert.ok(cacheFiles.length > 0, 'Cache file(s) should be written');

      // Second load: full cache hit
      Store.clear();
      const calc2 = mde.load(binPath, { cacheDir: tmpDir });
      assert.strictEqual(calc2.types.size, typeCount);
      assert.ok(calc2.types.has('nat'));
    });

    it('invalidates cache when source changes', () => {
      const tmpFile = path.join(tmpDir, 'test.ill');
      fs.writeFileSync(tmpFile, 'mytype: type.');

      // First load: writes cache
      const calc1 = mde.load(tmpFile, { cacheDir: tmpDir });
      assert.strictEqual(calc1.types.size, 1);
      assert.ok(calc1.types.has('mytype'));

      // Modify source
      fs.writeFileSync(tmpFile, 'mytype: type.\nmytype2: type.');

      // Second load: hash changed → cache miss → new cache
      Store.clear();
      const calc2 = mde.load(tmpFile, { cacheDir: tmpDir });
      assert.strictEqual(calc2.types.size, 2);
      assert.ok(calc2.types.has('mytype2'));
    });

    it('cache:imports restores SDK and parses top file fresh', () => {
      const libFile = path.join(tmpDir, 'lib.ill');
      const mainFile = path.join(tmpDir, 'main.ill');
      fs.writeFileSync(libFile, 'nat: type.\nz: nat.\ns: nat -> nat.');
      fs.writeFileSync(mainFile, '#import(lib.ill)\nmyfact: nat.');

      // First load: miss, writes imports cache
      const calc1 = mde.load(mainFile, { cache: 'imports', cacheDir: tmpDir });
      assert.ok(calc1.types.has('nat'));
      assert.ok(calc1.types.has('myfact'));

      // Modify top file only
      fs.writeFileSync(mainFile, '#import(lib.ill)\nmyfact2: nat.');

      // Second load: imports cache hit, top file parsed fresh
      Store.clear();
      const calc2 = mde.load(mainFile, { cache: 'imports', cacheDir: tmpDir });
      assert.ok(calc2.types.has('nat'), 'SDK types still present');
      assert.ok(calc2.types.has('myfact2'), 'New top-file type present');
      assert.ok(!calc2.types.has('myfact'), 'Old top-file type gone');
    });

    it('cache:false writes no cache files', () => {
      const tmpFile = path.join(tmpDir, 'nocache.ill');
      fs.writeFileSync(tmpFile, 'mytype: type.');

      mde.load(tmpFile, { cache: false });
      const cacheFiles = fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'));
      assert.strictEqual(cacheFiles.length, 0, 'No cache files should be written');
    });

    it('cached load produces same types/clauses as fresh load', () => {
      const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

      // Fresh load
      Store.clear();
      const calcFresh = mde.load(binPath, { cache: false });

      // Cached load (first call = miss + write, same result)
      Store.clear();
      const calcCached = mde.load(binPath, { cacheDir: tmpDir });

      assert.strictEqual(calcCached.types.size, calcFresh.types.size);
      assert.strictEqual(calcCached.clauses.size, calcFresh.clauses.size);
      for (const [name] of calcFresh.types) {
        assert.ok(calcCached.types.has(name), `Missing type: ${name}`);
      }
    });

    it('corrupted cache file falls back to fresh parse', () => {
      const binPath = path.join(__dirname, '../../calculus/ill/programs/bin.ill');

      // First load: writes cache
      const calc1 = mde.load(binPath, { cacheDir: tmpDir });
      const typeCount = calc1.types.size;

      // Corrupt all cache files
      for (const f of fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'))) {
        const p = path.join(tmpDir, f);
        const buf = fs.readFileSync(p);
        buf[30] ^= 0xFF;
        fs.writeFileSync(p, buf);
      }

      // Second load: corrupted → fallback to fresh parse
      Store.clear();
      const calc2 = mde.load(binPath, { cacheDir: tmpDir });
      assert.strictEqual(calc2.types.size, typeCount);
    });

    it('file with no imports uses single-tier cache', () => {
      const tmpFile = path.join(tmpDir, 'simple.ill');
      fs.writeFileSync(tmpFile, 'mytype: type.\nval: mytype.');

      // First load: writes one cache file (full only)
      const calc = mde.load(tmpFile, { cacheDir: tmpDir });
      assert.ok(calc.types.has('mytype'));
      assert.ok(calc.types.has('val'));

      const cacheFiles = fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'));
      assert.strictEqual(cacheFiles.length, 1, 'Only full-tier cache file');

      // Second load: hits full cache
      Store.clear();
      const calc2 = mde.load(tmpFile, { cacheDir: tmpDir });
      assert.ok(calc2.types.has('mytype'));
      assert.ok(calc2.types.has('val'));
    });

    it('cache:imports with real EVM files', () => {
      const msPath = path.join(__dirname, '../../calculus/ill/programs/multisig.ill');

      // First load: miss, writes imports cache
      const calc1 = mde.load(msPath, { cache: 'imports', cacheDir: tmpDir });
      assert.ok(calc1.types.has('nat'), 'has SDK type');
      assert.ok(calc1.queries.has('symex'), 'has symex query');

      // Only imports cache (not full)
      const cacheFiles = fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'));
      assert.strictEqual(cacheFiles.length, 1, 'Only imports cache file');

      // Second load: imports cache hit, top file parsed fresh
      Store.clear();
      const calc2 = mde.load(msPath, { cache: 'imports', cacheDir: tmpDir });
      assert.ok(calc2.types.has('nat'));
      assert.ok(calc2.queries.has('symex'));
      assert.strictEqual(calc2.types.size, calc1.types.size);
    });

    it('auto-cached explore produces same tree as fresh', () => {
      const { explore } = require('../../lib/engine/explore');
      const treeUtils = require('../../lib/engine/tree-utils');
      const msPath = path.join(__dirname, '../../calculus/ill/programs/multisig.ill');

      // Fresh load
      Store.clear();
      const calcFresh = mde.load(msPath, { cache: false });
      const stateFresh = mde.decomposeQuery(calcFresh.queries.get('symex'));
      const treeFresh = explore(stateFresh, calcFresh.forwardRules, {
        maxDepth: 200,
        calc: { clauses: calcFresh.clauses, types: calcFresh.types },
        dangerouslyUseFFI: true
      });

      // Auto-cached load (first call = miss + write)
      Store.clear();
      const calcCached = mde.load(msPath, { cacheDir: tmpDir });
      const stateCached = mde.decomposeQuery(calcCached.queries.get('symex'));
      const treeCached = explore(stateCached, calcCached.forwardRules, {
        maxDepth: 200,
        calc: { clauses: calcCached.clauses, types: calcCached.types },
        dangerouslyUseFFI: true
      });

      assert.strictEqual(treeUtils.countNodes(treeCached), treeUtils.countNodes(treeFresh));
      assert.strictEqual(treeUtils.countLeaves(treeCached), treeUtils.countLeaves(treeFresh));
      assert.strictEqual(treeUtils.maxDepth(treeCached), treeUtils.maxDepth(treeFresh));
    });

    it('two-tier cache: full miss → imports hit → full hit', () => {
      const msPath = path.join(__dirname, '../../calculus/ill/programs/multisig.ill');

      // First load: double miss → writes both imports and full caches
      const calc1 = mde.load(msPath, { cacheDir: tmpDir });
      const cacheFiles1 = fs.readdirSync(tmpDir).filter(f => f.endsWith('.bin'));
      assert.strictEqual(cacheFiles1.length, 2, 'Both imports and full cache written');

      // Second load: full cache hit
      Store.clear();
      const calc2 = mde.load(msPath, { cacheDir: tmpDir });
      assert.strictEqual(calc2.types.size, calc1.types.size);
      assert.strictEqual(calc2.clauses.size, calc1.clauses.size);
    });
  });
});
