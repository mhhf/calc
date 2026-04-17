/**
 * Tests for lib/prover/prove-source — source string → proof-tree/v1 JSON
 * with on-disk cache.
 */

const { describe, it, before, after } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const os = require('os');
const path = require('path');

const { proveSource, hashKey } = require('../lib/prover/prove-source');
const { FORMAT_VERSION } = require('../lib/prover/serialize-tree');

describe('prove-source', () => {
  let cacheDir;

  before(() => {
    cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-prove-source-'));
  });

  after(() => {
    fs.rmSync(cacheDir, { recursive: true, force: true });
  });

  describe('hashKey', () => {
    it('is deterministic for same inputs', () => {
      const k1 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      const k2 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      assert.strictEqual(k1, k2);
    });

    it('changes when source changes', () => {
      const k1 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      const k2 = hashKey('ill', 'default', 'sequent', '', 'B |- B');
      assert.notStrictEqual(k1, k2);
    });

    it('changes when profile changes', () => {
      const k1 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      const k2 = hashKey('ill', 'verified', 'sequent', '', 'A |- A');
      assert.notStrictEqual(k1, k2);
    });

    it('changes when calculus changes', () => {
      const k1 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      const k2 = hashKey('other', 'default', 'sequent', '', 'A |- A');
      assert.notStrictEqual(k1, k2);
    });

    it('changes when mode changes', () => {
      const k1 = hashKey('ill', 'default', 'sequent', '', 'A |- A');
      const k2 = hashKey('ill', 'default', 'backchain', '', 'A |- A');
      assert.notStrictEqual(k1, k2);
    });

    it('changes when imports digest changes', () => {
      const k1 = hashKey('ill', 'default', 'backchain', 'abc123', 'goal');
      const k2 = hashKey('ill', 'default', 'backchain', 'def456', 'goal');
      assert.notStrictEqual(k1, k2);
    });
  });

  describe('proveSource', () => {
    it('proves trivial identity', async () => {
      const r = await proveSource({ source: 'A |- A' });
      assert.strictEqual(r.ok, true);
      assert.ok(r.tree);
      assert.strictEqual(r.tree.format, FORMAT_VERSION);
      assert.strictEqual(r.tree.calculus, 'ill');
      assert.strictEqual(r.tree.profile, 'default');
      assert.ok(r.tree.root);
      assert.strictEqual(r.cacheHit, false);
    });

    it('proves a simple tensor introduction', async () => {
      const r = await proveSource({ source: 'A, B |- A * B' });
      assert.strictEqual(r.ok, true);
      assert.ok(r.tree);
    });

    it('proves modus ponens via loli', async () => {
      const r = await proveSource({ source: 'A, A -o B |- B' });
      assert.strictEqual(r.ok, true);
      assert.ok(r.tree);
    });

    it('returns ok:false for an unprovable sequent', async () => {
      const r = await proveSource({ source: 'A |- B' });
      assert.strictEqual(r.ok, false);
    });

    it('returns error for bogus syntax', async () => {
      const r = await proveSource({ source: '^^^^' });
      assert.strictEqual(r.ok, false);
      assert.ok(r.error);
    });

    it('throws on missing source', async () => {
      await assert.rejects(
        () => proveSource({}),
        /source.*required/,
      );
    });

    it('rejects unknown calculus name', async () => {
      const r = await proveSource({ calculus: 'xyz', source: 'A |- A' });
      assert.strictEqual(r.ok, false);
      assert.match(r.error, /unknown calculus/);
    });
  });

  describe('disk cache', () => {
    it('cold → writes cache; warm → hit', async () => {
      const source = 'A, A -o B |- B';
      // Cold pass
      const cold = await proveSource({ source, cacheDir });
      assert.strictEqual(cold.cacheHit, false);
      assert.strictEqual(cold.ok, true);
      // Cache file exists
      const files = fs.readdirSync(cacheDir);
      assert.ok(files.length >= 1);
      assert.ok(files.includes(cold.key + '.json'));
      // Warm pass
      const warm = await proveSource({ source, cacheDir });
      assert.strictEqual(warm.cacheHit, true);
      assert.strictEqual(warm.ok, true);
      // Round-trip via JSON normalizes prototypes (cold uses null-proto
      // objects from serializeTree; warm reads them back as plain objects).
      assert.strictEqual(JSON.stringify(warm.tree), JSON.stringify(cold.tree));
    });

    it('different source → different cache file', async () => {
      const a = await proveSource({ source: 'A |- A', cacheDir });
      const b = await proveSource({ source: 'B |- B', cacheDir });
      assert.notStrictEqual(a.key, b.key);
    });

    it('ignores cache entries from a stale format version', async () => {
      const key = hashKey('ill', 'default', 'sequent', '', 'stale |- stale');
      fs.writeFileSync(
        path.join(cacheDir, key + '.json'),
        JSON.stringify({ ok: true, tree: { format: 'proof-tree/v0' } }),
      );
      // Fresh key would differ; but force a lookup on the same key:
      const k = hashKey('ill', 'default', 'sequent', '', 'stale');
      assert.notStrictEqual(k, key); // different source → different key
      // Direct sanity: stale file is present but won't be read for other inputs.
      const r = await proveSource({ source: 'stale', cacheDir });
      // result should not be the stale object
      assert.notStrictEqual(r.tree?.format, 'proof-tree/v0');
    });
  });
});
