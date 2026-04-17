/**
 * TODO_0218 Phase 6 — LRU eviction + version-tag format migration.
 *
 * Covers the `cache-evict` module in isolation and its wire-up into
 * `mde.load()` via the compose cache path.
 */

'use strict';

const { describe, it, beforeEach, afterEach } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('fs');
const path = require('path');
const os = require('os');
const {
  ensureVersionTag, lruEvict, DEFAULT_MAX_BYTES, _resetVersionTagMemo,
} = require('../../lib/engine/cache-evict');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');

const SYMEX_PATH = path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

let tmpDir;

function freshTmpDir() {
  tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-evict-0218-'));
  return tmpDir;
}

describe('TODO_0218 Phase 6 — cache-evict module', () => {
  beforeEach(() => _resetVersionTagMemo());
  afterEach(() => {
    if (tmpDir && fs.existsSync(tmpDir)) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
      tmpDir = null;
    }
  });

  describe('ensureVersionTag', () => {
    it('creates dir and writes version.txt on first call', () => {
      const dir = path.join(os.tmpdir(), `calc-evict-fresh-${process.pid}-${Date.now()}`);
      try {
        ensureVersionTag(dir, 'v1');
        assert.equal(fs.readFileSync(path.join(dir, 'version.txt'), 'utf8'), 'v1');
      } finally {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    });

    it('preserves compose-*.bin when version matches', () => {
      const dir = freshTmpDir();
      fs.writeFileSync(path.join(dir, 'version.txt'), 'v1');
      fs.writeFileSync(path.join(dir, 'compose-abc.bin'), 'payload');
      ensureVersionTag(dir, 'v1');
      assert.ok(fs.existsSync(path.join(dir, 'compose-abc.bin')), 'file preserved');
    });

    it('wipes compose-*.bin on version mismatch', () => {
      const dir = freshTmpDir();
      fs.writeFileSync(path.join(dir, 'version.txt'), 'v1');
      fs.writeFileSync(path.join(dir, 'compose-abc.bin'), 'payload');
      fs.writeFileSync(path.join(dir, 'compose-def.bin'), 'payload');
      fs.writeFileSync(path.join(dir, 'unrelated.txt'), 'keep me');
      ensureVersionTag(dir, 'v2');
      assert.ok(!fs.existsSync(path.join(dir, 'compose-abc.bin')), 'wiped');
      assert.ok(!fs.existsSync(path.join(dir, 'compose-def.bin')), 'wiped');
      assert.ok(fs.existsSync(path.join(dir, 'unrelated.txt')), 'unrelated untouched');
      assert.equal(fs.readFileSync(path.join(dir, 'version.txt'), 'utf8'), 'v2');
    });

    it('wipes compose-*.bin when tag is missing', () => {
      const dir = freshTmpDir();
      fs.writeFileSync(path.join(dir, 'compose-abc.bin'), 'payload');
      ensureVersionTag(dir, 'v1');
      assert.ok(!fs.existsSync(path.join(dir, 'compose-abc.bin')), 'wiped');
      assert.equal(fs.readFileSync(path.join(dir, 'version.txt'), 'utf8'), 'v1');
    });
  });

  describe('lruEvict', () => {
    it('no-op under budget', () => {
      const dir = freshTmpDir();
      fs.writeFileSync(path.join(dir, 'compose-a.bin'), Buffer.alloc(100));
      fs.writeFileSync(path.join(dir, 'compose-b.bin'), Buffer.alloc(100));
      lruEvict(dir, 1000);
      assert.ok(fs.existsSync(path.join(dir, 'compose-a.bin')));
      assert.ok(fs.existsSync(path.join(dir, 'compose-b.bin')));
    });

    it('deletes oldest-atime files when over budget', () => {
      const dir = freshTmpDir();
      const a = path.join(dir, 'compose-a.bin');
      const b = path.join(dir, 'compose-b.bin');
      const c = path.join(dir, 'compose-c.bin');
      fs.writeFileSync(a, Buffer.alloc(500));
      fs.writeFileSync(b, Buffer.alloc(500));
      fs.writeFileSync(c, Buffer.alloc(500));
      // Force distinct atimes: oldest=a, middle=b, newest=c
      const now = Date.now() / 1000;
      fs.utimesSync(a, now - 300, now - 300);
      fs.utimesSync(b, now - 200, now - 200);
      fs.utimesSync(c, now - 100, now - 100);
      // Budget 800: total 1500, must evict two oldest to get to 500 <= 800.
      // Actually 1500-500(a)=1000 > 800, then 1000-500(b)=500 <= 800. So drops a and b.
      lruEvict(dir, 800);
      assert.ok(!fs.existsSync(a), 'oldest evicted');
      assert.ok(!fs.existsSync(b), 'second-oldest evicted');
      assert.ok(fs.existsSync(c), 'newest preserved');
    });

    it('ignores non-compose files', () => {
      const dir = freshTmpDir();
      fs.writeFileSync(path.join(dir, 'compose-a.bin'), Buffer.alloc(100));
      fs.writeFileSync(path.join(dir, 'unrelated.log'), Buffer.alloc(1000));
      lruEvict(dir, 50);
      assert.ok(!fs.existsSync(path.join(dir, 'compose-a.bin')), 'compose file evicted');
      assert.ok(fs.existsSync(path.join(dir, 'unrelated.log')), 'unrelated kept');
    });

    it('survives missing dir', () => {
      // Should not throw
      lruEvict(path.join(os.tmpdir(), 'calc-does-not-exist-' + Date.now()), 100);
    });
  });

  describe('DEFAULT_MAX_BYTES', () => {
    it('is 256 MB', () => {
      assert.equal(DEFAULT_MAX_BYTES, 256 * 1024 * 1024);
    });
  });
});

describe('TODO_0218 Phase 6 — wire-up into mde.load', () => {
  beforeEach(() => { Store.clear(); _resetVersionTagMemo(); });
  afterEach(() => {
    if (tmpDir && fs.existsSync(tmpDir)) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
      tmpDir = null;
    }
  });

  it('writes version.txt on first compose cache use', () => {
    const dir = freshTmpDir();
    mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    assert.ok(fs.existsSync(path.join(dir, 'version.txt')), 'version.txt written');
  });

  it('stale version.txt wipes compose-*.bin before next load', () => {
    const dir = freshTmpDir();
    // Populate cache.
    mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    const before = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    assert.equal(before.length, 1, 'one cache file after first load');

    // Tamper with version.txt to simulate engine-version mismatch.
    fs.writeFileSync(path.join(dir, 'version.txt'), 'stale-version');
    // Reset the in-process (dir, version) memo so the next call re-reads the
    // tag — mimics a separate process starting up against a stale cache dir.
    _resetVersionTagMemo();

    Store.clear();
    mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    const after = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    // The stale entry was wiped; new one written.
    assert.equal(after.length, 1, 'exactly one cache file after migration');
    // And version.txt was refreshed.
    const tag = fs.readFileSync(path.join(dir, 'version.txt'), 'utf8');
    assert.notEqual(tag, 'stale-version', 'version.txt refreshed');
  });

  it('honors opts.cacheMaxBytes for LRU budget', () => {
    const dir = freshTmpDir();
    // Plant two large decoy compose files so the budget triggers eviction.
    // We use a tiny cap so that even our own just-written cache file plus
    // the decoys exceed the budget, forcing the decoys (with older atimes)
    // to be evicted.
    fs.writeFileSync(path.join(dir, 'compose-decoy-old.bin'), Buffer.alloc(1024 * 1024));
    const oldTime = (Date.now() / 1000) - 3600;
    fs.utimesSync(path.join(dir, 'compose-decoy-old.bin'), oldTime, oldTime);

    mde.load(SYMEX_PATH, {
      cache: 'compose',
      cacheDir: dir,
      cacheMaxBytes: 1024, // tiny budget — forces eviction
    });
    // Decoy (oldest atime) should be gone.
    assert.ok(!fs.existsSync(path.join(dir, 'compose-decoy-old.bin')),
      'old decoy evicted under tight budget');
  });
});
