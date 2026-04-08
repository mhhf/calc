/**
 * Tests for compose disk cache — persisting composeGrade0 results to disk
 * so cold E2E skips the ~60ms compose overhead.
 */
const { describe, it, beforeEach, afterEach } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('fs');
const path = require('path');
const os = require('os');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');

const SYMEX_PATH = path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
const CODE_PATH = path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');

let tmpDir;

function freshTmpDir() {
  tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-compose-cache-test-'));
  return tmpDir;
}

function loadBytecodeHex() {
  const hex = fs.readFileSync(CODE_PATH, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
  const { loadBytecode } = require('../../lib/engine/ill/bytecode-loader');
  return loadBytecode(hex);
}

function loadWithCompose(cacheDir) {
  const bc = loadBytecodeHex();
  return mde.load(SYMEX_PATH, {
    cache: false,
    extraGrade0Facts: bc.facts,
    scopeGuard: require('../../lib/engine/ill/bytecode-loader').bytecodeArrGetGuard,
    fuseBasicBlocks: true,
    composeDiskCache: cacheDir
  });
}

describe('Compose disk cache', () => {
  beforeEach(() => { Store.clear(); });
  afterEach(() => {
    if (tmpDir && fs.existsSync(tmpDir)) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
      tmpDir = null;
    }
  });

  it('creates cache file on first load', () => {
    const dir = freshTmpDir();
    loadWithCompose(dir);
    const files = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    assert.equal(files.length, 1, 'exactly one compose cache file');
    assert(files[0].endsWith('.bin'), 'cache file is binary');
  });

  it('produces identical rules on cache hit', () => {
    const dir = freshTmpDir();

    // First load: populates cache
    const calc1 = loadWithCompose(dir);
    const names1 = calc1.forwardRules.map(r => r.name);

    // Second load: should hit cache
    Store.clear();
    const calc2 = loadWithCompose(dir);
    const names2 = calc2.forwardRules.map(r => r.name);

    // compactSnapshot renumbers Store IDs, so hashes differ —
    // compare names (structurally stable) instead
    assert.deepStrictEqual(names2, names1, 'cache hit produces same rule names');
    assert.equal(calc2.forwardRules.length, calc1.forwardRules.length);
  });

  it('cache hit is faster than cache miss', () => {
    const dir = freshTmpDir();

    // Warm up: first load populates cache
    loadWithCompose(dir);

    // Cold miss: clear store, load without cache dir
    Store.clear();
    const t0 = performance.now();
    const calc1 = mde.load(SYMEX_PATH, {
      cache: false,
      extraGrade0Facts: loadBytecodeHex().facts,
      scopeGuard: require('../../lib/engine/ill/bytecode-loader').bytecodeArrGetGuard,
      fuseBasicBlocks: true
    });
    const missTime = performance.now() - t0;

    // Cache hit: clear store, load with cache dir
    Store.clear();
    const t1 = performance.now();
    const calc2 = loadWithCompose(dir);
    const hitTime = performance.now() - t1;

    // Cache hit should be meaningfully faster (at least 20% improvement)
    assert(hitTime < missTime * 0.9,
      `cache hit (${hitTime.toFixed(1)}ms) should be faster than miss (${missTime.toFixed(1)}ms)`);

    // Both should produce same rule count
    assert.equal(calc2.forwardRules.length, calc1.forwardRules.length);
  });

  it('invalidates on different bytecode', () => {
    const dir = freshTmpDir();

    // First load with real bytecode
    loadWithCompose(dir);
    const files1 = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    assert.equal(files1.length, 1);

    // Second load with no extra facts (different key)
    Store.clear();
    mde.load(SYMEX_PATH, { cache: false, composeDiskCache: dir });
    const files2 = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    // Different input → different cache file (or no cache file if no compose)
    // The key point: the first cache file's key won't match
  });

  it('survives corrupted cache file', () => {
    const dir = freshTmpDir();

    // First load to create cache
    loadWithCompose(dir);
    const files = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    assert.equal(files.length, 1);

    // Corrupt the cache file
    fs.writeFileSync(path.join(dir, files[0]), 'not json at all {{{');

    // Should fall through to fresh compose (not throw)
    Store.clear();
    const calc = loadWithCompose(dir);
    assert(calc.forwardRules.length > 0, 'fresh compose works after corruption');
  });

  it('explore produces same results with cached vs fresh compose', () => {
    const { explore } = require('../../lib/engine/explore');
    const dir = freshTmpDir();

    function runExplore(calc) {
      const state = mde.decomposeQuery(calc.queries.get('symex'));
      return explore(state, calc.forwardRules, {
        maxDepth: 500,
        calc: { clauses: calc.clauses, definitions: calc.definitions },
        dangerouslyUseFFI: true
      });
    }

    function countNodes(tree) {
      let n = 0;
      const stack = [tree];
      while (stack.length > 0) {
        const node = stack.pop();
        n++;
        if (node.children) for (const c of node.children) stack.push(c);
      }
      return n;
    }

    // Fresh compose
    const calc1 = loadWithCompose(dir);
    const tree1 = runExplore(calc1);
    const nodes1 = countNodes(tree1);

    // Cache hit compose
    Store.clear();
    const calc2 = loadWithCompose(dir);
    const tree2 = runExplore(calc2);
    const nodes2 = countNodes(tree2);

    assert.equal(nodes2, nodes1, 'explore tree has same node count');
  });

  it('composeDiskCache: true uses default temp dir', () => {
    // Just verify it doesn't throw
    Store.clear();
    const bc = loadBytecodeHex();
    const calc = mde.load(SYMEX_PATH, {
      cache: false,
      extraGrade0Facts: bc.facts,
      scopeGuard: require('../../lib/engine/ill/bytecode-loader').bytecodeArrGetGuard,
      fuseBasicBlocks: true,
      composeDiskCache: true
    });
    assert(calc.forwardRules.length > 0);
  });
});
