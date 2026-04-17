/**
 * Tests for prove-source in backchain mode with `#import(path)` headers.
 *
 * Covers: sandboxing, header parsing, cache-key invalidation across
 * imported content hashes, mode routing (sequent vs backchain), and
 * the opaque-FFI-leaf / clause-expansion toggle.
 */

'use strict';

const { describe, it, before, after } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const os = require('os');
const path = require('path');

const {
  proveSource,
  parseHeader,
  resolveImport,
  SANDBOX_ROOT,
  _resetCache,
} = require('../lib/prover/prove-source');

describe('parseHeader', () => {
  it('extracts leading #import lines', () => {
    const src = '#import(programs/bin.ill)\n\nplus (i e) (i e) R';
    const { imports, body } = parseHeader(src);
    assert.deepStrictEqual(imports, ['programs/bin.ill']);
    assert.strictEqual(body, 'plus (i e) (i e) R');
  });

  it('allows comments and blank lines between imports', () => {
    const src = '% top\n#import(a.ill)\n\n% between\n#import(b.ill)\n\ngoal X';
    const { imports, body } = parseHeader(src);
    assert.deepStrictEqual(imports, ['a.ill', 'b.ill']);
    assert.strictEqual(body, 'goal X');
  });

  it('stops at first non-import/non-blank line', () => {
    const src = '#import(a.ill)\nplus X Y Z\n#import(b.ill)';
    const { imports, body } = parseHeader(src);
    assert.deepStrictEqual(imports, ['a.ill']);
    assert.ok(body.includes('plus X Y Z'));
    assert.ok(body.includes('#import(b.ill)'));
  });
});

describe('resolveImport — sandbox', () => {
  it('resolves a valid relative path under the sandbox root', () => {
    const resolved = resolveImport('programs/bin.ill');
    assert.ok(resolved.startsWith(SANDBOX_ROOT));
    assert.ok(resolved.endsWith('bin.ill'));
  });

  it('rejects absolute paths', () => {
    assert.throws(() => resolveImport('/etc/passwd'), /absolute imports rejected/);
  });

  it('rejects paths escaping the sandbox via ../', () => {
    assert.throws(
      () => resolveImport('../../../etc/passwd'),
      /escapes sandbox/,
    );
  });

  it('rejects non-existent files', () => {
    assert.throws(
      () => resolveImport('programs/does-not-exist.ill'),
      /import not found/,
    );
  });
});

describe('proveSource — backchain mode', () => {
  let cacheDir;
  before(() => {
    _resetCache();
    cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-prove-import-'));
  });
  after(() => { fs.rmSync(cacheDir, { recursive: true, force: true }); });

  it('proves plus (i e) (i e) R with #import(programs/bin.ill)', async () => {
    const source = '#import(programs/bin.ill)\n\nplus (i e) (i e) R';
    const r = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(r.ok, true, `expected ok=true, got error: ${r.error}`);
    assert.ok(r.tree);
    assert.strictEqual(r.tree.profile, 'default');
    assert.ok(r.tree.root);
    // Default mode: FFI intercepts plus → root is the opaque `ffi` leaf.
    assert.strictEqual(r.tree.root.rule, 'ffi');
  });

  it('teaching profile expands clauses', async () => {
    const source = '#import(programs/bin.ill)\n\nplus (i e) (i e) R';
    const r = await proveSource({
      source, mode: 'backchain', profile: 'teaching', cacheDir,
    });
    assert.strictEqual(r.ok, true);
    assert.ok(/^plus\//.test(r.tree.root.rule),
      `expected plus/* at root, got ${r.tree.root.rule}`);
    assert.ok(r.tree.root.premises.length >= 1);
  });

  it('cache hit on second call with same inputs', async () => {
    const source = '#import(programs/bin.ill)\n\nplus (o e) e R';
    const cold = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(cold.cacheHit, false);
    assert.strictEqual(cold.ok, true);
    const warm = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(warm.cacheHit, true);
    assert.strictEqual(warm.ok, true);
  });

  it('rejects escaping imports with a clear error', async () => {
    const source = '#import(../../etc/passwd)\n\nfoo';
    const r = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /escapes sandbox/);
  });

  it('rejects missing imports', async () => {
    const source = '#import(programs/not-a-real-file.ill)\n\nfoo';
    const r = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /import not found/);
  });

  it('backchain mode without any import → error', async () => {
    const source = 'plus (i e) (i e) R';
    const r = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /requires an #import/);
  });

  it('multi-import → explicit error (deferred feature)', async () => {
    const source = '#import(programs/bin.ill)\n#import(programs/evm.ill)\n\nfoo';
    const r = await proveSource({ source, mode: 'backchain', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /multiple #import/);
  });
});

describe('proveSource — sequent mode rejects imports', () => {
  it('sequent + #import → explicit error', async () => {
    const source = '#import(programs/bin.ill)\nA |- A';
    const r = await proveSource({ source });  // default mode = sequent
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /only supported in backchain/);
  });
});
