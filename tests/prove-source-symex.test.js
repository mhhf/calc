/**
 * Integration tests for prove-source in `symex` mode.
 *
 * Covers: #import wiring, mode dispatch, forward-trace/v1 payload shape,
 * queryName selection, lazy leaf-trace extraction, and error paths.
 */

'use strict';

const { describe, it, before, after } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const os = require('os');
const path = require('path');

const {
  proveSource,
  extractSymexLeafTrace,
  _resetCache,
} = require('../lib/prover/prove-source');

describe('proveSource — symex mode (tiny)', () => {
  let cacheDir;
  before(() => {
    _resetCache();
    cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-prove-symex-'));
  });
  after(() => { fs.rmSync(cacheDir, { recursive: true, force: true }); });

  it('explores programs/pure_linear.ill → forward-trace/v1 payload', async () => {
    const source = '#import(programs/pure_linear.ill)';
    const r = await proveSource({ source, mode: 'symex', cacheDir });
    assert.strictEqual(r.ok, true, `expected ok=true, got error: ${r.error}`);
    assert.ok(r.tree);
    assert.strictEqual(r.tree.format, 'forward-trace/v1');
    assert.strictEqual(r.tree.mode, 'symex');
    assert.ok(r.tree.stats.leafCount >= 1,
      `expected ≥1 leaf, got ${r.tree.stats.leafCount}`);
    // Leaves carry stepCount but NOT the trace itself.
    for (const leaf of r.tree.leaves) {
      assert.strictEqual(leaf.trace, undefined);
      assert.ok(typeof leaf.stepCount === 'number');
    }
  });

  it('cache hit on second identical call', async () => {
    const freshCache = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-prove-symex-hit-'));
    try {
      const source = '#import(programs/pure_linear.ill)';
      const cold = await proveSource({ source, mode: 'symex', cacheDir: freshCache });
      assert.strictEqual(cold.cacheHit, false);
      const warm = await proveSource({ source, mode: 'symex', cacheDir: freshCache });
      assert.strictEqual(warm.cacheHit, true);
      assert.strictEqual(warm.tree.format, 'forward-trace/v1');
    } finally {
      fs.rmSync(freshCache, { recursive: true, force: true });
    }
  });

  it('rejects symex without #import', async () => {
    const source = '';
    const r = await proveSource({ source, mode: 'symex', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /requires an #import/);
  });

  it('rejects unknown query name', async () => {
    const source = '#import(programs/pure_linear.ill)\n\nnosuchquery';
    const r = await proveSource({ source, mode: 'symex', cacheDir });
    assert.strictEqual(r.ok, false);
    assert.match(r.error, /not declared/);
  });

  it('extractSymexLeafTrace returns per-leaf trace from in-memory cache', async () => {
    const source = '#import(programs/pure_linear.ill)';
    const fresh = await proveSource({ source, mode: 'symex', cacheDir });
    assert.strictEqual(fresh.ok, true);
    const leaf0 = extractSymexLeafTrace(fresh.key, 0);
    assert.strictEqual(leaf0.ok, true);
    assert.ok(leaf0.leaf);
    assert.ok(Array.isArray(leaf0.leaf.trace));
    // At least one step expected — the file fires step1 then step2.
    assert.ok(leaf0.leaf.trace.length >= 1);
    assert.ok(leaf0.leaf.formulas);
  });

  it('extractSymexLeafTrace out-of-range → error', async () => {
    const source = '#import(programs/pure_linear.ill)';
    const fresh = await proveSource({ source, mode: 'symex', cacheDir });
    const miss = extractSymexLeafTrace(fresh.key, 999);
    assert.strictEqual(miss.ok, false);
    assert.match(miss.error, /out of range/);
  });
});
