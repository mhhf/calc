/**
 * Phase 4 of TODO_0218 — full-prefix hit path via `cache: 'compose'` sugar.
 *
 * Covers:
 *   - `cache: 'compose'` routes to the compose disk cache (Phase 4 sugar)
 *   - `CALC_COMPOSE_CACHE=1` env enables compose cache when cache != false
 *   - `CALC_CACHE_DIR` env overrides the cache directory
 *   - atomic write: no `.tmp.*` leftover after successful save
 *   - cache miss + cache hit produce byte-equivalent output (rule names)
 *   - `CALC_CACHE_VERIFY=1` runs both paths, diffs, and succeeds
 */

'use strict';

import { describe, it, beforeEach, afterEach } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';
import os from 'os';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
const SYMEX_PATH = path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

let tmpDir;

function freshTmpDir() {
  tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-phase4-'));
  return tmpDir;
}

describe('TODO_0218 Phase 4 — compose cache full-prefix hit path', () => {
  beforeEach(() => Store.clear());
  afterEach(() => {
    if (tmpDir && fs.existsSync(tmpDir)) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
      tmpDir = null;
    }
  });

  it('cache: "compose" routes to the compose disk cache', () => {
    const dir = freshTmpDir();
    const calc1 = mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    assert.ok(calc1.forwardRules.length > 0);
    const files = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
    assert.equal(files.length, 1, 'one compose-<key>.bin written');

    Store.clear();
    const calc2 = mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    assert.deepStrictEqual(
      calc2.forwardRules.map(r => r.name),
      calc1.forwardRules.map(r => r.name),
      'hit path reproduces rule names'
    );
  });

  it('CALC_COMPOSE_CACHE=1 env enables compose cache', () => {
    const dir = freshTmpDir();
    const prev = process.env.CALC_COMPOSE_CACHE;
    try {
      process.env.CALC_COMPOSE_CACHE = '1';
      mde.load(SYMEX_PATH, { cacheDir: dir });
      const files = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
      assert.equal(files.length, 1, 'compose cache written via env');
    } finally {
      if (prev === undefined) delete process.env.CALC_COMPOSE_CACHE;
      else process.env.CALC_COMPOSE_CACHE = prev;
    }
  });

  it('CALC_CACHE_DIR env overrides the cache directory', () => {
    const dir = freshTmpDir();
    const prev = process.env.CALC_CACHE_DIR;
    try {
      process.env.CALC_CACHE_DIR = dir;
      mde.load(SYMEX_PATH, { cache: 'compose' });
      const files = fs.readdirSync(dir).filter(f => f.startsWith('compose-'));
      assert.equal(files.length, 1, 'env-overridden dir is used');
    } finally {
      if (prev === undefined) delete process.env.CALC_CACHE_DIR;
      else process.env.CALC_CACHE_DIR = prev;
    }
  });

  it('atomic write: no .tmp.* leftover after save', () => {
    const dir = freshTmpDir();
    mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
    const stragglers = fs.readdirSync(dir).filter(f => f.includes('.tmp.'));
    assert.equal(stragglers.length, 0, 'no tmpfile residue');
  });

  it('cache: "verify" runs both paths and diffs them', () => {
    const dir = freshTmpDir();
    // First call writes cache AND replays; must not throw.
    const calc = mde.load(SYMEX_PATH, { cache: 'verify', cacheDir: dir });
    assert.ok(calc.forwardRules.length > 0);
  });

  it('CALC_CACHE_VERIFY=1 activates verify mode', () => {
    const dir = freshTmpDir();
    const prev = process.env.CALC_CACHE_VERIFY;
    try {
      process.env.CALC_CACHE_VERIFY = '1';
      const calc = mde.load(SYMEX_PATH, { cache: 'compose', cacheDir: dir });
      assert.ok(calc.forwardRules.length > 0);
    } finally {
      if (prev === undefined) delete process.env.CALC_CACHE_VERIFY;
      else process.env.CALC_CACHE_VERIFY = prev;
    }
  });
});
