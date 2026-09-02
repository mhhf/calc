/**
 * out/ill.json freshness gate (audit 2026-09-02). The bundle is derived
 * data: nothing failed when calculus/ill/ sources changed without a
 * `npm run build:bundle` — ui-flow tests happily ran against the stale
 * bundle. The builder stamps sources + sourceHash (content hash, so
 * git-checkout mtimes don't matter); this recomputes and compares.
 */

import { test } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import path from 'path';
import crypto from 'crypto';
import { fileURLToPath } from 'url';

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');

test('out/ill.json matches its calculus sources (rebuild with `npm run build:bundle`)', () => {
  const bundle = JSON.parse(fs.readFileSync(path.join(ROOT, 'out/ill.json'), 'utf8'));
  assert.ok(bundle.sourceHash, 'bundle carries no sourceHash — regenerate with npm run build:bundle');
  assert.ok(Array.isArray(bundle.sources) && bundle.sources.length > 0);
  const sh = crypto.createHash('sha256');
  for (const rel of bundle.sources) {
    sh.update(rel).update('\0').update(fs.readFileSync(path.join(ROOT, rel)));
  }
  assert.equal(sh.digest('hex'), bundle.sourceHash,
    'out/ill.json is STALE relative to calculus sources — run `npm run build:bundle`');
});
