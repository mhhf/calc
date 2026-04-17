/**
 * Engine version: content-hash of lib/**\/*.js (excluding tests).
 *
 * Included in compose-cache keys so that any change to the engine's JavaScript
 * code automatically invalidates prior snapshots. No developer discipline
 * required — no silent-miss-on-forgotten-bump failure mode.
 *
 * Memoized per Node process: first call pays ~5-15ms, subsequent calls 0ms.
 *
 * Hazard H9 of TODO_0218.
 */

'use strict';

const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const LIB_ROOT = path.resolve(__dirname, '..');

/** Filter: exclude tests + .d.ts files. */
function _includeFile(name) {
  if (name.endsWith('.test.js')) return false;
  if (name.endsWith('.d.ts')) return false;
  return name.endsWith('.js') || name.endsWith('.mjs') || name.endsWith('.cjs');
}

/** Stable-order DFS over lib/, collecting (relativePath, absPath) pairs. */
function _walkLib(dir, base, out) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  entries.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  for (const ent of entries) {
    const full = path.join(dir, ent.name);
    const rel = base ? `${base}/${ent.name}` : ent.name;
    if (ent.isDirectory()) {
      _walkLib(full, rel, out);
    } else if (ent.isFile() && _includeFile(ent.name)) {
      out.push({ rel, full });
    }
  }
}

let _cached = null;

/**
 * Compute the engine version hash. Memoized after first call.
 * Returns a 16-char hex prefix of sha256(files) — collision-free for cache use.
 */
function engineVersion() {
  if (_cached) return _cached;
  const files = [];
  _walkLib(LIB_ROOT, '', files);
  const h = crypto.createHash('sha256');
  for (const { rel, full } of files) {
    // Length-prefix the relative path so added/removed files are detected
    // unambiguously (distinguishes "ab/c.js" from "a/b/c.js" etc).
    const relBuf = Buffer.from(rel, 'utf8');
    const lenBuf = Buffer.alloc(4);
    lenBuf.writeUInt32LE(relBuf.length, 0);
    h.update(lenBuf);
    h.update(relBuf);
    h.update(fs.readFileSync(full));
  }
  _cached = h.digest('hex').slice(0, 16);
  return _cached;
}

/** Test-only: clear memo (for re-running tests that touch lib/). */
function _resetEngineVersionCache() { _cached = null; }

module.exports = { engineVersion, _resetEngineVersionCache };
