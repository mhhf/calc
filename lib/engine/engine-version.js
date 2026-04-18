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

import fs from 'fs';
import path from 'path';
import crypto from 'crypto';
const LIB_ROOT = path.resolve(import.meta.dirname, '..');

// Bun.hash.wyhash: 64-bit non-cryptographic hash. ~6× faster than sha256 on
// the raw hash op; in engineVersion() it saves ~0.4ms per cold-start call.
// Non-crypto is fine — use is fingerprinting, not signing. Feature-detected.
const _HAS_BUN_WYHASH = typeof globalThis.Bun !== 'undefined'
  && typeof globalThis.Bun?.hash?.wyhash === 'function';

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
 * Returns a 16-char hex digest: wyhash(files) on bun, sha256(files).slice(0,16) on node.
 * Truncated 64-bit is collision-free for cache-key use.
 */
function engineVersion() {
  if (_cached) return _cached;
  const files = [];
  _walkLib(LIB_ROOT, '', files);
  _cached = _HAS_BUN_WYHASH ? _hashWyhash(files) : _hashSha256(files);
  return _cached;
}

/** Bun path: pre-allocate + one wyhash call. 64-bit → 16 hex chars.
 *  Pre-alloc beats Buffer.concat by ~4× on 300+ small buffers (measured).
 *  Length-prefix on rel path disambiguates added/removed/renamed files
 *  (distinguishes "ab/c.js" from "a/b/c.js"). */
function _hashWyhash(files) {
  const entries = new Array(files.length);
  let total = 0;
  for (let i = 0; i < files.length; i++) {
    const relBuf = Buffer.from(files[i].rel, 'utf8');
    const data = fs.readFileSync(files[i].full);
    entries[i] = { relBuf, data };
    total += 4 + relBuf.length + data.length;
  }
  const big = Buffer.allocUnsafe(total);
  let off = 0;
  for (let i = 0; i < entries.length; i++) {
    big.writeUInt32LE(entries[i].relBuf.length, off); off += 4;
    off += entries[i].relBuf.copy(big, off);
    off += entries[i].data.copy(big, off);
  }
  return globalThis.Bun.hash.wyhash(big).toString(16).padStart(16, '0');
}

/** Node path: streaming sha256, 16-char hex prefix.
 *  Length-prefix on rel path disambiguates added/removed/renamed files. */
function _hashSha256(files) {
  const h = crypto.createHash('sha256');
  for (const { rel, full } of files) {
    const relBuf = Buffer.from(rel, 'utf8');
    const lenBuf = Buffer.alloc(4);
    lenBuf.writeUInt32LE(relBuf.length, 0);
    h.update(lenBuf);
    h.update(relBuf);
    h.update(fs.readFileSync(full));
  }
  return h.digest('hex').slice(0, 16);
}

/** Test-only: clear memo (for re-running tests that touch lib/). */
function _resetEngineVersionCache() { _cached = null; }

export { engineVersion, _resetEngineVersionCache };
export default { engineVersion, _resetEngineVersionCache };
