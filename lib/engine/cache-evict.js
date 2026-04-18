/**
 * Compose cache eviction + format migration (TODO_0218 Phase 6).
 *
 * Two jobs:
 *   - LRU eviction: when the snapshot directory exceeds a size budget,
 *     delete oldest-accessed files until under budget.
 *   - Format migration: write a `version.txt` in the cache dir. On read, if
 *     the engine version no longer matches, wipe the directory contents
 *     rather than trying to load stale snapshots.
 *
 * Both run best-effort — any IO error leaves the cache as-is rather than
 * killing the load. Correctness never depends on eviction; the cache key
 * alone is authoritative.
 */

'use strict';

import fs from 'fs';
import path from 'path';
/** Default max cache directory size in bytes. 256MB. */
const DEFAULT_MAX_BYTES = 256 * 1024 * 1024;

/** Filename predicate for compose cache entries. */
function _isComposeEntry(name) {
  return name.startsWith('compose-') && name.endsWith('.bin');
}

// Process-level memo: once a (dir, version) pair has been validated we skip
// all IO on subsequent calls. Invalidated only by a different dir or version.
let _lastDir = null;
let _lastVersion = null;

/**
 * Ensure the cache directory's engine-version tag matches `version`. If it
 * doesn't (or is missing), wipe all `compose-*.bin` files in the dir and
 * write a fresh tag. Non-existent dir is created on demand.
 *
 * Wiping is safe because snapshots are a pure optimization — the next load
 * re-populates on demand.
 */
function ensureVersionTag(dir, version) {
  if (dir === _lastDir && version === _lastVersion) return;
  try {
    fs.mkdirSync(dir, { recursive: true });
    const tagPath = path.join(dir, 'version.txt');
    let current = null;
    try { current = fs.readFileSync(tagPath, 'utf8').trim(); } catch {}
    if (current !== version) {
      // Version mismatch or missing: wipe compose-*.bin (keep subdirs and
      // unrelated files the user might have dropped in).
      let names = [];
      try { names = fs.readdirSync(dir); } catch {}
      for (const name of names) {
        if (_isComposeEntry(name)) {
          try { fs.unlinkSync(path.join(dir, name)); } catch {}
        }
      }
      fs.writeFileSync(tagPath, version);
    }
    _lastDir = dir;
    _lastVersion = version;
  } catch {
    // Best-effort. On any IO error, leave dir alone. Do not memoize —
    // a later retry with healed filesystem state should still run.
  }
}

/**
 * LRU eviction: if the directory's `compose-*.bin` total size exceeds
 * `maxBytes`, delete oldest-atime files until under budget.
 *
 * @param {string} dir        cache dir
 * @param {number} [maxBytes] budget in bytes (default 256MB)
 */
function lruEvict(dir, maxBytes = DEFAULT_MAX_BYTES) {
  try {
    const names = fs.readdirSync(dir);
    const entries = [];
    let total = 0;
    for (const name of names) {
      if (!_isComposeEntry(name)) continue;
      const full = path.join(dir, name);
      let st;
      try { st = fs.statSync(full); } catch { continue; }
      if (!st.isFile()) continue;
      entries.push({ full, size: st.size, atime: st.atimeMs });
      total += st.size;
    }
    if (total <= maxBytes) return;
    // Oldest atime first → delete until under budget.
    entries.sort((a, b) => a.atime - b.atime);
    for (const e of entries) {
      if (total <= maxBytes) break;
      try {
        fs.unlinkSync(e.full);
        total -= e.size;
      } catch {}
    }
  } catch {
    // Best-effort (missing dir, permissions, etc.).
  }
}

/** Test-only: clear the (dir, version) memo. */
function _resetVersionTagMemo() { _lastDir = null; _lastVersion = null; }

export { ensureVersionTag, lruEvict, DEFAULT_MAX_BYTES, _resetVersionTagMemo };
export default { ensureVersionTag, lruEvict, DEFAULT_MAX_BYTES, _resetVersionTagMemo };
