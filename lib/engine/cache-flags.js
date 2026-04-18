/**
 * Central registry of cache-affecting inputs for the compose disk cache.
 *
 * Any env var / option that changes the compose pipeline's output MUST be
 * listed here. Leaving one out = soundness bug (stale cache hits produce
 * wrong results).
 *
 * Hazard H8 of TODO_0218. Tests can verify each listed flag actually changes
 * the produced cache key (see tests/engine/cache-flags-registry.test.js).
 */

'use strict';

/**
 * Names of env vars that feed compose semantics. Values are read at key
 * construction time, so flipping a flag between runs invalidates prior
 * snapshots automatically.
 */
const ENV_FLAGS = Object.freeze([
  'CALC_0216_POOL_DISJOINT',
  'CALC_0217_FFI_OFF',
  'CALC_0217_MEMO_OFF',
]);

/**
 * Names of load-opts that change compose output and must participate in the
 * cache key. Booleans + primitives only — complex objects (like scopeGuard,
 * residualResolver) are replaced by derived content hashes upstream.
 */
const OPT_FLAGS = Object.freeze([
  'fuseBasicBlocks',
  'cacheVersion',
]);

/**
 * Build the cache-affecting input fingerprint. Returns a deterministic
 * string — stable across processes with identical env + opts.
 *
 * Format: `env:K1=V1|K2=V2|...;opt:A=B|C=D|...`
 * Missing env vars are rendered as empty string ("").
 */
function cacheFlagFingerprint(opts) {
  const envParts = ENV_FLAGS.map(k => `${k}=${process.env[k] || ''}`).join('|');
  const optParts = OPT_FLAGS.map(k => {
    const v = opts && opts[k] !== undefined ? opts[k] : '';
    return `${k}=${JSON.stringify(v)}`;
  }).join('|');
  return `env:${envParts};opt:${optParts}`;
}

export { ENV_FLAGS, OPT_FLAGS, cacheFlagFingerprint };
export default { ENV_FLAGS, OPT_FLAGS, cacheFlagFingerprint };
