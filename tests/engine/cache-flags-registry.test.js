/**
 * Phase 3 of TODO_0218 — central flag registry.
 *
 * Every flag listed in cache-flags.js must produce a different fingerprint
 * when flipped. If this test fails, adding or removing a flag needs matching
 * test updates — don't relax the assertion.
 */

'use strict';

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { ENV_FLAGS, OPT_FLAGS, cacheFlagFingerprint } from '../../lib/engine/cache-flags.js';
import { engineVersion, _resetEngineVersionCache } from '../../lib/engine/engine-version.js';
describe('TODO_0218 Phase 3 — cache-flag registry', () => {
  it('baseline fingerprint is deterministic', () => {
    const a = cacheFlagFingerprint({});
    const b = cacheFlagFingerprint({});
    assert.equal(a, b);
  });

  it('every opt flag in OPT_FLAGS changes the fingerprint when toggled', () => {
    for (const flag of OPT_FLAGS) {
      const off = cacheFlagFingerprint({ [flag]: false });
      const on = cacheFlagFingerprint({ [flag]: true });
      assert.notEqual(on, off, `flag '${flag}' must affect fingerprint`);
    }
  });

  it('every env flag in ENV_FLAGS changes the fingerprint when set', () => {
    for (const flag of ENV_FLAGS) {
      const prev = process.env[flag];
      try {
        delete process.env[flag];
        const unset = cacheFlagFingerprint({});
        process.env[flag] = '1';
        const set = cacheFlagFingerprint({});
        assert.notEqual(set, unset, `env '${flag}' must affect fingerprint`);
      } finally {
        if (prev === undefined) delete process.env[flag];
        else process.env[flag] = prev;
      }
    }
  });
});

describe('TODO_0218 Phase 3 — engine version', () => {
  it('engineVersion is deterministic and stable across calls', () => {
    _resetEngineVersionCache();
    const a = engineVersion();
    const b = engineVersion();
    assert.equal(a, b);
    assert.match(a, /^[0-9a-f]{16}$/);
  });

  it('engineVersion is memoized (second call is cheap)', () => {
    _resetEngineVersionCache();
    const t0 = performance.now();
    engineVersion();
    const cold = performance.now() - t0;
    const t1 = performance.now();
    engineVersion();
    const hot = performance.now() - t1;
    assert.ok(hot * 10 < cold || hot < 0.1, `memo should be ~0ms, got hot=${hot} cold=${cold}`);
  });
});
