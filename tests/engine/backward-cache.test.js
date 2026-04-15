/**
 * Direct tests for backward-cache.js
 *
 * Covers: cache hit, miss, negative cache (failed lookup cached),
 * invalidation on Store.clear, profile tracking.
 */
const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { tryBWCache, clearBWCache, getCacheProfile, resetCacheProfile } = require('../../lib/engine/backward-cache');

describe('backward-cache', () => {
  beforeEach(() => {
    Store.clear(); // Also clears backward cache via Store.onClear
    resetCacheProfile();
  });

  it('returns undefined for non-predicate goals', () => {
    const h = Store.put('atom', ['x']);
    const result = tryBWCache(h, {}, [], {}, false, null, {});
    assert.equal(result, undefined);
  });

  it('returns undefined for goals with no FFI parsed modes', () => {
    const goal = Store.put('foo', [Store.put('atom', ['a'])]);
    const result = tryBWCache(goal, {}, [], {}, false, null, {});
    assert.equal(result, undefined);
  });

  it('returns undefined for all-input modes (no output positions)', () => {
    const goal = Store.put('foo', [Store.put('atom', ['a'])]);
    const result = tryBWCache(goal, {}, [], {}, false, null, { foo: ['+'] });
    assert.equal(result, undefined);
  });

  it('returns undefined when input arg is a metavar', () => {
    const mv = Store.put('metavar', ['X']);
    const goal = Store.put('foo', [mv]);
    const result = tryBWCache(goal, {}, [], {}, false, null, { foo: ['+'] });
    assert.equal(result, undefined);
  });

  it('clearBWCache resets state', () => {
    clearBWCache();
    const profile = getCacheProfile();
    assert.equal(profile.hits, 0);
    assert.equal(profile.misses, 0);
    assert.equal(profile.negHits, 0);
  });

  it('profile tracks misses', () => {
    // Build a goal with output position — will trigger a cache miss probe
    const input = Store.put('atom', ['val']);
    const output = Store.put('metavar', ['Y']);
    const goal = Store.put('inc', [input, output]);

    // Need minimal calc with clauses that will fail resolution
    const calc = { clauses: new Map(), definitions: new Map(), backchainIndex: null };

    tryBWCache(goal, { [output]: 0 }, [undefined], calc, false, null, { inc: ['+', '-'] });
    const profile = getCacheProfile();
    assert.equal(profile.misses, 1);
  });

  it('second lookup of failed goal returns cached negative (negHit)', () => {
    const input = Store.put('atom', ['val']);
    const output = Store.put('metavar', ['Y']);
    const goal = Store.put('inc', [input, output]);

    const calc = { clauses: new Map(), definitions: new Map(), backchainIndex: null };
    const modes = { inc: ['+', '-'] };

    // First call: miss → probe → fail → cache negative
    tryBWCache(goal, { [output]: 0 }, [undefined], calc, false, null, modes);

    // Second call: should return null (cached negative)
    resetCacheProfile();
    const result = tryBWCache(goal, { [output]: 0 }, [undefined], calc, false, null, modes);
    assert.equal(result, null);
    assert.equal(getCacheProfile().negHits, 1);
  });

  it('Store.clear invalidates cache', () => {
    const input = Store.put('atom', ['val']);
    const output = Store.put('metavar', ['Y']);
    const goal = Store.put('inc', [input, output]);
    const calc = { clauses: new Map(), definitions: new Map(), backchainIndex: null };

    tryBWCache(goal, { [output]: 0 }, [undefined], calc, false, null, { inc: ['+', '-'] });
    Store.clear();
    resetCacheProfile();

    // Rebuild after clear
    const input2 = Store.put('atom', ['val']);
    const output2 = Store.put('metavar', ['Y']);
    const goal2 = Store.put('inc', [input2, output2]);

    const result = tryBWCache(goal2, { [output2]: 0 }, [undefined], calc, false, null, { inc: ['+', '-'] });
    // After clear, should be a fresh miss, not a negHit
    assert.equal(getCacheProfile().negHits, 0);
  });
});

describe('backward-cache — positive hit with real calc', () => {
  const path = require('path');
  let calc, modes;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    const loaded = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
    // Build a calc object suitable for tryBWCache (clauses + definitions)
    calc = {
      clauses: loaded.clauses,
      definitions: loaded.definitions,
      backchainIndex: null,
      backwardOpts: {},
    };
    // ffiParsedModes comes from opt/ffi, not from the calc object
    modes = require('../../lib/engine/opt/ffi').ffiParsedModes;
  });

  it('caches successful resolution and returns hit on second call', () => {
    resetCacheProfile();
    const five = Store.put('binlit', [5n]);
    const outMv = Store.put('metavar', ['_out']);
    const goal = Store.put('inc', [five, outMv]);
    const slots = { [outMv]: 0 };
    const theta1 = [undefined];

    // First call: miss → backchain resolves inc(5, ?out) → caches result
    const r1 = tryBWCache(goal, slots, theta1, calc, false, null, modes);
    assert.ok(r1 !== undefined && r1 !== null, 'should resolve inc(5, ?)');
    assert.equal(getCacheProfile().misses, 1);
    assert.equal(getCacheProfile().hits, 0);
    const firstOutput = theta1[0];
    assert.ok(firstOutput !== undefined, 'output should be bound');

    // Second call: same goal → cache hit
    resetCacheProfile();
    const theta2 = [undefined];
    const r2 = tryBWCache(goal, slots, theta2, calc, false, null, modes);
    assert.ok(r2 !== undefined && r2 !== null, 'should hit cache');
    assert.equal(getCacheProfile().hits, 1);
    assert.equal(getCacheProfile().misses, 0);
    assert.equal(theta2[0], firstOutput, 'cached output should match');
  });
});
