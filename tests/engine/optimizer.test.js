/**
 * Direct tests for optimizer.js
 *
 * Covers: profile (bare/fast/full), env var override, custom profiles.
 */
import { describe, it, beforeEach, afterEach } from 'node:test';
import assert from 'node:assert/strict';
import { profile } from '../../lib/engine/optimizer.js';
describe('profile', () => {
  let savedEnv;

  beforeEach(() => {
    savedEnv = process.env.CALC_PROFILE;
    delete process.env.CALC_PROFILE;
  });

  afterEach(() => {
    if (savedEnv !== undefined) process.env.CALC_PROFILE = savedEnv;
    else delete process.env.CALC_PROFILE;
  });

  it('defaults to the all-on full profile', () => {
    const p = profile();
    assert.equal(p.name, 'full');
    assert.equal(p.ffi, true);
    assert.equal(p.discTree, true);
    assert.equal(p.fingerprint, true);
    assert.equal(p.structuralMemo, true);
  });

  it('resolves bare profile — all optimizations off', () => {
    const p = profile('bare');
    assert.equal(p.name, 'bare');
    assert.equal(p.ffi, false);
    assert.equal(p.discTree, false);
    assert.equal(p.fingerprint, false);
    assert.equal(p.compiledSub, false);
  });

  it('resolves fast profile — FFI + compiledSub + preserved', () => {
    const p = profile('fast');
    assert.equal(p.name, 'fast');
    assert.equal(p.ffi, true);
    assert.equal(p.compiledSub, true);
    assert.equal(p.preserved, true);
    assert.equal(p.discTree, false);
    assert.equal(p.fingerprint, false);
  });

  it('throws on unknown profile name', () => {
    assert.throws(() => profile('nonexistent'), /Unknown profile/);
  });

  it('accepts custom object profile', () => {
    const p = profile({ ffi: true, discTree: false });
    assert.equal(p.name, 'custom');
    assert.equal(p.ffi, true);
    assert.equal(p.discTree, false);
    // Defaults fill in missing fields
    assert.equal(p.fingerprint, false);
  });

  it('CALC_PROFILE env var overrides argument', () => {
    process.env.CALC_PROFILE = 'bare';
    const p = profile('full');
    assert.equal(p.name, 'bare');
    assert.equal(p.ffi, false);
  });

  it('env var throws on unknown profile', () => {
    process.env.CALC_PROFILE = 'bogus';
    assert.throws(() => profile(), /Unknown profile/);
  });
});
