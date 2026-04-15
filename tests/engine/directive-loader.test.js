/**
 * Direct tests for directive-loader.js
 *
 * Covers: scanDirectives, detectDuplicates, parseModality, stateHasFreevars, isSubset.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const fs = require('fs');
const os = require('os');
const Store = require('../../lib/kernel/store');
const dl = require('../../tools/directive-loader');

describe('directive-loader', () => {
  beforeEach(() => Store.clear());

  describe('scanDirectives', () => {
    it('extracts directive names from file content', () => {
      const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'dl-test-'));
      const file1 = path.join(tmpDir, 'test1.ill');
      fs.writeFileSync(file1, '#trace foo.\n#dump_state bar.\nsome content.\n');

      const re = /#(\w+)\s/g;
      const result = dl.scanDirectives([file1], re);

      assert.equal(result.size, 1);
      const names = result.get(file1);
      assert.ok(names.has('trace'));
      assert.ok(names.has('dump_state'));

      fs.rmSync(tmpDir, { recursive: true });
    });

    it('returns empty map for files with no directives', () => {
      const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'dl-test-'));
      const file = path.join(tmpDir, 'empty.ill');
      fs.writeFileSync(file, 'just some content.\n');

      const result = dl.scanDirectives([file], /#(\w+)\s/g);
      assert.equal(result.size, 0);

      fs.rmSync(tmpDir, { recursive: true });
    });
  });

  describe('detectDuplicates', () => {
    it('does not throw when no duplicates', () => {
      const map = new Map([
        ['/a.ill', new Set(['foo'])],
        ['/b.ill', new Set(['bar'])],
      ]);
      assert.doesNotThrow(() => dl.detectDuplicates(map));
    });

    it('throws on duplicate directive names across files', () => {
      const map = new Map([
        ['/a.ill', new Set(['dup'])],
        ['/b.ill', new Set(['dup'])],
      ]);
      assert.throws(() => dl.detectDuplicates(map), /Duplicate directive 'dup'/);
    });
  });

  describe('parseModality', () => {
    it('returns "not" for expect_not', () => {
      assert.equal(dl.parseModality('expect_not'), 'not');
    });

    it('returns "not" for expect_not_ prefix', () => {
      assert.equal(dl.parseModality('expect_not_foo'), 'not');
    });

    it('returns "some" for expect_some', () => {
      assert.equal(dl.parseModality('expect_some'), 'some');
    });

    it('returns "all" for expect prefix', () => {
      assert.equal(dl.parseModality('expect'), 'all');
    });

    it('returns null for unrecognized kind', () => {
      assert.equal(dl.parseModality('random'), null);
    });
  });

  describe('stateHasFreevars', () => {
    it('returns false for ground state', () => {
      const h = Store.put('atom', ['x']);
      assert.equal(dl.stateHasFreevars({ linear: { [h]: 1 }, persistent: {} }), false);
    });

    it('returns true when linear fact has freevar', () => {
      const fv = Store.put('freevar', ['X']);
      const h = Store.put('foo', [fv]);
      assert.equal(dl.stateHasFreevars({ linear: { [h]: 1 }, persistent: {} }), true);
    });

    it('returns true when persistent fact has freevar', () => {
      const fv = Store.put('freevar', ['Y']);
      const h = Store.put('bar', [fv]);
      assert.equal(dl.stateHasFreevars({ linear: {}, persistent: { [h]: true } }), true);
    });
  });

  describe('isSubset', () => {
    it('returns true for empty pattern', () => {
      assert.equal(dl.isSubset({ linear: {}, persistent: {} }, { linear: {}, persistent: {} }), true);
    });

    it('returns true when state contains all pattern facts', () => {
      const h = Store.put('atom', ['x']);
      const pattern = { linear: { [h]: 1 }, persistent: {} };
      const state = { linear: { [h]: 2 }, persistent: {} };
      assert.equal(dl.isSubset(pattern, state), true);
    });

    it('returns false when state is missing a linear fact', () => {
      const h = Store.put('atom', ['x']);
      const pattern = { linear: { [h]: 2 }, persistent: {} };
      const state = { linear: { [h]: 1 }, persistent: {} };
      assert.equal(dl.isSubset(pattern, state), false);
    });

    it('returns false when state is missing a persistent fact', () => {
      const h = Store.put('atom', ['p']);
      const pattern = { linear: {}, persistent: { [h]: true } };
      const state = { linear: {}, persistent: {} };
      assert.equal(dl.isSubset(pattern, state), false);
    });
  });
});
