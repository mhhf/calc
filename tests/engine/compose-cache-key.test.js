/**
 * Direct tests for compose.js cache key functions (C22 fix verification)
 *
 * Covers: _tablingCacheKey, _composeFullKey — canonical string keys,
 * collision resistance vs old 32-bit hash.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { _tablingCacheKey, _composeFullKey } = require('../../lib/engine/compose');

describe('compose cache keys (C22)', () => {
  beforeEach(() => Store.clear());

  describe('_tablingCacheKey', () => {
    it('returns string key', () => {
      const key = _tablingCacheKey(new Map(), new Map());
      assert.equal(typeof key, 'string');
    });

    it('same clauses+definitions produce same key', () => {
      const h1 = Store.put('atom', ['a']);
      const h2 = Store.put('atom', ['b']);
      const clauses = new Map([['c1', { hash: h1 }]]);
      const defs = new Map([['d1', h2]]);

      const k1 = _tablingCacheKey(clauses, defs);
      const k2 = _tablingCacheKey(clauses, defs);
      assert.equal(k1, k2);
    });

    it('different clauses produce different key', () => {
      const h1 = Store.put('atom', ['a']);
      const h2 = Store.put('atom', ['b']);
      const clauses1 = new Map([['c1', { hash: h1 }]]);
      const clauses2 = new Map([['c1', { hash: h2 }]]);
      const defs = new Map();

      const k1 = _tablingCacheKey(clauses1, defs);
      const k2 = _tablingCacheKey(clauses2, defs);
      assert.notEqual(k1, k2);
    });

    it('handles null clauses/definitions', () => {
      const key = _tablingCacheKey(null, null);
      assert.equal(typeof key, 'string');
      assert.equal(key, '|');
    });
  });

  describe('_composeFullKey', () => {
    it('includes rule hashes in key', () => {
      const r1 = { hash: Store.put('atom', ['r1']) };
      const r2 = { hash: Store.put('atom', ['r2']) };

      const k1 = _composeFullKey([r1], new Map(), new Map(), null, false);
      const k2 = _composeFullKey([r1, r2], new Map(), new Map(), null, false);
      assert.notEqual(k1, k2);
    });

    it('includes resolver flag in key', () => {
      const r1 = { hash: Store.put('atom', ['r1']) };
      const k1 = _composeFullKey([r1], new Map(), new Map(), null, false);
      const k2 = _composeFullKey([r1], new Map(), new Map(), null, true);
      assert.notEqual(k1, k2);
    });

    it('includes extra grade0 facts in key', () => {
      const r1 = { hash: Store.put('atom', ['r1']) };
      const f1 = { hash: Store.put('atom', ['f1']) };
      const extra = new Map([['pred', [f1]]]);

      const k1 = _composeFullKey([r1], new Map(), new Map(), null, false);
      const k2 = _composeFullKey([r1], new Map(), new Map(), extra, false);
      assert.notEqual(k1, k2);
    });

    it('returns deterministic key for same inputs', () => {
      const r1 = { hash: Store.put('atom', ['r1']) };
      const clauses = new Map([['c', { hash: Store.put('atom', ['c']) }]]);
      const defs = new Map([['d', Store.put('atom', ['d'])]]);

      const k1 = _composeFullKey([r1], clauses, defs, null, false);
      const k2 = _composeFullKey([r1], clauses, defs, null, false);
      assert.equal(k1, k2);
    });
  });
});
