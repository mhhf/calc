const { describe, it } = require('node:test');
const assert = require('node:assert');
const {
  hashString,
  hashBigInt,
  hashCombine,
} = require('../lib/hash');

describe('Hash', () => {
  describe('hashString', () => {
    it('should produce consistent hashes for same input', () => {
      assert.strictEqual(hashString('hello'), hashString('hello'));
    });

    it('should produce different hashes for different inputs', () => {
      assert.notStrictEqual(hashString('hello'), hashString('world'));
    });

    it('should handle empty string', () => {
      const h = hashString('');
      assert.strictEqual(typeof h, 'number');
    });

    it('should handle unicode', () => {
      const h = hashString('hello 世界 🎉');
      assert.strictEqual(typeof h, 'number');
    });
  });

  describe('hashBigInt', () => {
    it('should produce consistent hashes', () => {
      assert.strictEqual(hashBigInt(12345n), hashBigInt(12345n));
    });

    it('should produce different hashes for different values', () => {
      assert.notStrictEqual(hashBigInt(12345n), hashBigInt(12346n));
    });

    it('should handle zero', () => {
      const h = hashBigInt(0n);
      assert.strictEqual(typeof h, 'number');
    });

    it('should handle negative numbers', () => {
      assert.notStrictEqual(hashBigInt(-42n), hashBigInt(42n));
    });

    it('should handle large numbers', () => {
      const large = (1n << 256n) - 1n;
      const h = hashBigInt(large);
      assert.strictEqual(typeof h, 'number');
    });
  });

  describe('hashCombine', () => {
    it('should combine multiple hashes', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      const combined = hashCombine(h1, h2);
      assert.strictEqual(typeof combined, 'number');
    });

    it('should be order-sensitive', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      assert.notStrictEqual(hashCombine(h1, h2), hashCombine(h2, h1));
    });

    it('should handle single hash', () => {
      const h = hashString('test');
      const combined = hashCombine(h);
      assert.strictEqual(typeof combined, 'number');
    });
  });

  describe('collision resistance', () => {
    it('should have low collision rate for sequential strings', () => {
      const hashes = new Set();
      for (let i = 0; i < 10000; i++) {
        hashes.add(hashString(`test_${i}`));
      }
      assert.strictEqual(hashes.size, 10000);
    });

    it('should have low collision rate for sequential integers', () => {
      const hashes = new Set();
      for (let i = 0; i < 10000; i++) {
        hashes.add(hashBigInt(BigInt(i)));
      }
      assert.strictEqual(hashes.size, 10000);
    });
  });
});
