const { describe, it } = require('node:test');
const assert = require('node:assert');
const {
  hash64,
  hashString,
  hashBytes,
  hashBigInt,
  hashNumber,
  hashCombine,
  structHash,
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
      assert.strictEqual(typeof h, 'bigint');
    });

    it('should handle unicode', () => {
      const h = hashString('hello 世界 🎉');
      assert.strictEqual(typeof h, 'bigint');
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
      assert.strictEqual(typeof h, 'bigint');
    });

    it('should handle negative numbers', () => {
      assert.notStrictEqual(hashBigInt(-42n), hashBigInt(42n));
    });

    it('should handle large numbers', () => {
      const large = (1n << 256n) - 1n;
      const h = hashBigInt(large);
      assert.strictEqual(typeof h, 'bigint');
    });
  });

  describe('hashNumber', () => {
    it('should produce consistent hashes', () => {
      assert.strictEqual(hashNumber(42), hashNumber(42));
    });

    it('should handle floats (truncates)', () => {
      assert.strictEqual(hashNumber(3.14), hashNumber(3));
    });
  });

  describe('hashBytes', () => {
    it('should produce consistent hashes', () => {
      const buf = new Uint8Array([1, 2, 3, 4]);
      assert.strictEqual(hashBytes(buf), hashBytes(new Uint8Array([1, 2, 3, 4])));
    });

    it('should produce different hashes for different buffers', () => {
      const buf1 = new Uint8Array([1, 2, 3]);
      const buf2 = new Uint8Array([1, 2, 4]);
      assert.notStrictEqual(hashBytes(buf1), hashBytes(buf2));
    });

    it('should handle empty buffer', () => {
      const h = hashBytes(new Uint8Array(0));
      assert.strictEqual(typeof h, 'bigint');
    });
  });

  describe('hashCombine', () => {
    it('should combine multiple hashes', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      const combined = hashCombine(h1, h2);
      assert.strictEqual(typeof combined, 'bigint');
    });

    it('should be order-sensitive', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      assert.notStrictEqual(hashCombine(h1, h2), hashCombine(h2, h1));
    });

    it('should handle single hash', () => {
      const h = hashString('test');
      const combined = hashCombine(h);
      assert.strictEqual(typeof combined, 'bigint');
    });
  });

  describe('structHash', () => {
    it('should include constructor ID', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(2, [0x123n]);
      assert.notStrictEqual(h1, h2);
    });

    it('should include children', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(1, [0x456n]);
      assert.notStrictEqual(h1, h2);
    });

    it('should include arity', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(1, [0x123n, 0x123n]);
      assert.notStrictEqual(h1, h2);
    });

    it('should handle empty children', () => {
      const h = structHash(5, []);
      assert.strictEqual(typeof h, 'bigint');
    });

    it('should be consistent', () => {
      assert.strictEqual(structHash(1, [0xABCn, 0xDEFn]), structHash(1, [0xABCn, 0xDEFn]));
    });
  });

  describe('hash64', () => {
    it('should dispatch to hashString for strings', () => {
      assert.strictEqual(hash64('test'), hashString('test'));
    });

    it('should dispatch to hashBigInt for bigints', () => {
      assert.strictEqual(hash64(42n), hashBigInt(42n));
    });

    it('should dispatch to hashNumber for numbers', () => {
      assert.strictEqual(hash64(42), hashNumber(42));
    });

    it('should dispatch to hashBytes for Uint8Array', () => {
      const buf = new Uint8Array([1, 2, 3]);
      assert.strictEqual(hash64(buf), hashBytes(buf));
    });

    it('should handle arrays by hashing elements', () => {
      const h = hash64(['a', 'b', 'c']);
      assert.strictEqual(typeof h, 'bigint');
    });

    it('should throw for unsupported types', () => {
      assert.throws(() => hash64({}), /Cannot hash/);
    });
  });

  describe('collision resistance', () => {
    it('should have low collision rate for sequential strings', () => {
      const hashes = new Set();
      for (let i = 0; i < 10000; i++) {
        hashes.add(hashString(`test_${i}`));
      }
      // Should have no collisions for 10k sequential strings
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
