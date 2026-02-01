const {
  hash64,
  hashString,
  hashBytes,
  hashBigInt,
  hashNumber,
  hashCombine,
  structHash,
} = require('../lib/hash');
const should = require('chai').should();

describe('Hash', () => {
  describe('hashString', () => {
    it('should produce consistent hashes for same input', () => {
      hashString('hello').should.equal(hashString('hello'));
    });

    it('should produce different hashes for different inputs', () => {
      hashString('hello').should.not.equal(hashString('world'));
    });

    it('should handle empty string', () => {
      const h = hashString('');
      (typeof h).should.equal('bigint');
    });

    it('should handle unicode', () => {
      const h = hashString('hello 世界 🎉');
      (typeof h).should.equal('bigint');
    });
  });

  describe('hashBigInt', () => {
    it('should produce consistent hashes', () => {
      hashBigInt(12345n).should.equal(hashBigInt(12345n));
    });

    it('should produce different hashes for different values', () => {
      hashBigInt(12345n).should.not.equal(hashBigInt(12346n));
    });

    it('should handle zero', () => {
      const h = hashBigInt(0n);
      (typeof h).should.equal('bigint');
    });

    it('should handle negative numbers', () => {
      hashBigInt(-42n).should.not.equal(hashBigInt(42n));
    });

    it('should handle large numbers', () => {
      const large = (1n << 256n) - 1n;
      const h = hashBigInt(large);
      (typeof h).should.equal('bigint');
    });
  });

  describe('hashNumber', () => {
    it('should produce consistent hashes', () => {
      hashNumber(42).should.equal(hashNumber(42));
    });

    it('should handle floats (truncates)', () => {
      hashNumber(3.14).should.equal(hashNumber(3));
    });
  });

  describe('hashBytes', () => {
    it('should produce consistent hashes', () => {
      const buf = new Uint8Array([1, 2, 3, 4]);
      hashBytes(buf).should.equal(hashBytes(new Uint8Array([1, 2, 3, 4])));
    });

    it('should produce different hashes for different buffers', () => {
      const buf1 = new Uint8Array([1, 2, 3]);
      const buf2 = new Uint8Array([1, 2, 4]);
      hashBytes(buf1).should.not.equal(hashBytes(buf2));
    });

    it('should handle empty buffer', () => {
      const h = hashBytes(new Uint8Array(0));
      (typeof h).should.equal('bigint');
    });
  });

  describe('hashCombine', () => {
    it('should combine multiple hashes', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      const combined = hashCombine(h1, h2);
      (typeof combined).should.equal('bigint');
    });

    it('should be order-sensitive', () => {
      const h1 = hashString('a');
      const h2 = hashString('b');
      hashCombine(h1, h2).should.not.equal(hashCombine(h2, h1));
    });

    it('should handle single hash', () => {
      const h = hashString('test');
      const combined = hashCombine(h);
      (typeof combined).should.equal('bigint');
    });
  });

  describe('structHash', () => {
    it('should include constructor ID', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(2, [0x123n]);
      h1.should.not.equal(h2);
    });

    it('should include children', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(1, [0x456n]);
      h1.should.not.equal(h2);
    });

    it('should include arity', () => {
      const h1 = structHash(1, [0x123n]);
      const h2 = structHash(1, [0x123n, 0x123n]);
      h1.should.not.equal(h2);
    });

    it('should handle empty children', () => {
      const h = structHash(5, []);
      (typeof h).should.equal('bigint');
    });

    it('should be consistent', () => {
      structHash(1, [0xABCn, 0xDEFn]).should.equal(structHash(1, [0xABCn, 0xDEFn]));
    });
  });

  describe('hash64', () => {
    it('should dispatch to hashString for strings', () => {
      hash64('test').should.equal(hashString('test'));
    });

    it('should dispatch to hashBigInt for bigints', () => {
      hash64(42n).should.equal(hashBigInt(42n));
    });

    it('should dispatch to hashNumber for numbers', () => {
      hash64(42).should.equal(hashNumber(42));
    });

    it('should dispatch to hashBytes for Uint8Array', () => {
      const buf = new Uint8Array([1, 2, 3]);
      hash64(buf).should.equal(hashBytes(buf));
    });

    it('should handle arrays by hashing elements', () => {
      const h = hash64(['a', 'b', 'c']);
      (typeof h).should.equal('bigint');
    });

    it('should throw for unsupported types', () => {
      (() => hash64({})).should.throw(/Cannot hash/);
    });
  });

  describe('collision resistance', () => {
    it('should have low collision rate for sequential strings', () => {
      const hashes = new Set();
      for (let i = 0; i < 10000; i++) {
        hashes.add(hashString(`test_${i}`));
      }
      // Should have no collisions for 10k sequential strings
      hashes.size.should.equal(10000);
    });

    it('should have low collision rate for sequential integers', () => {
      const hashes = new Set();
      for (let i = 0; i < 10000; i++) {
        hashes.add(hashBigInt(BigInt(i)));
      }
      hashes.size.should.equal(10000);
    });
  });
});
