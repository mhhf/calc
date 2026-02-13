/**
 * Tests for Primitive Storage (binlit, strlit, charlit)
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const Store = require('../../lib/kernel/store');
const { unify, unifyBinlit, unifyStrlit } = require('../../lib/kernel/unify');
const {
  binToInt,
  intToBin,
  intToBinRecursive,
  strToHash,
  hashToStr,
  charToHash,
  hashToChar
} = require('../../lib/engine/ffi/convert');
const arithmetic = require('../../lib/engine/ffi/arithmetic');

describe('Primitive Storage', { timeout: 10000 }, () => {
  beforeEach(() => {
    Store.clear();
  });

  describe('binlit', () => {
    it('stores numbers compactly', () => {
      const h = Store.put('binlit', [256n]);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'binlit');
      assert.strictEqual(node.children[0], 256n);
      assert.strictEqual(Store.size(), 1);
    });

    it('deduplicates identical values', () => {
      const h1 = Store.put('binlit', [42n]);
      const h2 = Store.put('binlit', [42n]);
      assert.strictEqual(h1, h2);
    });

    it('handles large 256-bit values', () => {
      const maxU256 = (1n << 256n) - 1n;
      const h = Store.put('binlit', [maxU256]);
      const node = Store.get(h);
      assert.strictEqual(node.children[0], maxU256);
      assert.strictEqual(Store.size(), 1);
    });

    it('handles zero', () => {
      const h = Store.put('binlit', [0n]);
      const node = Store.get(h);
      assert.strictEqual(node.children[0], 0n);
    });
  });

  describe('strlit', () => {
    it('stores strings', () => {
      const h = Store.put('strlit', ['hello']);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'strlit');
      assert.strictEqual(node.children[0], 'hello');
    });

    it('handles empty string', () => {
      const h = Store.put('strlit', ['']);
      const node = Store.get(h);
      assert.strictEqual(node.children[0], '');
    });

    it('handles unicode', () => {
      const h = Store.put('strlit', ['hello 世界 🌍']);
      const node = Store.get(h);
      assert.strictEqual(node.children[0], 'hello 世界 🌍');
    });

    it('deduplicates identical strings', () => {
      const h1 = Store.put('strlit', ['test']);
      const h2 = Store.put('strlit', ['test']);
      assert.strictEqual(h1, h2);
    });
  });

  describe('charlit', () => {
    it('stores character code points', () => {
      const h = Store.put('charlit', [97]); // 'a'
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'charlit');
      assert.strictEqual(node.children[0], 97);
    });

    it('handles unicode code points', () => {
      const h = Store.put('charlit', [0x1F30D]); // 🌍
      const node = Store.get(h);
      assert.strictEqual(node.children[0], 0x1F30D);
    });
  });
});

describe('Convert Functions', { timeout: 10000 }, () => {
  beforeEach(() => {
    Store.clear();
  });

  describe('intToBin', () => {
    it('creates binlit for small numbers', () => {
      const h = intToBin(42n);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'binlit');
      assert.strictEqual(node.children[0], 42n);
    });

    it('creates binlit for zero', () => {
      const h = intToBin(0n);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'binlit');
      assert.strictEqual(node.children[0], 0n);
    });

    it('creates binlit for large numbers', () => {
      const large = (1n << 256n) - 1n;
      const h = intToBin(large);
      assert.strictEqual(Store.size(), 1);
    });
  });

  describe('binToInt', () => {
    it('handles binlit', () => {
      const h = Store.put('binlit', [42n]);
      assert.strictEqual(binToInt(h), 42n);
    });

    it('handles legacy atom e', () => {
      const h = Store.put('atom', ['e']);
      assert.strictEqual(binToInt(h), 0n);
    });

    it('handles legacy i/o form', () => {
      // 10 = (o (i (o (i e)))) = 0 + 2*(1 + 2*(0 + 2*(1 + 2*0)))
      const e = Store.put('atom', ['e']);
      const i = Store.put('atom', ['i']);
      const o = Store.put('atom', ['o']);

      const t1 = Store.put('app', [i, e]);     // (i e) = 1
      const t2 = Store.put('app', [o, t1]);    // (o (i e)) = 2
      const t3 = Store.put('app', [i, t2]);    // (i (o (i e))) = 5
      const t4 = Store.put('app', [o, t3]);    // (o (i (o (i e)))) = 10

      assert.strictEqual(binToInt(t4), 10n);
    });
  });

  describe('intToBinRecursive', () => {
    it('creates legacy form', () => {
      const h = intToBinRecursive(0n);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'atom');
      assert.strictEqual(node.children[0], 'e');
    });

    it('creates correct structure for 1', () => {
      const h = intToBinRecursive(1n);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'app');
      // (i e)
      const head = Store.get(node.children[0]);
      assert.strictEqual(head.children[0], 'i');
    });
  });

  describe('strToHash / hashToStr', () => {
    it('round-trips strings', () => {
      const h = strToHash('hello world');
      assert.strictEqual(hashToStr(h), 'hello world');
    });

    it('handles empty string', () => {
      const h = strToHash('');
      assert.strictEqual(hashToStr(h), '');
    });
  });

  describe('charToHash / hashToChar', () => {
    it('round-trips code points', () => {
      const h = charToHash(97);
      assert.strictEqual(hashToChar(h), 97);
    });
  });
});

describe('Ephemeral Unification', { timeout: 10000 }, () => {
  beforeEach(() => {
    Store.clear();
  });

  describe('binlit patterns', () => {
    it('unifies binlit(0n) with e', () => {
      const zero = Store.put('binlit', [0n]);
      const e = Store.put('atom', ['e']);
      const result = unify(e, zero);
      assert(result !== null);
    });

    it('unifies binlit(10n) with (o X)', () => {
      const ten = Store.put('binlit', [10n]);
      const o = Store.put('atom', ['o']);
      const X = Store.put('freevar', ['_X']);
      const oX = Store.put('app', [o, X]);

      const result = unify(oX, ten);
      assert(result !== null);

      // X should be bound to binlit(5n)
      const binding = result.find(([v]) => v === X);
      assert(binding, 'X should be bound');
      const boundNode = Store.get(binding[1]);
      assert.strictEqual(boundNode.tag, 'binlit');
      assert.strictEqual(boundNode.children[0], 5n);
    });

    it('fails to unify binlit(10n) with (i X)', () => {
      const ten = Store.put('binlit', [10n]);
      const i = Store.put('atom', ['i']);
      const X = Store.put('freevar', ['_X']);
      const iX = Store.put('app', [i, X]);

      const result = unify(iX, ten);
      assert.strictEqual(result, null);
    });

    it('unifies binlit(7n) with (i X)', () => {
      const seven = Store.put('binlit', [7n]);
      const i = Store.put('atom', ['i']);
      const X = Store.put('freevar', ['_X']);
      const iX = Store.put('app', [i, X]);

      const result = unify(iX, seven);
      assert(result !== null);

      // X should be bound to binlit(3n) since 7 = 1 + 2*3
      const binding = result.find(([v]) => v === X);
      assert(binding, 'X should be bound');
      const boundNode = Store.get(binding[1]);
      assert.strictEqual(boundNode.tag, 'binlit');
      assert.strictEqual(boundNode.children[0], 3n);
    });

    it('fails to unify binlit(0n) with (o X)', () => {
      const zero = Store.put('binlit', [0n]);
      const o = Store.put('atom', ['o']);
      const X = Store.put('freevar', ['_X']);
      const oX = Store.put('app', [o, X]);

      const result = unify(oX, zero);
      assert.strictEqual(result, null);
    });

    it('unifies identical binlits', () => {
      const h1 = Store.put('binlit', [42n]);
      const h2 = Store.put('binlit', [42n]);
      const result = unify(h1, h2);
      assert(result !== null);
    });

    it('fails to unify different binlits', () => {
      const h1 = Store.put('binlit', [42n]);
      const h2 = Store.put('binlit', [43n]);
      const result = unify(h1, h2);
      assert.strictEqual(result, null);
    });
  });

  describe('strlit patterns', () => {
    it('unifies strlit("") with nil', () => {
      const empty = Store.put('strlit', ['']);
      const nil = Store.put('atom', ['nil']);
      const result = unify(nil, empty);
      assert(result !== null);
    });

    it('fails to unify strlit("") with cons(H, T)', () => {
      const empty = Store.put('strlit', ['']);
      const cons = Store.put('atom', ['cons']);
      const H = Store.put('freevar', ['_H']);
      const T = Store.put('freevar', ['_T']);
      const consH = Store.put('app', [cons, H]);
      const consHT = Store.put('app', [consH, T]);

      const result = unify(consHT, empty);
      assert.strictEqual(result, null);
    });

    it('unifies strlit("hello") with cons(H, T)', () => {
      const hello = Store.put('strlit', ['hello']);
      const cons = Store.put('atom', ['cons']);
      const H = Store.put('freevar', ['_H']);
      const T = Store.put('freevar', ['_T']);
      const consH = Store.put('app', [cons, H]);
      const consHT = Store.put('app', [consH, T]);

      const result = unify(consHT, hello);
      assert(result !== null);

      // H should be charlit('h')
      const hBinding = result.find(([v]) => v === H);
      assert(hBinding, 'H should be bound');
      const hNode = Store.get(hBinding[1]);
      assert.strictEqual(hNode.tag, 'charlit');
      assert.strictEqual(hNode.children[0], 'h'.charCodeAt(0));

      // T should be strlit("ello")
      const tBinding = result.find(([v]) => v === T);
      assert(tBinding, 'T should be bound');
      const tNode = Store.get(tBinding[1]);
      assert.strictEqual(tNode.tag, 'strlit');
      assert.strictEqual(tNode.children[0], 'ello');
    });

    it('unifies identical strlits', () => {
      const h1 = Store.put('strlit', ['test']);
      const h2 = Store.put('strlit', ['test']);
      const result = unify(h1, h2);
      assert(result !== null);
    });

    it('fails to unify different strlits', () => {
      const h1 = Store.put('strlit', ['test']);
      const h2 = Store.put('strlit', ['other']);
      const result = unify(h1, h2);
      assert.strictEqual(result, null);
    });
  });

  describe('charlit patterns', () => {
    it('unifies identical charlits', () => {
      const h1 = Store.put('charlit', [97]);
      const h2 = Store.put('charlit', [97]);
      const result = unify(h1, h2);
      assert(result !== null);
    });

    it('fails to unify different charlits', () => {
      const h1 = Store.put('charlit', [97]);
      const h2 = Store.put('charlit', [98]);
      const result = unify(h1, h2);
      assert.strictEqual(result, null);
    });

    it('fails to unify charlit with non-charlit', () => {
      const h1 = Store.put('charlit', [97]);
      const h2 = Store.put('atom', ['a']);
      const result = unify(h1, h2);
      assert.strictEqual(result, null);
    });
  });
});

describe('FFI Operations', { timeout: 10000 }, () => {
  beforeEach(() => {
    Store.clear();
  });

  describe('fixed_mul', () => {
    it('scales multiplication correctly', () => {
      // 1.5 * 2.0 with 18 decimals
      // 1.5 = 1_500_000_000_000_000_000
      // 2.0 = 2_000_000_000_000_000_000
      // result = (1.5e18 * 2e18) / 1e18 = 3e18
      const d = intToBin(18n);
      const a = intToBin(1_500_000_000_000_000_000n);
      const b = intToBin(2_000_000_000_000_000_000n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.fixed_mul([d, a, b, c]);
      assert(result.success);

      const cValue = binToInt(result.theta[0][1]);
      assert.strictEqual(cValue, 3_000_000_000_000_000_000n);
    });

    it('handles small decimals', () => {
      // 1.5 * 2.0 with 2 decimals = 150 * 200 / 100 = 300
      const d = intToBin(2n);
      const a = intToBin(150n);
      const b = intToBin(200n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.fixed_mul([d, a, b, c]);
      assert(result.success);

      const cValue = binToInt(result.theta[0][1]);
      assert.strictEqual(cValue, 300n);
    });
  });

  describe('fixed_div', () => {
    it('scales division correctly', () => {
      // 3.0 / 2.0 with 18 decimals
      // 3.0 = 3e18, 2.0 = 2e18
      // result = (3e18 * 1e18) / 2e18 = 1.5e18
      const d = intToBin(18n);
      const a = intToBin(3_000_000_000_000_000_000n);
      const b = intToBin(2_000_000_000_000_000_000n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.fixed_div([d, a, b, c]);
      assert(result.success);

      const cValue = binToInt(result.theta[0][1]);
      assert.strictEqual(cValue, 1_500_000_000_000_000_000n);
    });

    it('fails on division by zero', () => {
      const d = intToBin(2n);
      const a = intToBin(100n);
      const b = intToBin(0n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.fixed_div([d, a, b, c]);
      assert(!result.success);
      assert.strictEqual(result.reason, 'division_by_zero');
    });
  });

  describe('string_concat', () => {
    it('concatenates strings', () => {
      const a = strToHash('hello');
      const b = strToHash(' world');
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.string_concat([a, b, c]);
      assert(result.success);

      const cValue = hashToStr(result.theta[0][1]);
      assert.strictEqual(cValue, 'hello world');
    });

    it('handles empty strings', () => {
      const a = strToHash('test');
      const b = strToHash('');
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.string_concat([a, b, c]);
      assert(result.success);

      const cValue = hashToStr(result.theta[0][1]);
      assert.strictEqual(cValue, 'test');
    });
  });

  describe('string_length', () => {
    it('returns correct length', () => {
      const s = strToHash('hello');
      const len = Store.put('freevar', ['_Len']);

      const result = arithmetic.string_length([s, len]);
      assert(result.success);

      const lenValue = binToInt(result.theta[0][1]);
      assert.strictEqual(lenValue, 5n);
    });

    it('returns 0 for empty string', () => {
      const s = strToHash('');
      const len = Store.put('freevar', ['_Len']);

      const result = arithmetic.string_length([s, len]);
      assert(result.success);

      const lenValue = binToInt(result.theta[0][1]);
      assert.strictEqual(lenValue, 0n);
    });
  });

  describe('binlit with existing arithmetic', () => {
    it('plus works with binlit', () => {
      const a = intToBin(100n);
      const b = intToBin(200n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.plus([a, b, c]);
      assert(result.success);

      const cValue = binToInt(result.theta[0][1]);
      assert.strictEqual(cValue, 300n);
    });

    it('mul works with binlit', () => {
      const a = intToBin(10n);
      const b = intToBin(20n);
      const c = Store.put('freevar', ['_C']);

      const result = arithmetic.mul([a, b, c]);
      assert(result.success);

      const cValue = binToInt(result.theta[0][1]);
      assert.strictEqual(cValue, 200n);
    });
  });
});
