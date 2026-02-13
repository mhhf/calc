/**
 * FFI Unit Tests
 */

const assert = require('assert');
const ffi = require('../../lib/engine/ffi');
const { binToInt, intToBin, isGround } = require('../../lib/engine/ffi/convert');
const Store = require('../../lib/kernel/store');

describe('FFI Convert', () => {
  beforeEach(() => Store.clear());

  describe('binToInt', () => {
    it('converts e to 0', () => {
      const e = Store.put('atom', ['e']);
      assert.strictEqual(binToInt(e), 0n);
    });

    it('converts (i e) to 1', () => {
      const e = Store.put('atom', ['e']);
      const i = Store.put('atom', ['i']);
      const i_e = Store.put('app', [i, e]);
      assert.strictEqual(binToInt(i_e), 1n);
    });

    it('converts (o (i e)) to 2', () => {
      const e = Store.put('atom', ['e']);
      const i = Store.put('atom', ['i']);
      const o = Store.put('atom', ['o']);
      const i_e = Store.put('app', [i, e]);
      const o_i_e = Store.put('app', [o, i_e]);
      assert.strictEqual(binToInt(o_i_e), 2n);
    });

    it('converts (i (i e)) to 3', () => {
      const e = Store.put('atom', ['e']);
      const i = Store.put('atom', ['i']);
      const i_e = Store.put('app', [i, e]);
      const i_i_e = Store.put('app', [i, i_e]);
      assert.strictEqual(binToInt(i_i_e), 3n);
    });

    it('returns null for metavariable', () => {
      const meta = Store.put('freevar', ['_X']);
      assert.strictEqual(binToInt(meta), null);
    });
  });

  describe('intToBin', () => {
    it('converts 0 to e', () => {
      const h = intToBin(0n);
      const node = Store.get(h);
      assert.strictEqual(node.tag, 'atom');
      assert.strictEqual(node.children[0], 'e');
    });

    it('converts 1 to (i e)', () => {
      const h = intToBin(1n);
      assert.strictEqual(binToInt(h), 1n);
    });

    it('round-trips small numbers', () => {
      for (let n = 0n; n <= 20n; n++) {
        const h = intToBin(n);
        assert.strictEqual(binToInt(h), n, `Failed for ${n}`);
      }
    });

    it('round-trips powers of 2', () => {
      for (const n of [1n, 2n, 4n, 8n, 16n, 32n, 64n, 128n, 256n, 512n, 1024n]) {
        const h = intToBin(n);
        assert.strictEqual(binToInt(h), n, `Failed for ${n}`);
      }
    });

    it('round-trips edge cases', () => {
      for (const n of [127n, 128n, 255n, 256n, 1023n, 1024n, 65535n, 65536n]) {
        const h = intToBin(n);
        assert.strictEqual(binToInt(h), n, `Failed for ${n}`);
      }
    });
  });

  describe('isGround', () => {
    it('returns true for atoms', () => {
      const e = Store.put('atom', ['e']);
      assert.strictEqual(isGround(e), true);
    });

    it('returns true for ground terms', () => {
      const h = intToBin(255n);
      assert.strictEqual(isGround(h), true);
    });

    it('returns false for metavariables', () => {
      const meta = Store.put('freevar', ['_X']);
      assert.strictEqual(isGround(meta), false);
    });

    it('returns true for non-meta freevars', () => {
      const normal = Store.put('freevar', ['X']);
      assert.strictEqual(isGround(normal), true);
    });

    it('returns false for terms containing metavariables', () => {
      const i = Store.put('atom', ['i']);
      const meta = Store.put('freevar', ['_X']);
      const app = Store.put('app', [i, meta]);
      assert.strictEqual(isGround(app), false);
    });
  });
});

describe('FFI Mode', () => {
  beforeEach(() => Store.clear());

  describe('parseMode', () => {
    it('parses "+" mode', () => {
      assert.deepStrictEqual(ffi.mode.parseMode('+'), ['+']);
    });

    it('parses "+ + -" mode', () => {
      assert.deepStrictEqual(ffi.mode.parseMode('+ + -'), ['+', '+', '-']);
    });

    it('handles extra whitespace', () => {
      assert.deepStrictEqual(ffi.mode.parseMode('  +   +   -  '), ['+', '+', '-']);
    });
  });

  describe('checkMode', () => {
    it('accepts ground args for + mode', () => {
      const a = intToBin(5n);
      const b = intToBin(3n);
      assert.strictEqual(ffi.mode.checkMode([a, b], '+ +'), true);
    });

    it('rejects metavar for + mode', () => {
      const a = intToBin(5n);
      const b = Store.put('freevar', ['_X']);
      assert.strictEqual(ffi.mode.checkMode([a, b], '+ +'), false);
    });

    it('accepts metavar for - mode', () => {
      const a = intToBin(5n);
      const b = intToBin(3n);
      const c = Store.put('freevar', ['_C']);
      assert.strictEqual(ffi.mode.checkMode([a, b, c], '+ + -'), true);
    });

    it('rejects wrong arity', () => {
      const a = intToBin(5n);
      assert.strictEqual(ffi.mode.checkMode([a], '+ + -'), false);
    });
  });
});

describe('FFI Arithmetic', () => {
  beforeEach(() => Store.clear());

  describe('plus', () => {
    it('computes 0 + 0 = 0', () => {
      const a = intToBin(0n);
      const b = intToBin(0n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.plus([a, b, c]);

      assert(result.success);
      assert.strictEqual(result.theta.length, 1);
      assert.strictEqual(result.theta[0][0], c);
      assert.strictEqual(binToInt(result.theta[0][1]), 0n);
    });

    it('computes 1 + 1 = 2', () => {
      const a = intToBin(1n);
      const b = intToBin(1n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.plus([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 2n);
    });

    it('computes 255 + 1 = 256', () => {
      const a = intToBin(255n);
      const b = intToBin(1n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.plus([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 256n);
    });

    it('fails mode check for non-ground first input', () => {
      const a = Store.put('freevar', ['_A']);
      const b = intToBin(1n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.plus([a, b, c]);

      assert(!result.success);
      assert.strictEqual(result.reason, 'mode_mismatch');
    });

    it('fails mode check for non-ground second input', () => {
      const a = intToBin(1n);
      const b = Store.put('freevar', ['_B']);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.plus([a, b, c]);

      assert(!result.success);
      assert.strictEqual(result.reason, 'mode_mismatch');
    });
  });

  describe('inc', () => {
    it('computes succ(0) = 1', () => {
      const a = intToBin(0n);
      const b = Store.put('freevar', ['_B']);

      const result = ffi.arithmetic.inc([a, b]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 1n);
    });

    it('computes succ(255) = 256', () => {
      const a = intToBin(255n);
      const b = Store.put('freevar', ['_B']);

      const result = ffi.arithmetic.inc([a, b]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 256n);
    });
  });

  describe('mul', () => {
    it('computes 3 * 5 = 15', () => {
      const a = intToBin(3n);
      const b = intToBin(5n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.mul([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 15n);
    });

    it('computes 0 * 100 = 0', () => {
      const a = intToBin(0n);
      const b = intToBin(100n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.mul([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 0n);
    });
  });

  describe('sub', () => {
    it('computes 5 - 3 = 2', () => {
      const a = intToBin(5n);
      const b = intToBin(3n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.sub([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 2n);
    });

    it('computes 3 - 5 = 0 (saturating)', () => {
      const a = intToBin(3n);
      const b = intToBin(5n);
      const c = Store.put('freevar', ['_C']);

      const result = ffi.arithmetic.sub([a, b, c]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 0n);
    });
  });

  describe('div', () => {
    it('computes 10 / 3 = 3', () => {
      const a = intToBin(10n);
      const b = intToBin(3n);
      const q = Store.put('freevar', ['_Q']);

      const result = ffi.arithmetic.div([a, b, q]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 3n);
    });

    it('fails for division by zero', () => {
      const a = intToBin(10n);
      const b = intToBin(0n);
      const q = Store.put('freevar', ['_Q']);

      const result = ffi.arithmetic.div([a, b, q]);

      assert(!result.success);
      assert.strictEqual(result.reason, 'division_by_zero');
    });
  });

  describe('mod', () => {
    it('computes 10 % 3 = 1', () => {
      const a = intToBin(10n);
      const b = intToBin(3n);
      const r = Store.put('freevar', ['_R']);

      const result = ffi.arithmetic.mod([a, b, r]);

      assert(result.success);
      assert.strictEqual(binToInt(result.theta[0][1]), 1n);
    });
  });

  describe('lt', () => {
    it('returns success for 3 < 5', () => {
      const a = intToBin(3n);
      const b = intToBin(5n);

      const result = ffi.arithmetic.lt([a, b]);

      assert(result.success);
      assert.deepStrictEqual(result.theta, []);
    });

    it('returns failure for 5 < 3', () => {
      const a = intToBin(5n);
      const b = intToBin(3n);

      const result = ffi.arithmetic.lt([a, b]);

      assert(!result.success);
    });

    it('returns failure for 5 < 5', () => {
      const a = intToBin(5n);
      const b = intToBin(5n);

      const result = ffi.arithmetic.lt([a, b]);

      assert(!result.success);
    });
  });
});

describe('FFI Registry', () => {
  it('has arithmetic.plus registered', () => {
    assert(ffi.has('arithmetic.plus'));
  });

  it('has all arithmetic functions registered', () => {
    const expected = ['plus', 'inc', 'mul', 'sub', 'div', 'mod', 'lt', 'le', 'eq'];
    for (const name of expected) {
      assert(ffi.has(`arithmetic.${name}`), `Missing: arithmetic.${name}`);
    }
  });

  it('returns undefined for unknown paths', () => {
    assert.strictEqual(ffi.get('unknown.function'), undefined);
  });
});
