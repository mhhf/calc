const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { show } = require('../../lib/engine/show');
const { isGround, collectMetavars, collectFreevars } = require('../../lib/engine/pattern-utils');
const { serialize, deserialize } = require('../../lib/engine/store-binary');
const { match, matchIndexed, undoSave, undoRestore, unify } = require('../../lib/kernel/unify');
const { arr_get, arr_set, alen, read_bytes } = require('../../lib/engine/ffi/array');

describe('arrlit - Stage 1: Store Infrastructure', () => {
  beforeEach(() => Store.clear());

  describe('put/get round-trips', () => {
    it('creates an arrlit with Uint32Array', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      assert.equal(Store.tag(arr), 'arrlit');
      assert.equal(Store.arity(arr), 1);
    });

    it('retrieves elements via getArrayElements', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      const elems = Store.getArrayElements(arr);
      assert.ok(elems instanceof Uint32Array);
      assert.equal(elems.length, 2);
      assert.equal(elems[0], a);
      assert.equal(elems[1], b);
    });

    it('content-addresses: same elements → same hash', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr1 = Store.putArray([a, b]);
      const arr2 = Store.putArray([a, b]);
      assert.equal(arr1, arr2);
    });

    it('different elements → different hash', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr1 = Store.putArray([a, b]);
      const arr2 = Store.putArray([b, a]);
      assert.notEqual(arr1, arr2);
    });

    it('empty arrlit', () => {
      const arr = Store.putArray([]);
      assert.equal(Store.tag(arr), 'arrlit');
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 0);
    });

    it('single-element arrlit', () => {
      const a = Store.put('atom', ['hello']);
      const arr = Store.putArray([a]);
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 1);
      assert.equal(elems[0], a);
    });

    it('Store.get returns Uint32Array child for arrlit', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const node = Store.get(arr);
      assert.equal(node.tag, 'arrlit');
      assert.equal(node.children.length, 1);
      assert.ok(node.children[0] instanceof Uint32Array);
    });

    it('Store.isTermChild returns false for array child', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const child = Store.child(arr, 0);
      assert.equal(Store.isTermChild(child), false);
    });
  });

  describe('show', () => {
    it('displays short arrlit', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      assert.equal(show(arr), '[0x1, 0x2]');
    });

    it('truncates long arrlit', () => {
      const elems = [];
      for (let i = 0; i < 10; i++) elems.push(Store.put('binlit', [BigInt(i)]));
      const arr = Store.putArray(elems);
      const s = show(arr);
      assert.ok(s.includes('...10'));
      assert.ok(s.startsWith('[0x0, 0x1, 0x2, 0x3, 0x4, ...10]'));
    });
  });

  describe('isGround', () => {
    it('ground arrlit → true', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      assert.equal(isGround(arr), true);
    });

    it('arrlit with metavar → false', () => {
      const mv = Store.put('freevar', ['_X']);
      const arr = Store.putArray([mv]);
      assert.equal(isGround(arr), false);
    });

    it('empty arrlit → true', () => {
      const arr = Store.putArray([]);
      assert.equal(isGround(arr), true);
    });
  });

  describe('collectMetavars', () => {
    it('finds metavars inside arrlit', () => {
      const mv = Store.put('freevar', ['_X']);
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a, mv]);
      const out = new Set();
      collectMetavars(arr, out);
      assert.equal(out.size, 1);
      assert.ok(out.has(mv));
    });
  });

  describe('collectFreevars', () => {
    it('finds freevars inside arrlit', () => {
      const fv = Store.put('freevar', ['X']);
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a, fv]);
      const out = collectFreevars(arr);
      assert.equal(out.size, 1);
      assert.ok(out.has(fv));
    });
  });

  describe('clear resets ARRAY_TABLE', () => {
    it('clear clears arrays', () => {
      const a = Store.put('binlit', [1n]);
      Store.putArray([a]);
      Store.clear();
      // After clear, getArrayElements on old hash returns undefined
      assert.equal(Store.getArrayElements(1), undefined);
    });
  });

  describe('snapshot/restore', () => {
    it('preserves arrlits across snapshot/restore', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      const snap = Store.snapshot();

      Store.clear();
      Store.restore(snap);

      assert.equal(Store.tag(arr), 'arrlit');
      const elems = Store.getArrayElements(arr);
      assert.ok(elems instanceof Uint32Array);
      assert.equal(elems.length, 2);
      // After restore, element hashes are same (content-addressed)
      assert.equal(Store.tag(elems[0]), 'binlit');
      assert.equal(Store.child(elems[0], 0), 1n);
    });
  });

  describe('binary serialize/deserialize', () => {
    it('round-trips arrlits through binary format', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);

      Store.clear();
      Store.restore(restored);

      assert.equal(Store.tag(arr), 'arrlit');
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 3);
      assert.equal(Store.child(elems[0], 0), 1n);
      assert.equal(Store.child(elems[1], 0), 2n);
      assert.equal(Store.child(elems[2], 0), 3n);
    });

    it('round-trips empty arrlit through binary format', () => {
      const arr = Store.putArray([]);
      const snap = Store.snapshot();
      const buf = serialize(snap);
      const restored = deserialize(buf);

      Store.clear();
      Store.restore(restored);

      assert.equal(Store.tag(arr), 'arrlit');
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 0);
    });
  });
});

describe('arrlit - Stage 2: Ephemeral Expansion', () => {
  beforeEach(() => Store.clear());

  describe('match (one-way)', () => {
    it('match(acons(X, Y), arrlit([a,b,c])) → X=a, Y=arrlit([b,c])', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const X = Store.put('freevar', ['_X']);
      const Y = Store.put('freevar', ['_Y']);
      const pat = Store.put('acons', [X, Y]);
      const theta = match(pat, arr);
      assert.ok(theta !== null);
      const xVal = theta.find(([v]) => v === X)?.[1];
      const yVal = theta.find(([v]) => v === Y)?.[1];
      assert.equal(xVal, a);
      assert.equal(Store.tag(yVal), 'arrlit');
      const tailElems = Store.getArrayElements(yVal);
      assert.equal(tailElems.length, 2);
      assert.equal(tailElems[0], b);
      assert.equal(tailElems[1], c);
    });

    it('match(ae, arrlit([])) → success', () => {
      const arr = Store.putArray([]);
      const ae = Store.put('atom', ['ae']);
      const theta = match(ae, arr);
      assert.ok(theta !== null);
    });

    it('match(ae, arrlit([a])) → fail', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const ae = Store.put('atom', ['ae']);
      assert.equal(match(ae, arr), null);
    });

    it('match(acons(X, ae), arrlit([a])) → X=a', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const X = Store.put('freevar', ['_X']);
      const ae = Store.put('atom', ['ae']);
      const pat = Store.put('acons', [X, ae]);
      const theta = match(pat, arr);
      assert.ok(theta !== null);
      const xVal = theta.find(([v]) => v === X)?.[1];
      assert.equal(xVal, a);
    });

    it('match(acons(X, acons(Y, Z)), arrlit([a,b,c])) → X=a, Y=b, Z=arrlit([c])', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const X = Store.put('freevar', ['_X']);
      const Y = Store.put('freevar', ['_Y']);
      const Z = Store.put('freevar', ['_Z']);
      const inner = Store.put('acons', [Y, Z]);
      const pat = Store.put('acons', [X, inner]);
      const theta = match(pat, arr);
      assert.ok(theta !== null);
      const xVal = theta.find(([v]) => v === X)?.[1];
      const yVal = theta.find(([v]) => v === Y)?.[1];
      const zVal = theta.find(([v]) => v === Z)?.[1];
      assert.equal(xVal, a);
      assert.equal(yVal, b);
      assert.equal(Store.tag(zVal), 'arrlit');
      assert.equal(Store.getArrayElements(zVal).length, 1);
      assert.equal(Store.getArrayElements(zVal)[0], c);
    });
  });

  describe('unify (two-way)', () => {
    it('unify(acons(X,Y), arrlit([a,b])) → theta', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      const X = Store.put('freevar', ['_X']);
      const Y = Store.put('freevar', ['_Y']);
      const pat = Store.put('acons', [X, Y]);
      const theta = unify(pat, arr);
      assert.ok(theta !== null);
      const xVal = theta.find(([v]) => v === X)?.[1];
      assert.equal(xVal, a);
    });

    it('unify(arrlit([a,b]), arrlit([a,b])) → success', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      // Same hash → trivially equal
      const theta = unify(arr, arr);
      assert.ok(theta !== null);
    });

    it('unify(arrlit([X,b]), arrlit([a,b])) → X=a', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const X = Store.put('freevar', ['_X']);
      const arr1 = Store.putArray([X, b]);
      const arr2 = Store.putArray([a, b]);
      const theta = unify(arr1, arr2);
      assert.ok(theta !== null);
      const xVal = theta.find(([v]) => v === X)?.[1];
      assert.equal(xVal, a);
    });

    it('unify(arrlit([a]), arrlit([a,b])) → fail (length mismatch)', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr1 = Store.putArray([a]);
      const arr2 = Store.putArray([a, b]);
      assert.equal(unify(arr1, arr2), null);
    });
  });

  describe('matchIndexed', () => {
    it('matchIndexed with acons over arrlit', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      const X = Store.put('freevar', ['_X']);
      const Y = Store.put('freevar', ['_Y']);
      const pat = Store.put('acons', [X, Y]);
      const slots = { [X]: 0, [Y]: 1 };
      const theta = new Array(2);
      const saved = undoSave();
      const ok = matchIndexed(pat, arr, theta, slots);
      assert.equal(ok, true);
      assert.equal(theta[0], a);
      assert.equal(Store.tag(theta[1]), 'arrlit');
    });

    it('matchIndexed ae vs empty arrlit', () => {
      const arr = Store.putArray([]);
      const ae = Store.put('atom', ['ae']);
      const theta = new Array(0);
      const slots = {};
      const ok = matchIndexed(ae, arr, theta, slots);
      assert.equal(ok, true);
    });

    it('matchIndexed ae vs non-empty arrlit → fail', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const ae = Store.put('atom', ['ae']);
      const theta = new Array(0);
      const slots = {};
      const ok = matchIndexed(ae, arr, theta, slots);
      assert.equal(ok, false);
    });
  });
});

describe('arrlit - Stage 3: FFI', () => {
  beforeEach(() => Store.clear());

  describe('arr_get', () => {
    it('retrieves element at index 0', () => {
      const a = Store.put('binlit', [0x60n]);
      const b = Store.put('binlit', [0x40n]);
      const arr = Store.putArray([a, b]);
      const idx = Store.put('binlit', [0n]);
      const out = Store.put('freevar', ['_V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, true);
      assert.equal(result.theta[0][0], out);
      assert.equal(result.theta[0][1], a);
    });

    it('retrieves element at index 1', () => {
      const a = Store.put('binlit', [0x60n]);
      const b = Store.put('binlit', [0x40n]);
      const arr = Store.putArray([a, b]);
      const idx = Store.put('binlit', [1n]);
      const out = Store.put('freevar', ['_V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, true);
      assert.equal(result.theta[0][1], b);
    });

    it('fails on out-of-bounds index', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const idx = Store.put('binlit', [5n]);
      const out = Store.put('freevar', ['_V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, false);
    });

    it('fails on non-ground index', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const idx = Store.put('freevar', ['_I']);
      const out = Store.put('freevar', ['_V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, false);
    });
  });

  describe('arr_set', () => {
    it('replaces element at index', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const arr = Store.putArray([a, b]);
      const idx = Store.put('binlit', [0n]);
      const newVal = Store.put('binlit', [99n]);
      const out = Store.put('freevar', ['_R']);
      const result = arr_set([arr, idx, newVal, out]);
      assert.equal(result.success, true);
      const newArr = result.theta[0][1];
      const elems = Store.getArrayElements(newArr);
      assert.equal(Store.child(elems[0], 0), 99n);
      assert.equal(Store.child(elems[1], 0), 2n);
    });
  });

  describe('alen', () => {
    it('returns length of empty array', () => {
      const arr = Store.putArray([]);
      const out = Store.put('freevar', ['_L']);
      const result = alen([arr, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0n);
    });

    it('returns length of non-empty array', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const out = Store.put('freevar', ['_L']);
      const result = alen([arr, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 3n);
    });
  });

  describe('read_bytes', () => {
    it('reads 1 byte', () => {
      const b1 = Store.put('binlit', [0x60n]);
      const b2 = Store.put('binlit', [0x40n]);
      const arr = Store.putArray([b1, b2]);
      const offset = Store.put('binlit', [0n]);
      const num = Store.put('binlit', [1n]);
      const out = Store.put('freevar', ['_V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x60n);
    });

    it('reads 2 bytes big-endian', () => {
      const b1 = Store.put('binlit', [0x60n]);
      const b2 = Store.put('binlit', [0x40n]);
      const arr = Store.putArray([b1, b2]);
      const offset = Store.put('binlit', [0n]);
      const num = Store.put('binlit', [2n]);
      const out = Store.put('freevar', ['_V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x6040n);
    });

    it('reads with offset', () => {
      const b1 = Store.put('binlit', [0x10n]);
      const b2 = Store.put('binlit', [0x20n]);
      const b3 = Store.put('binlit', [0x30n]);
      const arr = Store.putArray([b1, b2, b3]);
      const offset = Store.put('binlit', [1n]);
      const num = Store.put('binlit', [2n]);
      const out = Store.put('freevar', ['_V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x2030n);
    });

    it('fails on out-of-bounds', () => {
      const b1 = Store.put('binlit', [1n]);
      const arr = Store.putArray([b1]);
      const offset = Store.put('binlit', [0n]);
      const num = Store.put('binlit', [5n]);
      const out = Store.put('freevar', ['_V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, false);
    });
  });
});
