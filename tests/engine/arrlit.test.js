const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { show } = require('../../lib/engine/show');
const { isGround, collectMetavars, collectFreevars } = require('../../lib/engine/pattern-utils');
const { serialize, deserialize } = require('../../lib/engine/store-binary');

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
