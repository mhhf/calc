const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { show } = require('../../lib/engine/show');
const { isGround, collectMetavars, collectFreevars } = require('../../lib/engine/pattern-utils');
const { serialize, deserialize } = require('../../lib/engine/store-binary');
const { match, matchIndexed, undoSave, undoRestore, unify } = require('../../lib/kernel/unify');
const { arr_get, arr_set, alen, read_bytes, arrToTrie, trieNav } = require('../../lib/engine/ill/ffi/array');
const { parserFromTables, parserTables } = require('../../lib/calculus/builders');

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
      const mv = Store.put('metavar', ['X']);
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
      const mv = Store.put('metavar', ['X']);
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

describe('arrlit - Stage 2: Equational Normalization', () => {
  beforeEach(() => Store.clear());

  describe('match (one-way)', () => {
    it('match(acons(X, Y), arrlit([a,b,c])) → X=a, Y=arrlit([b,c])', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const X = Store.put('metavar', ['X']);
      const Y = Store.put('metavar', ['Y']);
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
      const X = Store.put('metavar', ['X']);
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
      const X = Store.put('metavar', ['X']);
      const Y = Store.put('metavar', ['Y']);
      const Z = Store.put('metavar', ['Z']);
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
      const X = Store.put('metavar', ['X']);
      const Y = Store.put('metavar', ['Y']);
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
      const X = Store.put('metavar', ['X']);
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
      const X = Store.put('metavar', ['X']);
      const Y = Store.put('metavar', ['Y']);
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
      const out = Store.put('metavar', ['V']);
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
      const out = Store.put('metavar', ['V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, true);
      assert.equal(result.theta[0][1], b);
    });

    it('fails on out-of-bounds index', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const idx = Store.put('binlit', [5n]);
      const out = Store.put('metavar', ['V']);
      const result = arr_get([arr, idx, out]);
      assert.equal(result.success, false);
    });

    it('fails on non-ground index', () => {
      const a = Store.put('binlit', [1n]);
      const arr = Store.putArray([a]);
      const idx = Store.put('metavar', ['I']);
      const out = Store.put('metavar', ['V']);
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
      const out = Store.put('metavar', ['R']);
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
      const out = Store.put('metavar', ['L']);
      const result = alen([arr, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0n);
    });

    it('returns length of non-empty array', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const c = Store.put('binlit', [3n]);
      const arr = Store.putArray([a, b, c]);
      const out = Store.put('metavar', ['L']);
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
      const out = Store.put('metavar', ['V']);
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
      const out = Store.put('metavar', ['V']);
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
      const out = Store.put('metavar', ['V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x2030n);
    });

    it('fails on out-of-bounds', () => {
      const b1 = Store.put('binlit', [1n]);
      const arr = Store.putArray([b1]);
      const offset = Store.put('binlit', [0n]);
      const num = Store.put('binlit', [5n]);
      const out = Store.put('metavar', ['V']);
      const result = read_bytes([arr, offset, num, out]);
      assert.equal(result.success, false);
    });
  });
});

describe('arrlit - Stage 4: Hex-to-arrlit Parser', () => {
  beforeEach(() => Store.clear());

  // Build a minimal parser with numbers + application enabled
  function makeParser() {
    const tables = { operators: [], nullary: {}, unaryPrefix: {},
      numbers: true, application: true, binaryNormalization: true };
    return parserFromTables(tables);
  }

  it('short hex stays binlit', () => {
    const parse = makeParser();
    const h = parse('0xFF');
    assert.equal(Store.tag(h), 'binlit');
    assert.equal(Store.child(h, 0), 0xFFn);
  });

  it('32-byte hex (64 chars) stays binlit', () => {
    const parse = makeParser();
    const hex64 = '0x' + 'ab'.repeat(32); // 64 hex chars
    const h = parse(hex64);
    assert.equal(Store.tag(h), 'binlit');
  });

  it('long hex (> 64 chars) → arrlit of byte binlits', () => {
    const parse = makeParser();
    // 66 hex chars = 33 bytes (> 32)
    const hex = '0x' + '60'.repeat(33);
    const h = parse(hex);
    assert.equal(Store.tag(h), 'arrlit');
    const elems = Store.getArrayElements(h);
    assert.equal(elems.length, 33);
    for (let i = 0; i < 33; i++) {
      assert.equal(Store.child(elems[i], 0), 0x60n);
    }
  });

  it('odd-length long hex → parse error', () => {
    const parse = makeParser();
    // 65 hex chars (odd, > 64) → should throw
    assert.throws(() => parse('0x' + 'a'.repeat(65)), /odd-length hex/);
  });

  it('round-trip: hex → arrlit → elements match byte values', () => {
    const parse = makeParser();
    const hex = '0x' + '0102030405060708091011121314151617181920212223242526272829303132aa';
    const h = parse(hex);
    assert.equal(Store.tag(h), 'arrlit');
    const elems = Store.getArrayElements(h);
    assert.equal(elems.length, 33);
    assert.equal(Store.child(elems[0], 0), 0x01n);
    assert.equal(Store.child(elems[32], 0), 0xAAn);
  });
});

describe('arrlit - Stage 6: acons-over-arrlit normalization', () => {
  beforeEach(() => Store.clear());

  it('acons(H, arrlit([a,b])) normalizes to arrlit([H,a,b])', () => {
    const a = Store.put('binlit', [1n]);
    const b = Store.put('binlit', [2n]);
    const h = Store.put('binlit', [3n]);
    const arr = Store.putArray([a, b]);
    const result = Store.put('acons', [h, arr]);
    assert.equal(Store.tag(result), 'arrlit');
    const elems = Store.getArrayElements(result);
    assert.equal(elems.length, 3);
    assert.equal(elems[0], h);
    assert.equal(elems[1], a);
    assert.equal(elems[2], b);
  });

  it('acons(H, ae) normalizes to arrlit([H])', () => {
    const h = Store.put('binlit', [42n]);
    const ae = Store.put('atom', ['ae']);
    const result = Store.put('acons', [h, ae]);
    assert.equal(Store.tag(result), 'arrlit');
    const elems = Store.getArrayElements(result);
    assert.equal(elems.length, 1);
    assert.equal(elems[0], h);
  });

  it('nested acons normalizes: acons(v1, acons(v2, arrlit([v3]))) → arrlit([v1,v2,v3])', () => {
    const v1 = Store.put('binlit', [1n]);
    const v2 = Store.put('binlit', [2n]);
    const v3 = Store.put('binlit', [3n]);
    const arr = Store.putArray([v3]);
    const inner = Store.put('acons', [v2, arr]); // → arrlit([v2, v3])
    assert.equal(Store.tag(inner), 'arrlit');
    const result = Store.put('acons', [v1, inner]); // → arrlit([v1, v2, v3])
    assert.equal(Store.tag(result), 'arrlit');
    const elems = Store.getArrayElements(result);
    assert.equal(elems.length, 3);
    assert.equal(elems[0], v1);
    assert.equal(elems[1], v2);
    assert.equal(elems[2], v3);
  });

  it('acons with freevar + arrlit normalizes to arrlit with freevar', () => {
    const x = Store.put('metavar', ['X']);
    const a = Store.put('binlit', [1n]);
    const arr = Store.putArray([a]);
    const result = Store.put('acons', [x, arr]);
    assert.equal(Store.tag(result), 'arrlit');
    const elems = Store.getArrayElements(result);
    assert.equal(elems.length, 2);
    assert.equal(elems[0], x);
    assert.equal(elems[1], a);
  });

  it('isGround on arrlit with freevar returns false', () => {
    const x = Store.put('metavar', ['X']);
    const a = Store.put('binlit', [1n]);
    const ae = Store.put('atom', ['ae']);
    const result = Store.put('acons', [x, Store.put('acons', [a, ae])]);
    assert.equal(Store.tag(result), 'arrlit');
    assert.equal(isGround(result), false);
  });

  it('collectMetavars finds metavars inside normalized arrlit', () => {
    const x = Store.put('metavar', ['X']);
    const y = Store.put('metavar', ['Y']);
    const ae = Store.put('atom', ['ae']);
    const result = Store.put('acons', [x, Store.put('acons', [y, ae])]);
    assert.equal(Store.tag(result), 'arrlit');
    const vars = new Set();
    collectMetavars(result, vars);
    assert.ok(vars.has(x));
    assert.ok(vars.has(y));
  });

  it('content-addressing: same elements → same hash regardless of construction', () => {
    const a = Store.put('binlit', [1n]);
    const b = Store.put('binlit', [2n]);
    // Build via putArray
    const direct = Store.putArray([a, b]);
    // Build via acons normalization
    const ae = Store.put('atom', ['ae']);
    const via_acons = Store.put('acons', [a, Store.put('acons', [b, ae])]);
    assert.equal(direct, via_acons, 'Same elements should produce same hash');
  });

  it('acons with non-arrlit, non-ae tail is NOT normalized', () => {
    const h = Store.put('binlit', [1n]);
    const y = Store.put('metavar', ['Y']);
    const result = Store.put('acons', [h, y]);
    assert.equal(Store.tag(result), 'acons', 'Should remain acons when tail is freevar');
  });

  it('match works on normalized arrlit patterns', () => {
    const a = Store.put('binlit', [1n]);
    const arr = Store.putArray([a]);
    const X = Store.put('metavar', ['X']);
    const ae = Store.put('atom', ['ae']);
    // acons(X, ae) normalizes to arrlit([X])
    const pat = Store.put('acons', [X, ae]);
    assert.equal(Store.tag(pat), 'arrlit');
    const theta = match(pat, arr);
    assert.ok(theta !== null);
    const xVal = theta.find(([v]) => v === X)?.[1];
    assert.equal(xVal, a);
  });
});

describe('arrlit - Stage 5: Bit-indexed trie', () => {
  beforeEach(() => Store.clear());

  function mkBin(n) { return Store.put('binlit', [BigInt(n)]); }
  function mkIdx(n) { return Store.put('binlit', [BigInt(n)]); }
  function mv(name) { return Store.put('metavar', [name]); }

  describe('arrToTrie', () => {
    it('converts 1-element array', () => {
      const a = mkBin(42);
      const arr = Store.putArray([a]);
      const trie = arrToTrie(arr);
      assert.notEqual(trie, arr);
      assert.equal(Store.tag(trie), 'tn');
    });

    it('converts 4-element array', () => {
      const elems = [mkBin(10), mkBin(20), mkBin(30), mkBin(40)];
      const arr = Store.putArray(elems);
      const trie = arrToTrie(arr);
      assert.equal(Store.tag(trie), 'tn');
    });

    it('returns input unchanged for non-arrlit', () => {
      const atom = Store.put('atom', ['ae']);
      assert.equal(arrToTrie(atom), atom);
    });

    it('returns input unchanged for empty arrlit', () => {
      const arr = Store.putArray([]);
      assert.equal(arrToTrie(arr), arr);
    });
  });

  describe('trie_get via trieNav', () => {
    it('retrieves each element by index from converted trie', () => {
      const elems = [mkBin(10), mkBin(20), mkBin(30), mkBin(40)];
      const arr = Store.putArray(elems);
      const trie = arrToTrie(arr);

      for (let i = 0; i < elems.length; i++) {
        const val = trieNav(trie, BigInt(i));
        assert.notEqual(val, null, `trieNav failed at index ${i}`);
        assert.equal(val, elems[i], `wrong value at index ${i}`);
      }
    });

    it('works for larger arrays (16 elements)', () => {
      const elems = [];
      for (let i = 0; i < 16; i++) elems.push(mkBin(i * 10));
      const trie = arrToTrie(Store.putArray(elems));

      for (let i = 0; i < 16; i++) {
        const val = trieNav(trie, BigInt(i));
        assert.notEqual(val, null, `index ${i}`);
        assert.equal(val, elems[i], `value at index ${i}`);
      }
    });

    it('works for 256-element arrays (bytecode-sized)', () => {
      const elems = [];
      for (let i = 0; i < 256; i++) elems.push(mkBin(i));
      const trie = arrToTrie(Store.putArray(elems));

      for (const i of [0, 1, 2, 127, 128, 255]) {
        const val = trieNav(trie, BigInt(i));
        assert.notEqual(val, null, `index ${i}`);
        assert.equal(val, elems[i], `value at index ${i}`);
      }
    });
  });

  describe('trie_set via arr_set', () => {
    it('updates value at index 0', () => {
      const elems = [mkBin(10), mkBin(20), mkBin(30)];
      const trie = arrToTrie(Store.putArray(elems));
      const newVal = mkBin(99);
      const out = mv('R');
      const result = arr_set([trie, mkIdx(0), newVal, out]);
      assert.equal(result.success, true);

      const newTrie = result.theta[0][1];
      assert.equal(trieNav(newTrie, 0n), newVal);
      assert.equal(trieNav(newTrie, 1n), elems[1]);
      assert.equal(trieNav(newTrie, 2n), elems[2]);
    });

    it('updates value at non-zero index', () => {
      const elems = [mkBin(10), mkBin(20), mkBin(30)];
      const trie = arrToTrie(Store.putArray(elems));
      const newVal = mkBin(77);
      const out = mv('R');
      const result = arr_set([trie, mkIdx(2), newVal, out]);
      assert.equal(result.success, true);

      const newTrie = result.theta[0][1];
      assert.equal(trieNav(newTrie, 2n), newVal);
      // Original unchanged
      assert.equal(trieNav(trie, 2n), elems[2]);
    });
  });

  describe('arr_get FFI on trie', () => {
    it('arr_get works transparently on trie-backed arrays', () => {
      const elems = [mkBin(0x60), mkBin(0x40), mkBin(0x00)];
      const trie = arrToTrie(Store.putArray(elems));

      for (let i = 0; i < elems.length; i++) {
        const out = mv(`V${i}`);
        const result = arr_get([trie, mkIdx(i), out]);
        assert.equal(result.success, true, `arr_get on trie at index ${i}`);
        assert.equal(result.theta[0][1], elems[i]);
      }
    });
  });

  describe('arr_set FFI on trie', () => {
    it('arr_set works transparently on trie-backed arrays', () => {
      const elems = [mkBin(10), mkBin(20)];
      const trie = arrToTrie(Store.putArray(elems));
      const newVal = mkBin(99);
      const out = mv('R');
      const result = arr_set([trie, mkIdx(1), newVal, out]);
      assert.equal(result.success, true);

      const newTrie = result.theta[0][1];
      const r = arr_get([newTrie, mkIdx(1), mv('V')]);
      assert.equal(r.theta[0][1], newVal);
    });
  });

  describe('read_bytes FFI on trie', () => {
    it('reads contiguous bytes from trie', () => {
      const elems = [mkBin(0x10), mkBin(0x20), mkBin(0x30)];
      const trie = arrToTrie(Store.putArray(elems));
      const out = mv('V');
      const result = read_bytes([trie, mkIdx(0), mkIdx(2), out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x1020n);
    });

    it('reads bytes with offset from trie', () => {
      const elems = [mkBin(0x10), mkBin(0x20), mkBin(0x30)];
      const trie = arrToTrie(Store.putArray(elems));
      const out = mv('V');
      const result = read_bytes([trie, mkIdx(1), mkIdx(2), out]);
      assert.equal(result.success, true);
      assert.equal(Store.child(result.theta[0][1], 0), 0x2030n);
    });
  });
});

describe('arrlit - Stage 7: Bracket Syntax + bytesToSemantic', () => {
  beforeEach(() => Store.clear());

  // Build a parser with numbers + application + bracket syntax
  function makeParser() {
    const tables = { operators: [], nullary: {}, unaryPrefix: {},
      numbers: true, application: true, multiCharFreevars: true };
    return parserFromTables(tables);
  }

  describe('bracket syntax', () => {
    it('parses empty []', () => {
      const parse = makeParser();
      const h = parse('[]');
      assert.equal(Store.tag(h), 'arrlit');
      assert.equal(Store.getArrayElements(h).length, 0);
    });

    it('parses [0x60, 0x40]', () => {
      const parse = makeParser();
      const h = parse('[0x60, 0x40]');
      assert.equal(Store.tag(h), 'arrlit');
      const elems = Store.getArrayElements(h);
      assert.equal(elems.length, 2);
      assert.equal(Store.child(elems[0], 0), 0x60n);
      assert.equal(Store.child(elems[1], 0), 0x40n);
    });

    it('parses single-element [0x00]', () => {
      const parse = makeParser();
      const h = parse('[0x00]');
      assert.equal(Store.tag(h), 'arrlit');
      assert.equal(Store.getArrayElements(h).length, 1);
      assert.equal(Store.child(Store.getArrayElements(h)[0], 0), 0n);
    });

    it('parses mixed elements with freevars', () => {
      const parse = makeParser();
      const h = parse('[0x60, 0x73, Member01, 0x33]');
      assert.equal(Store.tag(h), 'arrlit');
      const elems = Store.getArrayElements(h);
      assert.equal(elems.length, 4);
      assert.equal(Store.child(elems[0], 0), 0x60n);
      assert.equal(Store.tag(elems[2]), 'metavar');
      assert.equal(Store.child(elems[3], 0), 0x33n);
    });

    it('bracket syntax in application context: bytecode [0x00]', () => {
      const parse = makeParser();
      const h = parse('bytecode [0x00]');
      assert.equal(Store.tag(h), 'bytecode');
      const arr = Store.child(h, 0);
      assert.equal(Store.tag(arr), 'arrlit');
    });

    it('parses [A | REST] as acons(A, REST)', () => {
      const parse = makeParser();
      const h = parse('[V | REST]');
      assert.equal(Store.tag(h), 'acons');
      assert.equal(Store.tag(Store.child(h, 0)), 'metavar');
      assert.equal(Store.child(Store.child(h, 0), 0), 'V');
      assert.equal(Store.tag(Store.child(h, 1)), 'metavar');
      assert.equal(Store.child(Store.child(h, 1), 0), 'REST');
    });

    it('parses [A, B | REST] as acons(A, acons(B, REST))', () => {
      const parse = makeParser();
      const h = parse('[A, B | REST]');
      assert.equal(Store.tag(h), 'acons');
      assert.equal(Store.child(Store.child(h, 0), 0), 'A');
      const inner = Store.child(h, 1);
      assert.equal(Store.tag(inner), 'acons');
      assert.equal(Store.child(Store.child(inner, 0), 0), 'B');
      assert.equal(Store.child(Store.child(inner, 1), 0), 'REST');
    });

    it('[A, B | ae] normalizes to arrlit via acons+ae normalization', () => {
      const parse = makeParser();
      const h = parse('[0x01, 0x02 | ae]');
      // acons(1, acons(2, ae)) → acons(1, arrlit([2])) → arrlit([1, 2])
      assert.equal(Store.tag(h), 'arrlit');
      const elems = Store.getArrayElements(h);
      assert.equal(elems.length, 2);
      assert.equal(Store.child(elems[0], 0), 1n);
      assert.equal(Store.child(elems[1], 0), 2n);
    });

    it('[compound expr | REST] works with application', () => {
      const parse = makeParser();
      const h = parse('[sha3 X | REST]');
      assert.equal(Store.tag(h), 'acons');
      const head = Store.child(h, 0);
      assert.equal(Store.tag(head), 'sha3');
    });
  });

  describe('bytesToSemantic', () => {
    const { bytesToSemantic } = require('../../lib/engine');

    it('converts PUSH1 data into single value', () => {
      const parse = makeParser();
      // bytecode [0x60, 0x42, 0x00] → PUSH1 0x42, STOP
      const bc = parse('bytecode [0x60, 0x42, 0x00]');
      const state = { linear: { [bc]: 1 }, persistent: {} };
      const result = bytesToSemantic(state);
      // Should convert: [0] = 0x60, [1] = 0x42 (already single byte), [2] = 0x00
      // PUSH1 data is 1 byte so it stays 0x42
      const bcHash = Object.keys(result.linear).find(h =>
        Store.tagId(Number(h)) === Store.TAG['bytecode']
      );
      const arr = Store.child(Number(bcHash), 0);
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 3);
      assert.equal(Store.child(elems[1], 0), 0x42n);
    });

    it('groups PUSH4 data into single big-endian value', () => {
      const parse = makeParser();
      // bytecode [0x63, 0x9e, 0x31, 0x7f, 0x12, 0x14] → PUSH4, data, EQ
      const bc = parse('bytecode [0x63, 0x9e, 0x31, 0x7f, 0x12, 0x14]');
      const state = { linear: { [bc]: 1 }, persistent: {} };
      const result = bytesToSemantic(state);
      const bcHash = Object.keys(result.linear).find(h =>
        Store.tagId(Number(h)) === Store.TAG['bytecode']
      );
      const arr = Store.child(Number(bcHash), 0);
      const elems = Store.getArrayElements(arr);
      assert.equal(elems.length, 6);
      assert.equal(Store.child(elems[0], 0), 0x63n); // PUSH4 opcode
      assert.equal(Store.child(elems[1], 0), 0x9e317f12n); // combined 4 bytes
      assert.equal(Store.child(elems[2], 0), 0n); // gap
      assert.equal(Store.child(elems[3], 0), 0n); // gap
      assert.equal(Store.child(elems[4], 0), 0n); // gap
      assert.equal(Store.child(elems[5], 0), 0x14n); // EQ opcode
    });

    it('no-op on already-semantic (non-byte-level) array', () => {
      // Array with a value > 0xFF → already semantic
      const big = Store.put('binlit', [0x1234n]);
      const small = Store.put('binlit', [0x60n]);
      const arr = Store.putArray([small, big]);
      const bc = Store.put('bytecode', [arr]);
      const state = { linear: { [bc]: 1 }, persistent: {} };
      const result = bytesToSemantic(state);
      // Should return unchanged
      assert.equal(Object.keys(result.linear)[0], String(bc));
    });

    it('no-op on array with freevars', () => {
      const fv = Store.put('metavar', ['X']);
      const small = Store.put('binlit', [0x60n]);
      const arr = Store.putArray([small, fv]);
      const bc = Store.put('bytecode', [arr]);
      const state = { linear: { [bc]: 1 }, persistent: {} };
      const result = bytesToSemantic(state);
      assert.equal(Object.keys(result.linear)[0], String(bc));
    });
  });
});
