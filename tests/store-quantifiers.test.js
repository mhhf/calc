/**
 * Tests for Store quantifier support: bound/exists/forall/evar tags,
 * debruijnSubst, and fresh eigenvariable generation.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');

const Store = require('../lib/kernel/store');
const { debruijnSubst } = require('../lib/kernel/substitute');
const { freshEvar, resetFresh, getFreshCounter } = require('../lib/kernel/fresh');

describe('Store quantifier tags', () => {
  it('bound(0) tag registration', () => {
    const b0 = Store.put('bound', [0n]);
    assert.strictEqual(Store.tag(b0), 'bound');
    assert.strictEqual(Store.child(b0, 0), 0n);
    assert.strictEqual(Store.arity(b0), 1);
  });

  it('evar tag registration via freshEvar', () => {
    resetFresh(100n);
    const e = freshEvar();
    assert.strictEqual(Store.tag(e), 'evar');
    assert.strictEqual(Store.child(e, 0), 100n);
    const e2 = freshEvar();
    assert.strictEqual(Store.child(e2, 0), 101n);
    assert.notStrictEqual(e, e2);
  });

  it('exists/forall Store.put + get', () => {
    const a = Store.put('atom', ['p']);
    const ex = Store.put('exists', [a]);
    assert.strictEqual(Store.tag(ex), 'exists');
    assert.strictEqual(Store.child(ex, 0), a);
    assert.strictEqual(Store.arity(ex), 1);

    const fa = Store.put('forall', [a]);
    assert.strictEqual(Store.tag(fa), 'forall');
    assert.strictEqual(Store.child(fa, 0), a);
  });

  it('alpha-equivalence: same body → same hash', () => {
    const p = Store.put('atom', ['p']);
    const b0 = Store.put('bound', [0n]);
    const body = Store.put('app', [p, b0]);
    const ex1 = Store.put('exists', [body]);
    const ex2 = Store.put('exists', [body]);
    assert.strictEqual(ex1, ex2);
  });

  it('evar content-addressing: same N → same hash', () => {
    const e1 = Store.put('evar', [42n]);
    const e2 = Store.put('evar', [42n]);
    assert.strictEqual(e1, e2);
    const e3 = Store.put('evar', [43n]);
    assert.notStrictEqual(e1, e3);
  });
});

describe('debruijnSubst', () => {
  it('basic: replace bound(0) with atom', () => {
    const p = Store.put('atom', ['p']);
    const a = Store.put('atom', ['a']);
    const b0 = Store.put('bound', [0n]);
    const body = Store.put('app', [p, b0]);
    const result = debruijnSubst(body, 0n, a);
    const expected = Store.put('app', [p, a]);
    assert.strictEqual(result, expected);
  });

  it('nested: outer replaces only bound(1) under binder', () => {
    const p = Store.put('atom', ['p']);
    const b0 = Store.put('bound', [0n]);
    const b1 = Store.put('bound', [1n]);
    const inner = Store.put('app', [p, b0, b1]);
    const body = Store.put('exists', [inner]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    const expectedInner = Store.put('app', [p, b0, a]);
    const expected = Store.put('exists', [expectedInner]);
    assert.strictEqual(result, expected);
  });

  it('no-change: bound(1) untouched at index=0', () => {
    const p = Store.put('atom', ['p']);
    const b1 = Store.put('bound', [1n]);
    const body = Store.put('app', [p, b1]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    assert.strictEqual(result, body);
  });

  it('replacement containing bound is not captured', () => {
    const p = Store.put('atom', ['p']);
    const q = Store.put('atom', ['q']);
    const b0 = Store.put('bound', [0n]);
    const body = Store.put('app', [p, b0]);
    const replacement = Store.put('app', [q, b0]);
    const result = debruijnSubst(body, 0n, replacement);
    const expected = Store.put('app', [p, replacement]);
    assert.strictEqual(result, expected);
  });

  it('nested forall binder', () => {
    const p = Store.put('atom', ['p']);
    const b0 = Store.put('bound', [0n]);
    const b1 = Store.put('bound', [1n]);
    const inner = Store.put('app', [p, b0, b1]);
    const body = Store.put('forall', [inner]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    const expectedInner = Store.put('app', [p, b0, a]);
    const expected = Store.put('forall', [expectedInner]);
    assert.strictEqual(result, expected);
  });
});

describe('freshEvar', () => {
  it('monotonic counter', () => {
    resetFresh(10n);
    assert.strictEqual(getFreshCounter(), 10n);
    const e1 = freshEvar();
    const e2 = freshEvar();
    assert.strictEqual(Store.child(e1, 0), 10n);
    assert.strictEqual(Store.child(e2, 0), 11n);
    assert.strictEqual(getFreshCounter(), 12n);
  });
});
