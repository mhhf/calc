/**
 * Regression test for decomposeQuery — B9 depth-aware substitution fix.
 *
 * Verifies de Bruijn depth-aware substitution correctly handles nested quantifiers.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');

describe('decomposeQuery — nested quantifiers (B9)', () => {
  let decomposeQuery;

  before(() => {
    Store.clear();
    require('../../lib/engine/ill/backchain-ill').initILL();
    decomposeQuery = require('../../lib/engine/convert').decomposeQuery;
  });

  it('decomposes flat forall X. forall Y. tensor(P(X), Q(Y))', () => {
    // De Bruijn: bound(1) = X (outermost), bound(0) = Y (innermost)
    const px = Store.put('pp', [Store.put('bound', [1n])]);
    const qy = Store.put('qq', [Store.put('bound', [0n])]);
    const body = Store.put('tensor', [px, qy]);
    const inner = Store.put('forall', [body]);
    const outer = Store.put('forall', [inner]);

    const result = decomposeQuery(outer);
    const linHashes = Object.keys(result.linear).map(Number);
    assert.equal(linHashes.length, 2);

    for (const h of linHashes) {
      const tag = Store.tag(h);
      assert.ok(tag === 'pp' || tag === 'qq');
      const child = Store.child(h, 0);
      assert.equal(Store.tag(child), 'freevar');
    }
  });

  it('decomposes forall X. exists Y. tensor(P(X), Q(Y))', () => {
    // De Bruijn: bound(1) = X (forall), bound(0) = Y (exists)
    const px = Store.put('pp', [Store.put('bound', [1n])]);
    const qy = Store.put('qq', [Store.put('bound', [0n])]);
    const body = Store.put('tensor', [px, qy]);
    const inner = Store.put('exists', [body]);
    const outer = Store.put('forall', [inner]);

    const result = decomposeQuery(outer);
    const linHashes = Object.keys(result.linear).map(Number);
    assert.equal(linHashes.length, 2);

    let foundFreevar = false, foundMetavar = false;
    for (const h of linHashes) {
      const child = Store.child(h, 0);
      const childTag = Store.tag(child);
      if (childTag === 'freevar') foundFreevar = true;
      if (childTag === 'metavar') foundMetavar = true;
    }
    assert.ok(foundFreevar, 'forall X should produce freevar');
    assert.ok(foundMetavar, 'exists Y should produce metavar');
  });

  it('nested exists inside tensor — depth-aware substitution (B9 regression)', () => {
    // forall X. tensor(P(X), exists Y. Q(X, Y))
    //
    // De Bruijn:
    //   In forall body:   X = bound(0)
    //   In exists body:   Y = bound(0), X = bound(1) (shifted by inner binder)
    //
    // Only the top-level forall is stripped. The inner exists stays as-is.
    // decomposeQuery produces:
    //   linear = { P(freevar): 1, exists(Q(freevar, bound(0))): 1 }
    //
    // B9 bug: old code used flat substitution, replacing ALL bound(0)
    // with freevar — including the bound(0) inside exists that refers to Y.
    // Fixed: debruijnSubst is depth-aware.

    const xRef = Store.put('bound', [0n]);  // X in forall body
    const px = Store.put('pp', [xRef]);

    // exists Y. Q(X, Y): under exists, X = bound(1), Y = bound(0)
    const xInner = Store.put('bound', [1n]);
    const yInner = Store.put('bound', [0n]);
    const qxy = Store.put('qq', [xInner, yInner]);
    const existsY = Store.put('exists', [qxy]);

    const body = Store.put('tensor', [px, existsY]);
    const forallX = Store.put('forall', [body]);

    const result = decomposeQuery(forallX);
    const linHashes = Object.keys(result.linear).map(Number);
    assert.equal(linHashes.length, 2);

    // Find the P and exists facts
    let pHash = null, existsHash = null;
    for (const h of linHashes) {
      const tag = Store.tag(h);
      if (tag === 'pp') pHash = h;
      if (tag === 'exists') existsHash = h;
    }

    assert.ok(pHash, 'should have P fact');
    assert.ok(existsHash, 'should have exists fact (inner exists not stripped)');

    // P(X): child should be freevar (X was correctly substituted)
    const pChild = Store.child(pHash, 0);
    assert.equal(Store.tag(pChild), 'freevar');

    // exists(Q(X', Y)): the body of exists should have:
    //   child 0 = freevar (X correctly substituted via depth-aware debruijnSubst)
    //   child 1 = bound(0) (Y NOT substituted — it's the exists-bound var)
    const existsBody = Store.child(existsHash, 0); // Q(X', Y)
    assert.equal(Store.tag(existsBody), 'qq');
    const qChild0 = Store.child(existsBody, 0);
    const qChild1 = Store.child(existsBody, 1);
    assert.equal(Store.tag(qChild0), 'freevar', 'Q first arg should be freevar (X correctly substituted)');
    assert.equal(Store.tag(qChild1), 'bound', 'Q second arg should stay as bound (Y, the exists binder)');
  });
});
