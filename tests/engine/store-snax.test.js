/**
 * Store-as-SNAX pins (TODO_0309 P4, THY_0037).
 *
 * The split verdict, executable: the content-addressed store violates
 * SNAX's L2 projection-distinctness exactly on equal subtrees (i),
 * but write conflicts are unrepresentable — the address determines
 * the content (ii); the destination TERM algebra satisfies L1+L2 on
 * the nose by constructor injectivity (iii); and addresses flow
 * bottom-up — a composite's hash is a function of its children (iv),
 * which is why content addresses cannot name futures (cell(a,□)).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';

describe('store-as-SNAX (THY_0037)', () => {
  before(() => { Store.clear(); });

  it('(i) L2 falsified: equal subtrees alias to one projected address', () => {
    const v = Store.put('pair_snx', [Store.put('atom', ['leafv']), Store.put('atom', ['leafv'])]);
    // the "pair with equal components": both projections dereference to
    // the SAME hash — aπ1★ = aπ2★, violating aπ1·p1 ≠ aπ2·p2.
    const a = Store.put('pair_snx', [v, v]);
    assert.equal(Store.child(a, 0), Store.child(a, 1),
      'structure sharing: projected addresses collide on equal subtrees');
  });

  it('(ii) L2′: write conflicts are unrepresentable — the address determines the content', () => {
    const x = Store.put('cell_snx', [Store.put('atom', ['v1'])]);
    const y = Store.put('cell_snx', [Store.put('atom', ['v1'])]);
    assert.equal(x, y, 'put is idempotent: the second write IS the first');
    const z = Store.put('cell_snx', [Store.put('atom', ['v2'])]);
    assert.notEqual(x, z, 'a different value cannot be written to the same address');
  });

  it('(iii) the destination TERM algebra satisfies L1+L2 on the nose', () => {
    // Free constructors: p1/p2 as in machine.sax. L1: projections are
    // constructor applications (locally calculable, no dereference).
    // L2: constructor injectivity — distinct projection paths from one
    // base are distinct TERMS, for all extensions.
    const d = Store.put('atom', ['d_snx']);
    const p1d = Store.put('p1_snx', [d]);
    const p2d = Store.put('p2_snx', [d]);
    assert.notEqual(p1d, p2d, 'p1 d ≠ p2 d');
    assert.notEqual(Store.put('p1_snx', [p1d]), Store.put('p1_snx', [p2d]),
      'distinctness survives all projection extensions');
    assert.notEqual(Store.put('p1_snx', [p1d]), Store.put('p2_snx', [p1d]),
      'sibling projections of one base stay distinct');
  });

  it('(iv) addresses flow bottom-up: a composite hash is a function of its children', () => {
    const c1 = Store.put('atom', ['ch1']);
    const c2 = Store.put('atom', ['ch2']);
    const a1 = Store.put('pair_snx', [c1, c2]);
    const a2 = Store.put('pair_snx', [c1, c2]);
    assert.equal(a1, a2, 'same children ⇒ same parent address');
    // The converse of SNAX's allocation order: the parent address
    // cannot exist before the children's values do — cell(a, □) for
    // composite a has no store representation (the temporal no-go).
  });
});
