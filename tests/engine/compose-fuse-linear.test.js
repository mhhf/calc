/**
 * Direct tests for compose.js:fuseLinearPair
 *
 * Covers: exists opening, predicate matching, unification failure handling.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { fuseLinearPair } = require('../../lib/engine/compose');
const { resolveConnectives } = require('../../lib/engine/compile');

describe('fuseLinearPair', () => {
  let rc;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
    const ccfg = require('../../lib/engine/ill/calculus-config');
    rc = resolveConnectives(ccfg.connectives);
  });

  it('returns null when cut predicate not found in producer consequent', () => {
    const a = Store.put('gas', [Store.put('atom', ['x'])]);
    const b = Store.put('pc', [Store.put('atom', ['y'])]);
    const bodyP = Store.put('monad', [b]);
    const producer = { hash: Store.put('loli', [a, bodyP]) };

    const c = Store.put('stack', [Store.put('atom', ['z'])]);
    const d = Store.put('mem', [Store.put('atom', ['w'])]);
    const bodyC = Store.put('monad', [d]);
    const consumer = { hash: Store.put('loli', [c, bodyC]) };

    const result = fuseLinearPair(producer, consumer, 'nonexistent', rc, null);
    assert.equal(result, null);
  });

  it('returns null when unification fails between cut formulas', () => {
    const x = Store.put('atom', ['x_val']);
    const y = Store.put('atom', ['y_val']);
    const a = Store.put('gas', [Store.put('atom', ['a'])]);

    const pAnte = a;
    const pConseq = Store.put('pc', [x]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [pConseq])]) };

    const cAnte = Store.put('pc', [y]);
    const cConseq = Store.put('gas', [Store.put('atom', ['z'])]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]) };

    // x_val !== y_val → unification fails
    const result = fuseLinearPair(producer, consumer, 'pc', rc, null);
    assert.equal(result, null);
  });

  it('fuses when cut predicate unifies via metavar', () => {
    const a = Store.put('atom', ['a']);
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);

    const pAnte = Store.put('gas', [a]);
    const pConseq = Store.put('pc', [mvX]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [pConseq])]) };

    const cAnte = Store.put('pc', [mvY]);
    const cConseq = Store.put('stack', [mvY]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]) };

    const result = fuseLinearPair(producer, consumer, 'pc', rc, null);
    assert.ok(result, 'should fuse via metavar unification');
    assert.ok(result.hash, 'fused rule should have a hash');
  });

  it('opens exists in producer consequent during fusion', () => {
    // Producer: gas(a) -o { exists X. pc(X) }
    const a = Store.put('atom', ['a']);
    const b0 = Store.put('bound', [0n]);
    const pAnte = Store.put('gas', [a]);
    const pcBound = Store.put('pc', [b0]);
    const exPc = Store.put('exists', [pcBound]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [exPc])]) };

    // Consumer: pc(M) -o { stack(M) }
    const mvM = Store.put('metavar', ['M']);
    const cAnte = Store.put('pc', [mvM]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]) };

    // Without exists opening, cut on 'pc' fails (producer consequent is 'exists', not 'pc')
    // With exists opening, bound(0) → fresh metavar, exposing pc(m_fresh) for cut
    const result = fuseLinearPair(producer, consumer, 'pc', rc, null);
    assert.ok(result, 'should fuse: exists opened to expose pc for cut elimination');
    assert.ok(result.hash, 'fused rule should have a hash');
  });

  it('opens nested exists (exists X. exists Y. pc(X, Y))', () => {
    const a = Store.put('atom', ['a']);
    const pAnte = Store.put('gas', [a]);
    // exists X. exists Y. pc(X, Y) — de Bruijn: bound(1)=X, bound(0)=Y inside inner exists
    const b0 = Store.put('bound', [0n]);
    const b1 = Store.put('bound', [1n]);
    const pcXY = Store.put('pc', [b1, b0]);
    const innerExists = Store.put('exists', [pcXY]);
    const outerExists = Store.put('exists', [innerExists]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [outerExists])]) };

    // Consumer: pc(M, N) -o { stack(M) }
    const mvM = Store.put('metavar', ['M2']);
    const mvN = Store.put('metavar', ['N2']);
    const cAnte = Store.put('pc', [mvM, mvN]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]) };

    const result = fuseLinearPair(producer, consumer, 'pc', rc, null);
    assert.ok(result, 'should fuse: nested exists opened recursively');
  });
});
