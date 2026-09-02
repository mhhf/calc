/**
 * Direct tests for compose.js:fusePair
 *
 * Covers: exists opening, predicate matching, unification failure handling.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import { fusePair } from '../../lib/engine/compose.js';
import { resolveConn } from '../../lib/engine/compile.js';
// Hoisted by tools/esm-hoist.js:
import mde from '../../calculus/ill/index.js';
import ccfg from '../../calculus/ill/calculus-config.js';
import { monadUnit as U } from '../../lib/engine/grades.js';

describe('fusePair', () => {
  let rc;

  before(() => {
    Store.clear();

    mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });

    rc = resolveConn(ccfg.connectives);
  });

  it('returns null when cut predicate not found in producer consequent', () => {
    const a = Store.put('gas', [Store.put('atom', ['x'])]);
    const b = Store.put('pc', [Store.put('atom', ['y'])]);
    const bodyP = Store.put('monad', [U(), b]);
    const producer = { hash: Store.put('loli', [a, bodyP]) };

    const c = Store.put('stack', [Store.put('atom', ['z'])]);
    const d = Store.put('mem', [Store.put('atom', ['w'])]);
    const bodyC = Store.put('monad', [U(), d]);
    const consumer = { hash: Store.put('loli', [c, bodyC]) };

    const result = fusePair(producer, consumer, 'nonexistent', rc, null);
    assert.equal(result, null);
  });

  it('returns null when unification fails between cut formulas', () => {
    const x = Store.put('atom', ['x_val']);
    const y = Store.put('atom', ['y_val']);
    const a = Store.put('gas', [Store.put('atom', ['a'])]);

    const pAnte = a;
    const pConseq = Store.put('pc', [x]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [U(), pConseq])]) };

    const cAnte = Store.put('pc', [y]);
    const cConseq = Store.put('gas', [Store.put('atom', ['z'])]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [U(), cConseq])]) };

    // x_val !== y_val → unification fails
    const result = fusePair(producer, consumer, 'pc', rc, null);
    assert.equal(result, null);
  });

  it('fuses when cut predicate unifies via metavar', () => {
    const a = Store.put('atom', ['a']);
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);

    const pAnte = Store.put('gas', [a]);
    const pConseq = Store.put('pc', [mvX]);
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [U(), pConseq])]) };

    const cAnte = Store.put('pc', [mvY]);
    const cConseq = Store.put('stack', [mvY]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [U(), cConseq])]) };

    const result = fusePair(producer, consumer, 'pc', rc, null);
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
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [U(), exPc])]) };

    // Consumer: pc(M) -o { stack(M) }
    const mvM = Store.put('metavar', ['M']);
    const cAnte = Store.put('pc', [mvM]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [U(), cConseq])]) };

    // Without exists opening, cut on 'pc' fails (producer consequent is 'exists', not 'pc')
    // With exists opening, bound(0) → fresh metavar, exposing pc(m_fresh) for cut
    const result = fusePair(producer, consumer, 'pc', rc, null);
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
    const producer = { hash: Store.put('loli', [pAnte, Store.put('monad', [U(), outerExists])]) };

    // Consumer: pc(M, N) -o { stack(M) }
    const mvM = Store.put('metavar', ['M2']);
    const mvN = Store.put('metavar', ['N2']);
    const cAnte = Store.put('pc', [mvM, mvN]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = { hash: Store.put('loli', [cAnte, Store.put('monad', [U(), cConseq])]) };

    const result = fusePair(producer, consumer, 'pc', rc, null);
    assert.ok(result, 'should fuse: nested exists opened recursively');
  });
});
