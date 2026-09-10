/**
 * Coinductive logic programming in the SLD backchainer (TODO_0009 Inc-5b).
 *
 * The complement of rung-1's inductive fail-on-loop: `opts.coindPreds` (a Set of
 * predicate-head names declared coinductive) makes a goal that recurs
 * IDENTICALLY on its path SUCCEED — witnessing membership in the greatest fixed
 * point (Simon–Gupta co-LP, sound over the persistent SLD fragment: no linear
 * resource crosses the back-edge). Guarded against the mixed inductive/
 * coinductive hazard: coinductive success requires the WHOLE cycle
 * (companion→bud) to stay within coinductive predicates — a cycle touching an
 * inductive predicate has no such justification and fails.
 *
 * Pins: (1) a bare coinductive loop succeeds, and only when declared; (2) an
 * infinite graph path is proven coinductively (a meaningful ν-property); (3) the
 * mixed-cycle guard rejects a cycle through an inductive predicate; (4) it never
 * proves a genuinely-false goal; (5) rung-1 inductive behaviour is preserved.
 */
import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import backward from '../../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../../calculus/ill/lib/backchain-ill.js';

beforeEach(() => { Store.clear(); });
const A = (s) => Store.put('atom', [s]);
const MV = (s) => Store.put('metavar', [s]);
const prove = (goal, clauses, types, opts) =>
  backward.prove(goal, clauses, types, { ...makeILLBackchainOpts(), ...opts });

describe('backchain co-LP — coinductive success (Inc-5b)', () => {
  it('a bare coinductive loop p <- p succeeds only when p is declared coinductive', () => {
    const p = A('p');
    const clauses = new Map([['loop', { hash: p, premises: [p] }]]);
    const types = new Map();
    // no loop handling → grinds to maxDepth and fails
    assert.equal(prove(p, clauses, types, { maxDepth: 3000 }).success, false);
    // rung-1 inductive: loop = fail
    assert.equal(prove(p, clauses, types, { loopCheck: true }).success, false);
    // co-LP: p coinductive → the loop is success (p ∈ gfp)
    assert.equal(prove(p, clauses, types, { coindPreds: new Set(['p']) }).success, true);
  });

  it('proves an infinite graph path coinductively (a meaningful ν-property)', () => {
    // edge(a,b), edge(b,a).  path(X) <- edge(X,Y), path(Y).
    // path(a) has an infinite walk a→b→a→… ⇒ coinductively provable.
    const a = A('a'), b = A('b'), X = MV('X'), Y = MV('Y');
    const path = (x) => Store.put('path', [x]);
    const edge = (x, y) => Store.put('edge', [x, y]);
    const clauses = new Map([['path/r', { hash: path(X), premises: [edge(X, Y), path(Y)] }]]);
    const types = new Map([['e1', edge(a, b)], ['e2', edge(b, a)]]);

    assert.equal(prove(path(a), clauses, types, { coindPreds: new Set(['path']), maxDepth: 5000 }).success, true,
      'the infinite path is a coinductive success');
    // rung-1 (inductive) refuses it (no finite path)
    assert.equal(prove(path(a), clauses, types, { loopCheck: true, maxDepth: 5000 }).success, false);
  });

  it('MIXED-CYCLE GUARD: a cycle through an inductive predicate is refused', () => {
    // a <- b, b <- a. Declare only `a` coinductive; the a→b→a cycle passes
    // through inductive `b`, so co-LP must NOT succeed.
    const a = A('a'), b = A('b');
    const clauses = new Map([
      ['ra', { hash: a, premises: [b] }],
      ['rb', { hash: b, premises: [a] }],
    ]);
    assert.equal(prove(a, clauses, new Map(), { coindPreds: new Set(['a']), maxDepth: 3000 }).success, false,
      'mixed inductive/coinductive cycle is unsound to accept → refused');
    // both coinductive ⇒ the cycle is entirely coinductive ⇒ success
    assert.equal(prove(a, clauses, new Map(), { coindPreds: new Set(['a', 'b']), maxDepth: 3000 }).success, true);
  });

  it('never proves a genuinely-false coinductive goal (no loop, no base case)', () => {
    // q coinductive but with a clause that recurses on a DISTINCT goal that
    // itself has no base and no loop → fails (no gfp witness).
    const q = (x) => Store.put('q', [x]);
    const s = (x) => Store.put('s', [x]);
    const N = MV('N');
    const clauses = new Map([['q/s', { hash: q(N), premises: [q(s(N))] }]]);  // q(N) <- q(s(N)) — strictly grows, never recurs
    assert.equal(prove(q(A('z')), clauses, new Map(), { coindPreds: new Set(['q']), maxDepth: 2000 }).success, false);
  });

  it('finite/inductive proofs are unaffected by coindPreds on unrelated predicates', () => {
    // nat(e). nat(s N) <- nat N.  A finite derivation must still succeed with a
    // coindPreds set naming an unrelated predicate.
    const e = A('e'); const s = (x) => Store.put('s', [x]); const nat = (x) => Store.put('nat', [x]);
    const N = MV('N');
    const types = new Map([['nat/z', nat(e)]]);
    const clauses = new Map([['nat/s', { hash: nat(s(N)), premises: [nat(N)] }]]);
    const goal = nat(s(s(e)));
    assert.equal(prove(goal, clauses, types, {}).success, true);
    assert.equal(prove(goal, clauses, types, { coindPreds: new Set(['stream']) }).success, true);
  });
});
