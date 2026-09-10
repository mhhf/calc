/**
 * Termination analysis (TODO_0009 §6, Inc-6). Sound ranking / dependency-graph
 * analysis over forward multiset-rewriting rules: `terminating` is a proof,
 * everything else is `unknown` (never a false certificate).
 */
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeTermination, tarjanSCC } from '../../lib/engine/termination.js';

const R = (name, consume, produce) => ({ name, consume, produce });

describe('termination — ranking / dependency analysis (Inc-6)', () => {
  it('tarjanSCC finds the strongly-connected components', () => {
    const adj = new Map([['a', ['b']], ['b', ['a', 'c']], ['c', []]]);
    const sccs = tarjanSCC(['a', 'b', 'c'], adj).map(s => s.sort().join(''));
    assert.ok(sccs.includes('ab'), 'a,b are mutually reachable');
    assert.ok(sccs.includes('c'), 'c is its own SCC');
  });

  it('an acyclic producer chain terminates (a → b → c)', () => {
    const r = analyzeTermination([R('r1', ['a'], ['b']), R('r2', ['b'], ['c'])]);
    assert.equal(r.result, 'terminating');
    assert.equal(r.witness.kind, 'acyclic');
  });

  it('request-bounded transfer terminates (ranking on the depleting request)', () => {
    // token,request -o token,token — token cycles, but each fire consumes one
    // request and none is produced, so the request count strictly decreases.
    const r = analyzeTermination([R('transfer', ['token', 'request'], ['token', 'token'])]);
    assert.equal(r.result, 'terminating');
    assert.equal(r.witness.kind, 'ranking');
    assert.deepEqual(r.witness.ranking, { kind: 'single', pred: 'request' });
  });

  it('a net-decreasing rule terminates (p*p -o p)', () => {
    const r = analyzeTermination([R('merge', ['p', 'p'], ['p'])]);
    assert.equal(r.result, 'terminating');   // δ[p] = 1 − 2 = −1
  });

  it('a self-sustaining rule is unknown (p -o p*p)', () => {
    const r = analyzeTermination([R('split', ['p'], ['p', 'p'])]);
    assert.equal(r.result, 'unknown', 'produces more than it consumes — no ranking');
  });

  it('an idle loop is unknown (p -o p)', () => {
    assert.equal(analyzeTermination([R('idle', ['p'], ['p'])]).result, 'unknown');
  });

  it('a genuinely non-terminating swap is unknown (a -o b, b -o a)', () => {
    // a→b→a forever; no single weight decreases both rules → unknown (sound: we
    // never CLAIM termination for a program that loops).
    const r = analyzeTermination([R('r1', ['a'], ['b']), R('r2', ['b'], ['a'])]);
    assert.equal(r.result, 'unknown');
  });

  it('KNOWN LIMITATION: value-based termination (gas) is unknown (count abstraction)', () => {
    // gas(N) -o gas(N−k) is `gas -o gas` at the predicate-count level: the count
    // is unchanged, so the ranking cannot see the decreasing argument.
    assert.equal(analyzeTermination([R('step', ['gas'], ['gas'])]).result, 'unknown');
  });

  it('reports the dependency SCCs for inspection', () => {
    const r = analyzeTermination([R('transfer', ['token', 'request'], ['token', 'token'])]);
    const tokenScc = r.sccs.find(s => s.preds.includes('token'));
    assert.equal(tokenScc.cyclic, true, 'token consumes+produces itself → cyclic');
    const reqScc = r.sccs.find(s => s.preds.includes('request'));
    assert.equal(reqScc.cyclic, false, 'request is never produced → acyclic');
  });
});
