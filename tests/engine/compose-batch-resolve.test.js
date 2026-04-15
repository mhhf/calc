/**
 * Tests for batch residual resolution (_resolveOnce / _resolveBatch).
 *
 * Resolves ground persistent goals at compile time in a single pass per rule,
 * with running theta composition for transitive dependencies.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConn, flattenAnte } = require('../../lib/engine/compile');
const { predHead } = require('../../lib/kernel/ast');
const { _resolveOnce, _resolveBatch } = require('../../lib/engine/compose');
const { getModeMeta: _illGetModeMeta } = require('../../lib/engine/opt/ffi');
const { intToBin, binToInt } = require('../../lib/engine/ill/ffi/convert');

function makeRule(name, anteHash, conseqBodyHash) {
  const conseqHash = Store.put('monad', [conseqBodyHash]);
  const hash = Store.put('loli', [anteHash, conseqHash]);
  return { name, hash, antecedent: anteHash, consequent: conseqHash };
}

function tensor(...hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

function bang(h) { return Store.put('bang', [GRADE_W, h]); }
function mv(name) { return Store.put('metavar', [name]); }
function bin(n) { return intToBin(BigInt(n)); }

/**
 * Simple resolver: handles inc and plus with ground inputs.
 */
function testResolver(goalHash) {
  const pred = predHead(goalHash);
  if (pred === 'inc' && Store.arity(goalHash) === 2) {
    const input = Store.child(goalHash, 0);
    const v = binToInt(input);
    if (v === null) return null;
    return Store.put('inc', [input, intToBin(v + 1n)]);
  }
  if (pred === 'plus' && Store.arity(goalHash) === 3) {
    const a = binToInt(Store.child(goalHash, 0));
    const b = binToInt(Store.child(goalHash, 1));
    if (a === null || b === null) return null;
    return Store.put('plus', [Store.child(goalHash, 0), Store.child(goalHash, 1), intToBin(a + b)]);
  }
  return null;
}

describe('_resolveOnce', () => {
  let rc;

  beforeEach(() => {
    Store.clear();
    rc = resolveConn(ILL_CONNECTIVES);
  });

  it('resolves single ground inc goal', () => {
    const five = bin(5);
    const Y = mv('Y');
    const inc = Store.put('inc', [five, Y]);
    const pc_h = Store.put('pc', [five]);
    const ante = tensor(pc_h, bang(inc));
    const conseq = Store.put('pc', [Y]);
    const rule = makeRule('test', ante, conseq);

    const result = _resolveOnce(rule, rc, _illGetModeMeta, testResolver);
    assert.notEqual(result.hash, rule.hash, 'rule should be changed');

    const newAnte = flattenAnte(Store.child(result.hash, 0), rc);
    assert.equal(newAnte.persistent.length, 0, 'inc goal should be resolved');

    // Consequent should have pc(6)
    const conseqBody = Store.child(Store.child(result.hash, 1), 0);
    const newConseq = flattenAnte(conseqBody, rc);
    const pcOut = newConseq.linear.find(h => predHead(h) === 'pc');
    assert.ok(pcOut, 'should have pc in consequent');
    assert.equal(binToInt(Store.child(pcOut, 0)), 6n, 'pc should be 6');
  });

  it('handles transitive deps: inc(5,Y) + plus(Y,2,Z)', () => {
    const five = bin(5);
    const Y = mv('Y');
    const Z = mv('Z');
    const inc = Store.put('inc', [five, Y]);
    const plus = Store.put('plus', [Y, bin(2), Z]);
    const pc_h = Store.put('pc', [five]);
    const ante = tensor(pc_h, bang(inc), bang(plus));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-trans', ante, conseq);

    const result = _resolveOnce(rule, rc, _illGetModeMeta, testResolver);
    const newAnte = flattenAnte(Store.child(result.hash, 0), rc);
    assert.equal(newAnte.persistent.length, 0, 'both goals should be resolved');

    // Z = 6 + 2 = 8
    const conseqBody = Store.child(Store.child(result.hash, 1), 0);
    const newConseq = flattenAnte(conseqBody, rc);
    const pcOut = newConseq.linear.find(h => predHead(h) === 'pc');
    assert.equal(binToInt(Store.child(pcOut, 0)), 8n, 'pc should be 8');
  });

  it('resolves inc chain directly: inc(5,Y) + inc(Y,Z)', () => {
    const five = bin(5);
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [five, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    const pc_h = Store.put('pc', [five]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-chain', ante, conseq);

    const result = _resolveOnce(rule, rc, _illGetModeMeta, testResolver);
    const newAnte = flattenAnte(Store.child(result.hash, 0), rc);
    assert.equal(newAnte.persistent.length, 0, 'both inc goals should be resolved');

    // Z = 7
    const conseqBody = Store.child(Store.child(result.hash, 1), 0);
    const newConseq = flattenAnte(conseqBody, rc);
    const pcOut = newConseq.linear.find(h => predHead(h) === 'pc');
    assert.equal(binToInt(Store.child(pcOut, 0)), 7n, 'pc should be 7');
  });

  it('returns rule unchanged when nothing is resolvable', () => {
    const X = mv('X');
    const Y = mv('Y');
    const inc = Store.put('inc', [X, Y]); // non-ground input
    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc));
    const conseq = Store.put('pc', [Y]);
    const rule = makeRule('test-noop', ante, conseq);

    const result = _resolveOnce(rule, rc, _illGetModeMeta, testResolver);
    assert.equal(result, rule, 'should return same object');
  });

  it('does not resolve inc chain when intermediate appears elsewhere', () => {
    const five = bin(5);
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [five, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    // Y appears in linear antecedent — chain should not be resolved via Phase 1
    const gas_h = Store.put('gas', [Y]);
    const pc_h = Store.put('pc', [five]);
    const ante = tensor(pc_h, gas_h, bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-unsafe', ante, conseq);

    const result = _resolveOnce(rule, rc, _illGetModeMeta, testResolver);
    // Phase 2 should still resolve inc(5,Y) since it's ground
    const newAnte = flattenAnte(Store.child(result.hash, 0), rc);
    const incGoals = newAnte.persistent.filter(h => predHead(h) === 'inc');
    // First inc is resolvable (ground), second becomes resolvable transitively
    assert.equal(incGoals.length, 0, 'both incs should be resolved via phase 2');

    // gas(Y) should become gas(6)
    const gasOut = newAnte.linear.find(h => predHead(h) === 'gas');
    assert.ok(gasOut, 'gas should still be present');
    assert.equal(binToInt(Store.child(gasOut, 0)), 6n, 'gas arg should be 6');
  });
});

describe('_resolveBatch', () => {
  let rc;

  beforeEach(() => {
    Store.clear();
    rc = resolveConn(ILL_CONNECTIVES);
  });

  it('resolves across a pool of rules', () => {
    const rules = [];
    for (let i = 0; i < 3; i++) {
      const v = bin(i * 10);
      const Y = mv(`Y${i}`);
      const inc = Store.put('inc', [v, Y]);
      const pc_h = Store.put('pc', [v]);
      const ante = tensor(pc_h, bang(inc));
      const conseq = Store.put('pc', [Y]);
      rules.push(makeRule(`rule-${i}`, ante, conseq));
    }

    const results = _resolveBatch(rules, rc, _illGetModeMeta, testResolver);
    assert.equal(results.length, 3);

    for (let i = 0; i < 3; i++) {
      const newAnte = flattenAnte(Store.child(results[i].hash, 0), rc);
      assert.equal(newAnte.persistent.length, 0, `rule ${i} should have all goals resolved`);
    }
  });
});
