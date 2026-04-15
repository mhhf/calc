/**
 * Tests for persistent inc chain fusion (Pass 3.5).
 *
 * Fuses !inc(X,Y) * !inc(Y,Z) → !plus(X, 2, Z) at compile time.
 * This is algebraic simplification on persistent goals — no grounding required.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConn, compileRule, flattenAnte } = require('../../lib/engine/compile');
const { predHead } = require('../../lib/kernel/ast');
const { _fuseChains } = require('../../lib/engine/compose');
const { ILL_CHAIN_CONFIGS } = require('../../lib/engine/ill/compose-config');
const { getModes, getModeMeta: _illGetModeMeta } = require('../../lib/engine/ill/ffi');
const { show } = require('../../lib/engine/show');

const COMPILE_OPTS = { connectives: ILL_CONNECTIVES, getModes };

/**
 * Helper: build a raw forward rule from Store hashes.
 */
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

function bang(h) {
  return Store.put('bang', [GRADE_W, h]);
}

function mv(name) {
  return Store.put('metavar', [name]);
}

function binlit(n) {
  return Store.put('binlit', [BigInt(n)]);
}

describe('_fuseChains (inc-only)', () => {
  let rc;

  beforeEach(() => {
    Store.clear();
    rc = resolveConn(ILL_CONNECTIVES);
  });

  it('fuses 2-inc chain: !inc(X,Y) * !inc(Y,Z) → !plus(X, 2, Z)', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const pc_h = Store.put('pc', [X]);
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);

    const ante = tensor(pc_h, bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-2chain', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    // Check the fused rule has !plus(X, 2, Z) instead of !inc(X,Y) * !inc(Y,Z)
    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(plusGoals.length, 1, 'should have one plus goal');
    assert.equal(incGoals.length, 0, 'should have no inc goals');

    // Check plus(X, 2, Z)
    const plus = plusGoals[0];
    assert.equal(Store.arity(plus), 3);
    assert.equal(Store.child(plus, 0), X, 'plus input should be X');
    assert.equal(Store.child(Store.child(plus, 1), 0), 2n, 'plus step should be 2');
    assert.equal(Store.child(plus, 2), Z, 'plus output should be Z');
  });

  it('fuses 3-inc chain: !inc(X,Y) * !inc(Y,Z) * !inc(Z,W) → !plus(X, 3, W)', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const W = mv('W');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    const inc3 = Store.put('inc', [Z, W]);

    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2), bang(inc3));
    const conseq = Store.put('pc', [W]);
    const rule = makeRule('test-3chain', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(plusGoals.length, 1);
    assert.equal(incGoals.length, 0);

    const plus = plusGoals[0];
    assert.equal(Store.child(plus, 0), X);
    assert.equal(Store.child(Store.child(plus, 1), 0), 3n, 'plus step should be 3');
    assert.equal(Store.child(plus, 2), W);
  });

  it('leaves single inc untouched (no chain)', () => {
    const X = mv('X');
    const Y = mv('Y');
    const inc1 = Store.put('inc', [X, Y]);

    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc1));
    const conseq = Store.put('pc', [Y]);
    const rule = makeRule('test-single', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');

    assert.equal(incGoals.length, 1, 'single inc should be preserved');
    assert.equal(plusGoals.length, 0, 'no plus should be created');
  });

  it('does not fuse when intermediate var appears in linear antecedent', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);

    // Y appears in linear antecedent (gas(Y)) — cannot eliminate
    const pc_h = Store.put('pc', [X]);
    const gas_h = Store.put('gas', [Y]);
    const ante = tensor(pc_h, gas_h, bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-unsafe-linear', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    // Should still have inc goals — not fused
    assert.equal(incGoals.length, 2, 'inc goals should be preserved when intermediate is used');
  });

  it('does not fuse when intermediate var appears in consequent', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);

    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2));
    // Y appears in consequent — cannot eliminate
    const conseq = tensor(Store.put('pc', [Z]), Store.put('gas', [Y]));
    const rule = makeRule('test-unsafe-conseq', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(incGoals.length, 2, 'inc goals should be preserved when intermediate is in consequent');
  });

  it('handles mixed: fuseable chain + standalone inc', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const A = mv('A');
    const B = mv('B');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    const inc3 = Store.put('inc', [A, B]); // standalone, different chain

    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2), bang(inc3));
    const conseq = tensor(Store.put('pc', [Z]), Store.put('gas', [B]));
    const rule = makeRule('test-mixed', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(plusGoals.length, 1, 'chain of 2 should become plus');
    assert.equal(incGoals.length, 1, 'standalone inc should remain');
  });

  it('fuses ground chain: !inc(0x5, Y) * !inc(Y, Z) → !plus(0x5, 2, Z)', () => {
    const five = binlit(5);
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [five, Y]);
    const inc2 = Store.put('inc', [Y, Z]);

    const pc_h = Store.put('pc', [five]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-ground', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');

    assert.equal(plusGoals.length, 1);
    const plus = plusGoals[0];
    assert.equal(Store.child(plus, 0), five, 'plus input should be ground 5');
    assert.equal(Store.child(Store.child(plus, 1), 0), 2n);
  });

  it('does not fuse when intermediate var appears in other persistent goal', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    // Another persistent goal uses Y
    const otherGoal = Store.put('gt', [Y, binlit(10), binlit(0), mv('R')]);

    const pc_h = Store.put('pc', [X]);
    const ante = tensor(pc_h, bang(inc1), bang(inc2), bang(otherGoal));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('test-unsafe-persistent', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(incGoals.length, 2, 'should not fuse when intermediate is used in other persistent goal');
  });

  it('updates rule name to reflect fusion', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);

    const ante = tensor(Store.put('pc', [X]), bang(inc1), bang(inc2));
    const conseq = Store.put('pc', [Z]);
    const rule = makeRule('evm/add', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.ok(result[0].name.includes('inc-fused'), `name should include 'inc-fused', got: ${result[0].name}`);
  });

  it('handles multiple independent chains in one rule', () => {
    const X = mv('X');
    const Y = mv('Y');
    const Z = mv('Z');
    const A = mv('A');
    const B = mv('B');
    const C = mv('C');
    // Chain 1: X→Y→Z
    const inc1 = Store.put('inc', [X, Y]);
    const inc2 = Store.put('inc', [Y, Z]);
    // Chain 2: A→B→C
    const inc3 = Store.put('inc', [A, B]);
    const inc4 = Store.put('inc', [B, C]);

    const ante = tensor(Store.put('pc', [X]), Store.put('gas', [A]),
      bang(inc1), bang(inc2), bang(inc3), bang(inc4));
    const conseq = tensor(Store.put('pc', [Z]), Store.put('gas', [C]));
    const rule = makeRule('test-two-chains', ante, conseq);

    const result = _fuseChains([rule], rc, _illGetModeMeta, [ILL_CHAIN_CONFIGS[0]]);
    assert.equal(result.length, 1);

    const fusedAnte = flattenAnte(Store.child(result[0].hash, 0), rc);
    const plusGoals = fusedAnte.persistent.filter(h => predHead(h) === 'plus');
    const incGoals = fusedAnte.persistent.filter(h => predHead(h) === 'inc');

    assert.equal(plusGoals.length, 2, 'both chains should become plus');
    assert.equal(incGoals.length, 0, 'no inc goals should remain');
  });
});
