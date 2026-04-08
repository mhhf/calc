/**
 * Tests for additive chain fusion (_fuseAdditiveChains) and arr_get/arr_set
 * residual resolution.
 *
 * Chain fusion collapses threading patterns like:
 *   checked_sub(G, 3, G2) * checked_sub(G2, 5, G3) → checked_sub(G, 8, G3)
 *   plus(X, 2, X2) * plus(X2, 3, X3) → plus(X, 5, X3)
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, flattenAntecedent } = require('../../lib/engine/compile');
const { getPredicateHead } = require('../../lib/kernel/ast');
const { _fuseAdditiveChains } = require('../../lib/engine/compose');
const { _resolveResidualOnce } = require('../../lib/engine/compose');
const { getModeMeta: _illGetModeMeta } = require('../../lib/engine/opt/ffi');
const { intToBin, binToInt } = require('../../lib/engine/ill/ffi/convert');
const { residualResolver } = require('../../lib/engine/ill/residual-resolver');

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

describe('_fuseAdditiveChains', () => {
  let rc;

  beforeEach(() => {
    Store.clear();
    rc = resolveConnectives(ILL_CONNECTIVES);
  });

  it('fuses a 2-link checked_sub chain', () => {
    const G = mv('G');
    const G2 = mv('G2');
    const G3 = mv('G3');
    const cs1 = Store.put('checked_sub', [G, bin(3), G2]);
    const cs2 = Store.put('checked_sub', [G2, bin(5), G3]);
    const pc_h = Store.put('pc', [bin(10)]);
    // Name must include '+' for fusion to trigger
    const ante = tensor(pc_h, bang(cs1), bang(cs2));
    const conseq = Store.put('pc', [G3]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta);
    assert.equal(result.length, 1);

    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const csGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'checked_sub');
    assert.equal(csGoals.length, 1, 'should fuse 2 checked_sub into 1');

    // Fused constant should be 3 + 5 = 8
    const fused = csGoals[0];
    assert.equal(binToInt(Store.child(fused, 1)), 8n, 'fused constant should be 8');
  });

  it('fuses a 3-link checked_sub chain', () => {
    const G = mv('G');
    const G2 = mv('G2');
    const G3 = mv('G3');
    const G4 = mv('G4');
    const cs1 = Store.put('checked_sub', [G, bin(1), G2]);
    const cs2 = Store.put('checked_sub', [G2, bin(2), G3]);
    const cs3 = Store.put('checked_sub', [G3, bin(3), G4]);
    const pc_h = Store.put('pc', [bin(10)]);
    const ante = tensor(pc_h, bang(cs1), bang(cs2), bang(cs3));
    const conseq = Store.put('pc', [G4]);
    const rule = makeRule('a+b+c', ante, conseq);

    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta);
    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const csGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'checked_sub');
    assert.equal(csGoals.length, 1, 'should fuse 3 checked_sub into 1');
    assert.equal(binToInt(Store.child(csGoals[0], 1)), 6n, 'fused constant should be 6');
  });

  it('fuses a plus chain', () => {
    const X = mv('X');
    const X2 = mv('X2');
    const X3 = mv('X3');
    const p1 = Store.put('plus', [X, bin(2), X2]);
    const p2 = Store.put('plus', [X2, bin(3), X3]);
    const pc_h = Store.put('pc', [bin(10)]);
    const ante = tensor(pc_h, bang(p1), bang(p2));
    const conseq = Store.put('pc', [X3]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta);
    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const plusGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'plus');
    assert.equal(plusGoals.length, 1, 'should fuse 2 plus into 1');
    assert.equal(binToInt(Store.child(plusGoals[0], 1)), 5n, 'fused constant should be 5');
  });

  it('does not fuse when intermediate var is used elsewhere', () => {
    const G = mv('G');
    const G2 = mv('G2');
    const G3 = mv('G3');
    const cs1 = Store.put('checked_sub', [G, bin(3), G2]);
    const cs2 = Store.put('checked_sub', [G2, bin(5), G3]);
    // G2 also appears in the linear antecedent
    const gas_h = Store.put('gas', [G2]);
    const pc_h = Store.put('pc', [bin(10)]);
    const ante = tensor(pc_h, gas_h, bang(cs1), bang(cs2));
    const conseq = Store.put('pc', [G3]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta);
    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const csGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'checked_sub');
    assert.equal(csGoals.length, 2, 'should NOT fuse when intermediate var leaks');
  });

  it('fuses chains regardless of rule name', () => {
    // Chain fusion works on any rule, not just fused rules
    const G = mv('G');
    const G2 = mv('G2');
    const G3 = mv('G3');
    const cs1 = Store.put('checked_sub', [G, bin(3), G2]);
    const cs2 = Store.put('checked_sub', [G2, bin(5), G3]);
    const pc_h = Store.put('pc', [bin(10)]);
    const ante = tensor(pc_h, bang(cs1), bang(cs2));
    const conseq = Store.put('pc', [G3]);
    const rule = makeRule('single_rule', ante, conseq);

    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta);
    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const csGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'checked_sub');
    assert.equal(csGoals.length, 1, 'should fuse even without + in name');
  });

  it('accepts custom chain configs', () => {
    // Custom predicate 'sub' with same structure as checked_sub
    const G = mv('G');
    const G2 = mv('G2');
    const G3 = mv('G3');
    const s1 = Store.put('sub', [G, bin(1), G2]);
    const s2 = Store.put('sub', [G2, bin(2), G3]);
    const pc_h = Store.put('pc', [bin(10)]);
    const ante = tensor(pc_h, bang(s1), bang(s2));
    const conseq = Store.put('pc', [G3]);
    const rule = makeRule('a+b', ante, conseq);

    const customConfig = [{ pred: 'sub', inputArg: 0, outputArg: 2, constantArg: 1, fusedPred: 'sub' }];
    const result = _fuseAdditiveChains([rule], rc, _illGetModeMeta, customConfig);
    const newAnte = flattenAntecedent(Store.child(result[0].hash, 0), rc);
    const subGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'sub');
    assert.equal(subGoals.length, 1, 'should fuse custom predicate chain');
    assert.equal(binToInt(Store.child(subGoals[0], 1)), 3n, 'fused constant should be 3');
  });
});

describe('arr_get residual resolution', () => {
  let rc;

  beforeEach(() => {
    Store.clear();
    rc = resolveConnectives(ILL_CONNECTIVES);
  });

  it('resolves arr_get on ground arrlit with ground index', () => {
    // Create a small array [0x60, 0x80, 0x40]
    const elems = new Uint32Array([bin(0x60), bin(0x80), bin(0x40)]);
    const arrHash = Store.put('arrlit', [elems]);
    const idx = bin(1);
    const V = mv('V');
    const arrGet = Store.put('arr_get', [arrHash, idx, V]);
    const pc_h = Store.put('pc', [bin(0)]);
    const ante = tensor(pc_h, bang(arrGet));
    const conseq = Store.put('pc', [V]);
    const rule = makeRule('test', ante, conseq);

    const result = _resolveResidualOnce(rule, rc, _illGetModeMeta, residualResolver);
    assert.notEqual(result.hash, rule.hash, 'rule should be changed');

    const newAnte = flattenAntecedent(Store.child(result.hash, 0), rc);
    const arrGetGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'arr_get');
    assert.equal(arrGetGoals.length, 0, 'arr_get goal should be resolved');

    // Consequent pc should have the value at index 1 = 0x80
    const conseqBody = Store.child(Store.child(result.hash, 1), 0);
    const newConseq = flattenAntecedent(conseqBody, rc);
    const pcOut = newConseq.linear.find(h => getPredicateHead(h) === 'pc');
    assert.ok(pcOut);
    assert.equal(Store.child(pcOut, 0), bin(0x80), 'pc should have value 0x80');
  });

  it('does not resolve arr_get with non-ground array', () => {
    const arrVar = mv('ARR');
    const idx = bin(0);
    const V = mv('V');
    const arrGet = Store.put('arr_get', [arrVar, idx, V]);
    const pc_h = Store.put('pc', [bin(0)]);
    const ante = tensor(pc_h, bang(arrGet));
    const conseq = Store.put('pc', [V]);
    const rule = makeRule('test', ante, conseq);

    const result = _resolveResidualOnce(rule, rc, _illGetModeMeta, residualResolver);
    assert.equal(result, rule, 'rule should not be changed');
  });

  it('does not resolve arr_get with non-ground index', () => {
    const elems = new Uint32Array([bin(0x60), bin(0x80)]);
    const arrHash = Store.put('arrlit', [elems]);
    const I = mv('I');
    const V = mv('V');
    const arrGet = Store.put('arr_get', [arrHash, I, V]);
    const pc_h = Store.put('pc', [bin(0)]);
    const ante = tensor(pc_h, bang(arrGet));
    const conseq = Store.put('pc', [V]);
    const rule = makeRule('test', ante, conseq);

    const result = _resolveResidualOnce(rule, rc, _illGetModeMeta, residualResolver);
    assert.equal(result, rule, 'rule should not be changed');
  });

  it('resolves arr_set on ground arrlit', () => {
    const v0 = bin(0x60);
    const v1 = bin(0x80);
    const elems = new Uint32Array([v0, v1]);
    const arrHash = Store.put('arrlit', [elems]);
    const idx = bin(0);
    const newVal = bin(0xFF);
    const Result = mv('R');
    const arrSet = Store.put('arr_set', [arrHash, idx, newVal, Result]);
    const pc_h = Store.put('pc', [bin(0)]);
    const ante = tensor(pc_h, bang(arrSet));
    const conseq = Store.put('stack', [Result]);
    const rule = makeRule('test', ante, conseq);

    const result = _resolveResidualOnce(rule, rc, _illGetModeMeta, residualResolver);
    assert.notEqual(result.hash, rule.hash, 'rule should be changed');

    const newAnte = flattenAntecedent(Store.child(result.hash, 0), rc);
    const arrSetGoals = newAnte.persistent.filter(h => getPredicateHead(h) === 'arr_set');
    assert.equal(arrSetGoals.length, 0, 'arr_set goal should be resolved');

    // Result should be an arrlit with [0xFF, 0x80]
    const conseqBody = Store.child(Store.child(result.hash, 1), 0);
    const newConseq = flattenAntecedent(conseqBody, rc);
    const stackOut = newConseq.linear.find(h => getPredicateHead(h) === 'stack');
    assert.ok(stackOut);
    const resultArr = Store.child(stackOut, 0);
    const resultElems = Store.getArrayElements(resultArr);
    assert.ok(resultElems, 'result should be an arrlit');
    assert.equal(resultElems.length, 2);
    assert.equal(resultElems[0], newVal, 'index 0 should be updated to 0xFF');
    assert.equal(resultElems[1], v1, 'index 1 should be unchanged');
  });
});

describe('residualResolver coverage', () => {
  beforeEach(() => Store.clear());

  it('resolves checked_sub with ground args', () => {
    const X = mv('X');
    const result = residualResolver(Store.put('checked_sub', [bin(10), bin(3), X]));
    assert.ok(result);
    assert.equal(binToInt(Store.child(result, 2)), 7n);
  });

  it('rejects checked_sub with underflow', () => {
    const X = mv('X');
    const result = residualResolver(Store.put('checked_sub', [bin(3), bin(10), X]));
    assert.equal(result, null, 'underflow should return null');
  });

  it('resolves gt with ground args', () => {
    const X = mv('X');
    const result = residualResolver(Store.put('gt', [bin(5), bin(3), bin(0), X]));
    assert.ok(result);
    assert.equal(binToInt(Store.child(result, 3)), 1n, '5 > 3 → 1');
  });

  it('resolves div and mod with ground args', () => {
    const X = mv('X');
    const divResult = residualResolver(Store.put('div', [bin(10), bin(3), X]));
    assert.ok(divResult);
    assert.equal(binToInt(Store.child(divResult, 2)), 3n);

    const modResult = residualResolver(Store.put('mod', [bin(10), bin(3), X]));
    assert.ok(modResult);
    assert.equal(binToInt(Store.child(modResult, 2)), 1n);
  });

  it('resolves add_mod and mul_mod', () => {
    const X = mv('X');
    const addMod = residualResolver(Store.put('add_mod', [bin(7), bin(5), bin(3), X]));
    assert.ok(addMod);
    assert.equal(binToInt(Store.child(addMod, 3)), 0n, '(7+5) % 3 = 0');

    const mulMod = residualResolver(Store.put('mul_mod', [bin(7), bin(5), bin(3), X]));
    assert.ok(mulMod);
    assert.equal(binToInt(Store.child(mulMod, 3)), 2n, '(7*5) % 3 = 2');
  });

  it('resolves arr_get on arrlit', () => {
    const V = mv('V');
    const elems = new Uint32Array([bin(100), bin(200), bin(300)]);
    const arr = Store.put('arrlit', [elems]);
    const result = residualResolver(Store.put('arr_get', [arr, bin(2), V]));
    assert.ok(result);
    assert.equal(Store.child(result, 2), bin(300));
  });

  it('rejects arr_get out of bounds', () => {
    const V = mv('V');
    const elems = new Uint32Array([bin(100)]);
    const arr = Store.put('arrlit', [elems]);
    const result = residualResolver(Store.put('arr_get', [arr, bin(5), V]));
    assert.equal(result, null);
  });
});
