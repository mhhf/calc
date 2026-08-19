/**
 * Multi-logic tests: connective roles, graceful degradation, coexistence.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import calculus from '../lib/calculus/index.js';
import Store from '../lib/kernel/store.js';
import { illConnectives } from '../lib/engine/ill/connectives.js';
// Hoisted by tools/esm-hoist.js:
import { rightFocus } from '../lib/prover/bridge.js';

describe('deriveRoles', () => {
  let ill;

  before(() => {
    calculus.clearCache();
    ill = calculus.loadILL();
  });

  it('should derive all ILL roles', () => {
    const r = ill.roles;
    assert.strictEqual(r.product, 'tensor');
    assert.strictEqual(r.implication, 'loli');
    assert.strictEqual(r.unit, 'one');
    assert.strictEqual(r.internalChoice, 'oplus');
    assert.strictEqual(r.externalChoice, 'with');
    assert.strictEqual(r.exponential, 'bang');
    assert.deepStrictEqual(r.computation, { tag: 'monad', bodyIdx: 0, gradeIdx: null });
    assert.strictEqual(r.existential, 'exists');
    assert.strictEqual(r.additiveZero, 'zero');
  });

  it('should have illConnectives() as tag → structural info table (derived from ill.calc)', () => {
    assert.deepStrictEqual(illConnectives().tensor, { category: 'multiplicative', arity: 2, polarity: 'positive' });
    assert.deepStrictEqual(illConnectives().loli, { category: 'multiplicative', arity: 2, polarity: 'negative' });
    assert.deepStrictEqual(illConnectives().bang, { category: 'exponential', arity: 2 });
    assert.deepStrictEqual(illConnectives().monad, { category: 'monad', arity: 1, polarity: 'negative' });
    assert.deepStrictEqual(illConnectives().oplus, { category: 'additive', arity: 2, polarity: 'positive' });
    assert.deepStrictEqual(illConnectives().with, { category: 'additive', arity: 2, polarity: 'negative' });
    assert.deepStrictEqual(illConnectives().exists, { category: 'quantifier', arity: 1, polarity: 'positive' });
    assert.deepStrictEqual(illConnectives().forall, { category: 'quantifier', arity: 1 });
    assert.deepStrictEqual(illConnectives().one, { category: 'multiplicative', arity: 0 });
    assert.deepStrictEqual(illConnectives().zero, { category: 'additive', arity: 0, polarity: 'positive' });
  });
});

describe('minimal-prop calculus (graceful degradation)', () => {
  let prop;

  before(() => {
    calculus.clearCache();
    prop = calculus.load(
      path.join(import.meta.dirname, 'fixtures/minimal-prop.calc')
    );
  });

  it('should derive product and unit roles only', () => {
    assert.strictEqual(prop.roles.product, 'prop_and');
    assert.strictEqual(prop.roles.unit, 'prop_true');
  });

  it('should NOT have monad/exponential/implication roles', () => {
    assert.strictEqual(prop.roles.computation, undefined);
    assert.strictEqual(prop.roles.exponential, undefined);
    assert.strictEqual(prop.roles.implication, undefined);
    assert.strictEqual(prop.roles.internalChoice, undefined);
    assert.strictEqual(prop.roles.externalChoice, undefined);
  });

  it('should not inject monad rules', () => {
    const monadRules = Object.keys(prop.rules).filter(n => n.startsWith('monad'));
    assert.strictEqual(monadRules.length, 0);
  });

});

describe('two calculi coexist', () => {
  let ill, prop;

  before(() => {
    calculus.clearCache();
    // Load both — they share the same Store
    ill = calculus.loadILL();
    prop = calculus.load(
      path.join(import.meta.dirname, 'fixtures/minimal-prop.calc')
    );
  });

  it('should have independent roles', () => {
    assert.strictEqual(ill.roles.product, 'tensor');
    assert.strictEqual(prop.roles.product, 'prop_and');
    assert.deepStrictEqual(ill.roles.computation, { tag: 'monad', bodyIdx: 0, gradeIdx: null });
    assert.strictEqual(prop.roles.computation, undefined);
  });

  it('should have independent rules', () => {
    assert.ok(Object.keys(ill.rules).length > Object.keys(prop.rules).length);
    assert.ok(ill.rules.tensor_r, 'ILL should have tensor_r');
    assert.strictEqual(prop.rules.tensor_r, undefined, 'prop should not have tensor_r');
  });

  it('should share Store for same-structure terms', () => {
    // Both calculi use 'atom' constructor — shared hashes
    const h1 = ill.AST.atom('p');
    const h2 = prop.AST.atom('p');
    assert.strictEqual(h1, h2, 'same atom in both calculi should share hash');
  });
});

describe('rightFocus with roles', () => {

  it('should decompose product with ILL roles', () => {
    const ill = calculus.loadILL();
    const a = Store.put('atom', ['p']);
    const b = Store.put('atom', ['q']);
    const t = Store.put('tensor', [a, b]);
    const linear = { [a]: 1, [b]: 1 };
    const result = rightFocus(linear, {}, t, ill.roles);
    assert.ok(result !== null);
  });

  it('should decompose unit with ILL roles', () => {
    const ill = calculus.loadILL();
    const one = Store.put('one', []);
    const result = rightFocus({}, {}, one, ill.roles);
    assert.ok(result !== null);
  });

  it('should reject known connectives in async position', () => {
    const ill = calculus.loadILL();
    const a = Store.put('atom', ['p']);
    const l = Store.put('loli', [a, a]);
    const result = rightFocus({ [a]: 1 }, {}, l, ill.roles);
    assert.strictEqual(result, null);
  });

  it('should work with empty roles (backward compat)', () => {
    const a = Store.put('atom', ['p']);
    // With empty roles, no connective matches → falls through to atom consumption
    const result = rightFocus({ [a]: 1 }, {}, a, {});
    assert.ok(result !== null);
  });
});
