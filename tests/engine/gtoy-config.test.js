/**
 * Toy non-ILL calculusConfig through the FULL load path — TODO_0265
 * Phase 3 acceptance (P6): B5 threading, B3 compile opts, B6 forward
 * cross-tag matching, B7 roles on the engine calc + bridge modeSwitch.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import mde from '../../lib/engine/index.js';
import forward from '../../lib/engine/forward.js';
import { modeSwitch } from '../../lib/prover/bridge.js';
import { setTheories } from '../../lib/kernel/unify.js';
import { defaultTheories } from '../../lib/kernel/eq-theory.js';
import { binlitTheory } from '../../lib/engine/ill/binlit-theory.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { gtoyConfig, gtoyGradeUnit } from '../fixtures/gtoy-config.js';

const RULES = path.join(import.meta.dirname, '../fixtures/gtoy-rules.ill');

const atom = (n) => Store.put('atom', [n]);
const mv = (n) => Store.put('metavar', [n]);
const bin = (n) => Store.put('binlit', [n]);

describe('gtoy config through mde.load (P6)', () => {
  let calc;
  before(() => {
    calc = mde.load(RULES, { cache: false, calculusConfig: gtoyConfig });
  });

  it('B5/B7: the engine calc carries the toy roles (not ILL fallback)', () => {
    assert.deepEqual(calc.roles.computation,
      { tag: 'gmonad', bodyIdx: 1, gradeIdx: 0 });
    assert.equal(calc.roles.product, 'tensor');
    assert.equal(calc.roles.exponential, 'bang');
  });

  it('B5: rules are parsed by the toy loader and compiled under the toy connectives', () => {
    assert.equal(calc.forwardRules.length, 2);
    const sell = calc.forwardRules.find(r => r.name === 'sell');
    // consequent unwrapped through gmonad's bodyIdx (grade = unit rational)
    assert.deepEqual(sell.consequent.linear, [Store.put('sold', [mv('N'), mv('D')])]);
    // antecedent pattern kept the structural rat(N, D) form
    assert.deepEqual(sell.antecedent.linear,
      [Store.put('price', [Store.put('rat', [mv('N'), mv('D')])])]);
  });

  it('B6: a compact-ratlit fact fires the rat(N,D)-headed rule ONLY with ratlitTheory installed', () => {
    const fact = Store.put('price', [putRat(1n, 2n)]);

    // Without ratlitTheory in the global set: no cross-tag match, no fire.
    setTheories([...defaultTheories, binlitTheory]);
    const cold = calc.exec(forward.createState({ [fact]: 1 }, {}), { maxSteps: 5 });
    assert.equal(cold.steps, 0, 'must NOT fire without the theory (B6 regression shape)');

    // With the toy init (defaultTheories + binlit + ratlit): fires and binds.
    gtoyConfig.init();
    const hot = calc.exec(forward.createState({ [fact]: 1 }, {}), { maxSteps: 5 });
    assert.equal(hot.steps, 1, 'fires via ratlit ↔ rat(N,D) rewrite');
    assert.equal(hot.state.linear[Store.put('sold', [bin(1n), bin(2n)])], 1);
  });

  it('B7: bridge modeSwitch reads the graded bodyIdx (gmonad_r)', () => {
    const goal = Store.put('gmonad', [gtoyGradeUnit(), atom('c')]);
    const seq = Seq.fromArrays([atom('a'), atom('b')], [], goal);
    const result = modeSwitch(seq, calc);
    assert.ok(result, 'modeSwitch verifies against the BODY child (idx 1), not the grade');
    assert.equal(result.proofNode.rule, 'gmonad_r');
    assert.equal(result.proofNode.proven, true);
  });
});
