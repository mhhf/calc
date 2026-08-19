/**
 * desugarTimed — TODO_0265 Phase 3 (window arithmetic → q-op goals, E7.1).
 *
 * `after (Q+2)` lowers to `after Q$0` plus a persistent `!qplus Q 2 Q$0`
 * goal tensored into the antecedent — arithmetic in grade position is
 * sugar for backward propositions, so no expression evaluator exists.
 * Also pins the timed validation errors.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { desugarTimed, desugarPreserved } from '../../lib/engine/convert.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { gradeW } from '../../lib/engine/grades.js';

const FIXTURE = path.join(import.meta.dirname, '../fixtures/graded-comp.calc');
const CT = {
  computation: { tag: 'gmonad', bodyIdx: 1, gradeIdx: 0 },
  implication: 'loli',
  product: 'tensor',
  exponential: 'bang',
  preserved: 'preserved',
};

const atom = (n) => Store.put('atom', [n]);
const fv = (n) => Store.put('freevar', [n]);
const mvq = (i) => Store.put('metavar', ['Q$' + i]);

describe('desugarTimed', () => {
  let parse;
  before(() => {
    const gt = calculus.load(FIXTURE);
    parse = buildParser(gt.constructors, {
      gradeUnit: () => putRat(0n, 1n),
    });
  });

  it('lowers after (Q+2) to after Q$0 + !qplus Q 2 Q$0', () => {
    const h = parse('food@Q * after (Q+2) -o { b }');
    const out = desugarTimed(h, CT);
    const anteIn = Store.put('tensor', [
      Store.put('at', [atom('food'), fv('Q')]),
      Store.put('after', [mvq(0)]),
    ]);
    const goal = Store.put('bang', [gradeW(),
      Store.put('qplus', [fv('Q'), putRat(2n, 1n), mvq(0)])]);
    assert.equal(Store.child(out, 0), Store.put('tensor', [anteIn, goal]));
    assert.equal(Store.child(out, 1), Store.child(h, 1), 'consequent untouched');
  });

  it('lowers nested arithmetic in dependency order', () => {
    const h = parse('a * after (Q+2*R) -o { b }');
    const out = desugarTimed(h, CT);
    const goalMul = Store.put('bang', [gradeW(),
      Store.put('qmul', [putRat(2n, 1n), fv('R'), mvq(0)])]);
    const goalAdd = Store.put('bang', [gradeW(),
      Store.put('qplus', [fv('Q'), mvq(0), mvq(1)])]);
    const anteIn = Store.put('tensor', [atom('a'), Store.put('after', [mvq(1)])]);
    assert.equal(Store.child(out, 0),
      Store.put('tensor', [Store.put('tensor', [anteIn, goalMul]), goalAdd]));
  });

  it('identity for rules without windows (and for atomic window args)', () => {
    const h1 = parse('a -o { b }');
    assert.equal(desugarTimed(h1, CT), h1);
    const h2 = parse('a@Q * after Q * before 5 -o { b }');
    assert.equal(desugarTimed(h2, CT), h2);
  });

  it('rejects arithmetic in @ position (v1, E7.1)', () => {
    assert.throws(() => desugarTimed(parse('a@(Q+2) -o { b }'), CT),
      /grade position/);
    assert.throws(() => desugarTimed(parse('a -o { b }@(Q+1)'), CT),
      /grade position/);
  });

  it('rejects windows, read, and explicit stamps in the consequent', () => {
    assert.throws(() => desugarTimed(parse('a -o { after 2 * b }'), CT), /antecedent guards/);
    assert.throws(() => desugarTimed(parse('a -o { read b }'), CT), /'read' marks antecedent/);
    assert.throws(() => desugarTimed(parse('a -o { b@5 }'), CT), /scheduler/);
  });

  it('timed $A@Q: antecedent keeps the stamped pattern, consequent copy is UNSTAMPED (E3)', () => {
    // Parse with forwardRules for the $ sugar; desugarPreserved(stripStamps=true)
    // is what a timed loader (loaderConfig.timed) applies.
    const gt2 = calculus.load(FIXTURE);
    const parseF = buildParser(gt2.constructors, {
      gradeUnit: () => putRat(0n, 1n), forwardRules: true,
    });
    const h = parseF('$m@Q * w -o { p }');
    const out = desugarTimed(desugarPreserved(h, CT.computation, CT, true), CT);
    const mv = Store.put('freevar', ['Q']);
    assert.equal(Store.child(out, 0),
      Store.put('tensor', [Store.put('at', [atom('m'), mv]), atom('w')]),
      'antecedent pattern stays stamped (binds Q)');
    assert.equal(Store.child(Store.child(out, 1), 1),
      Store.put('tensor', [atom('m'), atom('p')]),
      'consequent copy is unstamped — the scheduler stamps at a(m)+d');
    // Without stripStamps (an untimed loader) the stamped injection is
    // caught by validation instead of silently freezing the stamp.
    assert.throws(() => desugarTimed(desugarPreserved(h, CT.computation, CT), CT),
      /scheduler/);
  });

  it('rejects stamped persistents (D15 backstop) and read of persistents', () => {
    const at = Store.put('at', [atom('a'), putRat(1n, 1n)]);
    const bad = Store.put('loli', [
      Store.put('bang', [gradeW(), at]),
      Store.put('gmonad', [putRat(0n, 1n), atom('b')])]);
    assert.throws(() => desugarTimed(bad, CT), /D15/);
    assert.throws(() => desugarTimed(parse('read !p -o { b }'), CT), /meaningless/);
  });

  it('D15 is transitive: stamps nested anywhere under ! are rejected (audit r12)', () => {
    assert.throws(() => desugarTimed(parse('! (a@3 * b) -o { c }'), CT), /D15/);
    assert.throws(() => desugarTimed(parse('! (b * (a@3 * d)) -o { c }'), CT), /D15/);
  });

  it('read $P is contradictory; read of a stamped pattern is deliberately legal (E7.2)', () => {
    const parseF = buildParser(calculus.load(FIXTURE).constructors, {
      gradeUnit: () => putRat(0n, 1n), forwardRules: true,
    });
    assert.throws(() => desugarTimed(parseF('read $a -o { b }'), CT), /contradictory/);
    // read A@Q: matches the stamped cohort without consuming; its stamp
    // joins the activation max — intended.
    const ok = parse('read a@3 * b -o { c }');
    assert.equal(desugarTimed(ok, CT), ok);
  });
});
