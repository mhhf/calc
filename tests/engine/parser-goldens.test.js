/**
 * Parser goldens — TODO_0265 Phase 3 (circumfix derivation).
 *
 * Pins the parse STRUCTURE of representative ILL formulas through both
 * parser paths (calculus formula parser + .ill expression parser) BEFORE
 * the grammar-generator refactor that derives the `{ _ }` brace rule and
 * the `!` graded-prefix rules from @ascii declarations instead of
 * hardcodes. "ILL unchanged" = every case here stays hash-identical.
 */

import { test } from 'node:test';
import assert from 'node:assert';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import convert from '../../lib/engine/convert.js';
import { grade0, gradeW } from '../../lib/engine/grades.js';

const fv = (n) => Store.put('freevar', [n]);
const mv = (n) => Store.put('metavar', [n]);
const atom = (n) => Store.put('atom', [n]);
const bin = (n) => Store.put('binlit', [n]);

test('calculus parser goldens (ILL formula parser)', () => {
  const ill = calculus.loadILL();
  const A = ill.AST;
  const cases = [
    ['{ A }', () => A.monad(fv('A'))],
    ['{ A * B }', () => A.monad(A.tensor(fv('A'), fv('B')))],
    ['A -o { B }', () => A.loli(fv('A'), A.monad(fv('B')))],
    ['A -o B', () => A.loli(fv('A'), fv('B'))],
    ['! A', () => A.bang(gradeW(), fv('A'))],
    ['!_0 A', () => A.bang(grade0(), fv('A'))],
    ['!_ω A', () => A.bang(gradeW(), fv('A'))],
    ['! A * B', () => A.tensor(A.bang(gradeW(), fv('A')), fv('B'))],
    ['A * B', () => A.tensor(fv('A'), fv('B'))],
    ['A -o B * C', () => A.loli(fv('A'), A.tensor(fv('B'), fv('C')))],
    ['A + B', () => A.oplus(fv('A'), fv('B'))],
    ['A & B', () => A.with(fv('A'), fv('B'))],
    ['I', () => A.one()],
    ['zero', () => A.zero()],
    ['(A + B) & C', () => A.with(A.oplus(fv('A'), fv('B')), fv('C'))],
    ['{ A } * B', () => A.tensor(A.monad(fv('A')), fv('B'))],
  ];
  for (const [src, mk] of cases) {
    assert.strictEqual(ill.parse(src), mk(), `calculus parse: ${src}`);
  }
});

test('expr parser goldens (.ill expression parser)', () => {
  const p = convert.parseExpr;
  const cases = [
    ['{ A }', () => Store.put('monad', [mv('A')])],
    ['a * b -o { c }', () => Store.put('loli', [
      Store.put('tensor', [atom('a'), atom('b')]),
      Store.put('monad', [atom('c')])])],
    ['a -o { b * c }', () => Store.put('loli', [atom('a'),
      Store.put('monad', [Store.put('tensor', [atom('b'), atom('c')])])])],
    ['$a * b -o { c }', () => Store.put('loli', [
      Store.put('tensor', [Store.put('preserved', [atom('a')]), atom('b')]),
      Store.put('monad', [atom('c')])])],
    ['!plus X Y Z', () => Store.put('bang', [gradeW(),
      Store.put('plus', [mv('X'), mv('Y'), mv('Z')])])],
    ['!_0 q A', () => Store.put('bang', [grade0(),
      Store.put('q', [mv('A')])])],
    ['p 5', () => Store.put('p', [bin(5n)])],
    ['e', () => bin(0n)],
    ['(i (o (i e)))', () => bin(5n)],
    ['exists X. p X', () => Store.put('exists', [
      Store.put('p', [Store.put('bound', [0n])])])],
    ['{ stack S }', () => Store.put('monad', [Store.put('stack', [mv('S')])])],
  ];
  for (const [src, mk] of cases) {
    assert.strictEqual(p(src), mk(), `expr parse: ${src}`);
  }
});
