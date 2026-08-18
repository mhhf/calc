/**
 * Timed surface syntax — TODO_0265 Phase 3 acceptance (parser round-trip).
 *
 * `timedAnnotations`-gated grammar: postfix `A@t` stamps, `{B}@d` monad
 * grades, `after`/`before` windows with rational-expression args, the
 * `read` marker, and exact rational literals (digit-wise, never a float).
 * Also pins the rejections: `!A@t` (D15), double stamps, and that a
 * calculus without the gate parses none of it.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { putRat } from '../../lib/kernel/rat-term.js';

const FIXTURE = path.join(import.meta.dirname, '../fixtures/graded-comp.calc');

const atom = (n) => Store.put('atom', [n]);
const fv = (n) => Store.put('freevar', [n]);

describe('timed parser (gtoy fixture + timedAnnotations)', () => {
  let parse;
  before(() => {
    const gt = calculus.load(FIXTURE);
    parse = buildParser(gt.constructors, {
      gradeUnit: () => putRat(0n, 1n),
      timedAnnotations: true,
    });
  });

  it('stamps: integer, exact decimal, fraction, variable', () => {
    assert.equal(parse('a@3', ), Store.put('at', [atom('a'), putRat(3n, 1n)]));
    assert.equal(parse('a@0.5'), Store.put('at', [atom('a'), putRat(1n, 2n)]));
    assert.equal(parse('a@(3/2)'), Store.put('at', [atom('a'), putRat(3n, 2n)]));
    assert.equal(parse('a@Q'), Store.put('at', [atom('a'), fv('Q')]));
  });

  it('exact decimal lexing is digit-wise (0.1 stays 1/10)', () => {
    const h = parse('a@0.1');
    const t = Store.child(h, 1);
    assert.equal(Store.tag(t), 'ratlit');
    assert.equal(Store.child(t, 0), 1n);
    assert.equal(Store.child(t, 1), 10n);
    // 0.10 normalizes to the same hash
    assert.equal(parse('a@0.10'), h);
  });

  it('@ binds tighter than *', () => {
    assert.equal(parse('a@3 * b'),
      Store.put('tensor', [Store.put('at', [atom('a'), putRat(3n, 1n)]), atom('b')]));
  });

  it('bare {B} takes the unit grade; {B}@d replaces it', () => {
    assert.equal(parse('{ b }'), Store.put('gmonad', [putRat(0n, 1n), atom('b')]));
    assert.equal(parse('{ b }@2'), Store.put('gmonad', [putRat(2n, 1n), atom('b')]));
    assert.equal(parse('{ b }@0.5'), Store.put('gmonad', [putRat(1n, 2n), atom('b')]));
    assert.equal(parse('{ b }@D'), Store.put('gmonad', [fv('D'), atom('b')]));
  });

  it('windows: after/before with grade-expression args', () => {
    assert.equal(parse('before 5'), Store.put('before', [putRat(5n, 1n)]));
    assert.equal(parse('after (Q+2)'),
      Store.put('after', [Store.put('qexpr_add', [fv('Q'), putRat(2n, 1n)])]));
    // mul binds tighter than add inside grade expressions
    assert.equal(parse('after (Q+2*R)'),
      Store.put('after', [Store.put('qexpr_add', [fv('Q'),
        Store.put('qexpr_mul', [putRat(2n, 1n), fv('R')])])]));
  });

  it('read marker wraps the pattern', () => {
    assert.equal(parse('read a'), Store.put('readPreserved', [atom('a')]));
  });

  it('rational literals are ordinary term arguments too (facts: price 1/2)', () => {
    const gt = calculus.load(FIXTURE);
    const parseApp = buildParser(gt.constructors, {
      gradeUnit: () => putRat(0n, 1n), timedAnnotations: true, application: true,
    });
    assert.equal(parseApp('price 1/2'), Store.put('price', [putRat(1n, 2n)]));
    assert.equal(parseApp('p 0.5'), Store.put('p', [putRat(1n, 2n)]));
    assert.equal(parseApp('price (1/2)'), Store.put('price', [putRat(1n, 2n)]));
  });

  it('rejects: !A@t (D15), double stamps, @ on stamped node via parens', () => {
    assert.throws(() => parse('! a@3'), /D15/);
    assert.throws(() => parse('!_0 a@3'), /D15/);
    assert.throws(() => parse('(a@1)@2'), /double stamp/);
    assert.throws(() => parse('a@1@2'), /Parse error/);
  });

  it('float-formatted junk does not lex as a rational', () => {
    assert.throws(() => parse('a@1e5'), /Parse error/);
    assert.throws(() => parse('a@.5'), /Parse error/);
  });

  it('count-grade suffixes are RESERVED until Phase 4 — loud error, no silent misparse', () => {
    // Pre-fix, `!_2 wood` parsed as bang(ω, _2(wood)) — the phantom-wart class.
    assert.throws(() => parse('!_2 a'), /Parse error/);
    assert.throws(() => parse('!_W a'), /Parse error/);
  });

  it('zero denominator is a Parse error, not a leaked RangeError', () => {
    assert.throws(() => parse('a@3/0'), /Parse error: zero denominator/);
    assert.throws(() => parse('a@(3/0)'), /Parse error: zero denominator/);
  });

  it("'@' on an ungraded (1-ary) computation is rejected", async () => {
    const { earleyGrammarFromTables, parserFromGrammar } = await import('../../lib/parser/earley-grammar.js');
    const p = parserFromGrammar(earleyGrammarFromTables({
      operators: [], nullary: {}, unaryPrefix: {},
      circumfix: [{ open: '{', close: '}', name: 'monad', arity: 1 }],
      timedAnnotations: true,
    }));
    assert.throws(() => p('{ b }@3'), /ungraded computation/);
  });
});

describe('show.js renders timed forms exactly (no floats, no hex stamps)', () => {
  it('at / windows / read', async () => {
    const { show } = await import('../../lib/engine/show.js');
    assert.equal(show(Store.put('at', [atom('wood'), putRat(3n, 1n)])), 'wood@3');
    assert.equal(show(Store.put('at', [atom('wood'), putRat(1n, 2n)])), 'wood@1/2');
    assert.equal(show(Store.put('after', [putRat(5n, 2n)])), 'after 5/2');
    assert.equal(show(Store.put('readPreserved', [atom('emp')])), 'read emp');
  });
});

describe('timed syntax absent without the gate', () => {
  it('ILL parser rejects @, after, read', () => {
    const ill = calculus.loadILL();
    assert.throws(() => ill.parse('A@3'), /Parse error/);
    assert.throws(() => ill.parse('after (Q+2)'), /Parse error/);
    assert.throws(() => ill.parse('read A'), /Parse error/);
  });
});
