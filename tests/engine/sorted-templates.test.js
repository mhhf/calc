/**
 * Sorted mixfix templates — TODO_0268 item A.
 *
 * The declaration-derived successor of the `timedAnnotations` flag: any
 * #N-hole @ascii template classifies by the POSITION of same-sort holes
 * (mixfix discipline) — closed / prefix / postfix / infix — and cross-sort
 * holes target the auxiliary (grade) chain. Pins:
 *   - classification of the till surface (at/after/before/read/woplus)
 *   - woplus infix `A +[Q] B` parses with exact argument reordering
 *   - fences: two auxiliary sorts, interior same-sort holes, missing holes
 *   - the tables are pure data (bundle-serializable)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { extractParserTables } from '../../lib/parser/earley-grammar.js';
import { putRat } from '../../lib/kernel/rat-term.js';

const TILL_CALC = path.join(import.meta.dirname, '../../calculus/till/till.calc');

const atom = (n) => Store.put('atom', [n]);

const ctor = (name, argTypes, returnType, ascii, prec) => ({
  name, argTypes, returnType,
  annotations: { ascii, ...(prec ? { prec: { precedence: prec, associativity: 'left' } } : {}) },
});

describe('template classification (mixfix discipline)', () => {
  it('classifies the till surface from till.calc', () => {
    const { templates } = extractParserTables(calculus.load(TILL_CALC).constructors);
    const kinds = Object.fromEntries(templates.map(t => [t.name, t.kind]));
    assert.deepEqual(kinds, {
      at: 'postfix',            // #1@#2 — same-sort hole at the left edge
      after: 'closed',          // after #1 — grade hole only
      before: 'closed',
      readPreserved: 'prefix',  // read #1 — same-sort hole at the right edge
      woplus: 'infix',          // #2 +[#1] #3 — same-sort holes at both edges
    });
  });

  it('tables are pure data (JSON round-trip survives)', () => {
    const t = extractParserTables(calculus.load(TILL_CALC).constructors);
    assert.deepEqual(JSON.parse(JSON.stringify(t.templates)), t.templates);
  });

  it('rejects interior same-sort holes (unsupported mixfix shape)', () => {
    assert.throws(() => extractParserTables({
      w: ctor('w', ['formula', 'formula'], 'formula', '<< #1 >> #2 <<'),
    }), /unsupported mixfix shape/);
  });

  it('rejects templates with missing holes (no general elision)', () => {
    assert.throws(() => extractParserTables({
      w: ctor('w', ['grade', 'formula'], 'formula', 'foo #2'),
    }), /every argument needs a hole/);
  });

  it('folds every auxiliary sort onto the one grade chain (TODO_0011: sorts are the checker\'s job)', async () => {
    // The former one-aux-sort fence guarded sort semantics the parser no
    // longer owns: since rung 1, per-hole sorts (delay/count/weight/…) are
    // enforced by the sort checker; the grammar carries only the shared
    // literal/expression surface.
    const { earleyGrammarFromTables, parserFromGrammar } = await import('../../lib/parser/earley-grammar.js');
    const tables = extractParserTables({
      a: ctor('a', ['formula', 'grade'], 'formula', '#1@#2', 90),
      b: ctor('b', ['formula', 'clock'], 'formula', '#1~#2', 91),
    });
    const parse = parserFromGrammar(earleyGrammarFromTables(
      { ...tables, multiCharFreevars: true, numbers: true }));
    assert.equal(parse('x@3'), Store.put('a', [atom('x'), putRat(3n, 1n)]));
    assert.equal(parse('x~5'), Store.put('b', [atom('x'), putRat(5n, 1n)]));
  });
});

describe('woplus infix surface `A +[Q] B` (Phase 4b sugar, 0268 A)', () => {
  let parse;
  before(() => {
    parse = buildParser(calculus.load(TILL_CALC).constructors, {
      multiCharFreevars: true, numbers: true,
      gradeUnit: () => putRat(0n, 1n),
    });
  });

  it('parses with exact argument reordering (grade first in the node)', () => {
    assert.equal(parse('a +[1/2] b'),
      Store.put('woplus', [putRat(1n, 2n), atom('a'), atom('b')]));
    assert.equal(parse('a +[3/4] b'),
      Store.put('woplus', [putRat(3n, 4n), atom('a'), atom('b')]));
  });

  it('sits at oplus precedence (65): tighter than * and -o, like ILL oplus', () => {
    assert.equal(parse('a * b +[1/2] c'),
      Store.put('tensor', [atom('a'),
        Store.put('woplus', [putRat(1n, 2n), atom('b'), atom('c')])]));
    assert.equal(parse('a -o b +[1/2] c'),
      Store.put('loli', [atom('a'),
        Store.put('woplus', [putRat(1n, 2n), atom('b'), atom('c')])]));
    assert.equal(parse('(a * b) +[1/2] c'),
      Store.put('woplus', [putRat(1n, 2n),
        Store.put('tensor', [atom('a'), atom('b')]), atom('c')]));
  });

  it('left-associates and the prefix application form still parses', () => {
    // (a +[1/2] b) +[1/3] c
    assert.equal(parse('a +[1/2] b +[1/3] c'),
      Store.put('woplus', [putRat(1n, 3n),
        Store.put('woplus', [putRat(1n, 2n), atom('a'), atom('b')]),
        atom('c')]));
    const app = buildParser(calculus.load(TILL_CALC).constructors, {
      multiCharFreevars: true, numbers: true, application: true,
      gradeUnit: () => putRat(0n, 1n),
    });
    assert.equal(app('woplus 1/2 a b'),
      Store.put('woplus', [putRat(1n, 2n), atom('a'), atom('b')]));
  });

  it('renders back through the declared template', () => {
    const till = calculus.load(TILL_CALC);
    const h = Store.put('woplus', [putRat(1n, 2n), atom('a'), atom('b')]);
    assert.match(till.render(h), /a \+\[.*\] b/);
  });
});
