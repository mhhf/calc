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

  it('fully delimited templates are closed — interior same-sort holes parse at START (§5c)', async () => {
    const { earleyGrammarFromTables, parserFromGrammar } = await import('../../lib/parser/earley-grammar.js');
    const tables = extractParserTables({
      w: ctor('w', ['formula', 'formula'], 'formula', '<< #1 >> #2 <<'),
      tensor: ctor('tensor', ['formula', 'formula'], 'formula', '_ * _', 60),
    });
    assert.equal(tables.templates[0].kind, 'closed');
    const parse = parserFromGrammar(earleyGrammarFromTables(tables));
    // Interior holes are unrestricted (loosest level), like `( A )`.
    assert.equal(parse('<< a * b >> c <<'),
      Store.put('w', [Store.put('tensor', [atom('a'), atom('b')]), atom('c')]));
  });

  it('an arity-1 `!`-prefixed #-template routes to templates, not unaryPrefix (TODO_0272 MINOR 2)', () => {
    // `@ascii "! #1"` starts with `!`, so the arity-1 unaryPrefix branch used
    // to swallow it into an untokenizable unaryPrefix['! #1'] before the
    // #-template branch ran. The `#`-guard routes it to templates instead.
    const tables = extractParserTables({
      e: ctor('e', ['formula'], 'formula', '! #1', 80),
    });
    assert.ok(tables.templates.some(t => t.name === 'e'),
      '`! #1` must classify as a template');
    assert.ok(!('! #1' in tables.unaryPrefix) && !('!' in tables.unaryPrefix),
      'must not leak into unaryPrefix');
  });

  it('rejects a same-sort hole that is neither at an edge nor delimited', () => {
    assert.throws(() => extractParserTables({
      w: ctor('w', ['formula', 'formula'], 'formula', '#1 << #2 >>'),
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

describe('parcel sugar `4wood` (§5d, D4 counted parcels)', () => {
  const flags = {
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true, numbers: true, application: true,
    arrows: true, forwardRules: true, binaryNormalization: true,
    gradeUnit: () => putRat(0n, 1n),
  };
  let parse;
  before(() => {
    parse = buildParser(calculus.load(TILL_CALC).constructors, flags);
  });

  it('fused `4wood` is hash-identical to `!_4 wood`', () => {
    assert.equal(parse('4wood'), parse('!_4 wood'));
    assert.equal(parse('4wood'),
      Store.put('bang', [putRat(4n, 1n), atom('wood')]));
  });

  it('works at formula-operand positions; names resolve like IDENTs', () => {
    assert.equal(parse('4wood * spoon'),
      Store.put('tensor', [Store.put('bang', [putRat(4n, 1n), atom('wood')]), atom('spoon')]));
    assert.equal(parse('2Wood'),
      Store.put('bang', [putRat(2n, 1n), Store.put('metavar', ['Wood'])]));
  });

  it('SPACED `4 wood` stays application juxtaposition — the surface is taken', () => {
    // `f 4 wood` = f(4, wood) is live syntax in rule bodies; standalone
    // `4 wood` is an app chain headed by the literal, NOT a parcel.
    assert.equal(parse('f 4 wood'),
      Store.put('f', [Store.put('binlit', [4n]), atom('wood')]));
    assert.equal(Store.tag(parse('4 wood')), 'app');
  });

  it('a spaced parcel production would be ambiguous (detector-verified — why fused won)', async () => {
    const { earleyGrammarFromTables, parserFromGrammar, extractParserTables: ept } =
      await import('../../lib/parser/earley-grammar.js');
    const { T, NT, setStrictAmbiguity } = await import('../../lib/parser/earley.js');
    const spec = earleyGrammarFromTables(
      { ...ept(calculus.load(TILL_CALC).constructors), ...flags });
    // Experiment: graft `UNARY → NUMBER operand` (the spaced parcel rule)
    // onto the real grammar, located via the $-preserved rule's shape.
    // Locate the $-preserved rule by its RHS shape (terminal '$' followed by a non-terminal),
    // not by the internal production tag, to avoid test-coupling to grammar internals.
    const dollar = spec.rules.find(r => r.rhs.length === 2 && r.rhs[0].sym === 0 && r.rhs[0].v === '$' && r.rhs[1].sym === 1);
    spec.rules.push({ lhs: dollar.lhs, rhs: [T('NUMBER'), NT(dollar.rhs[1].v)], action: c => c[1], tag: 'unary' });
    const p = parserFromGrammar(spec);
    setStrictAmbiguity(true);
    try {
      assert.throws(() => p('4 wood'), /Ambiguous parse/);
    } finally {
      setStrictAmbiguity(false);
    }
  });

  it('stamped parcels need the explicit form: `4wood@3` is a loud error', () => {
    assert.throws(() => parse('4wood@3'), /Parse error/);
    assert.equal(parse('!_4 wood@3'),
      Store.put('bang', [putRat(4n, 1n),
        Store.put('at', [atom('wood'), putRat(3n, 1n)])]));
  });

  it('parcels are formula operands, not term args: `f 4wood` is a loud error', () => {
    assert.throws(() => parse('f 4wood'), /Parse error/);
  });

  it('a keyword name is not parcelable: `4I` / `4type` are loud errors (TODO_0272 M3)', () => {
    // The fused path resolves the name like an IDENT, bypassing the keyword
    // table. Without the guard `4I` → bang(4, freevar('I')) diverges from
    // `!_4 I` → bang(4, one()). Throw instead — parceling a formula constant
    // is meaningless anyway.
    assert.throws(() => parse('4I'), /'I' is a keyword/);
    assert.throws(() => parse('4type'), /'type' is a keyword/);
    // a non-keyword resource name still parcels, incl. count 0
    assert.equal(parse('0wood'),
      Store.put('bang', [putRat(0n, 1n), atom('wood')]));
  });

  it('no parcels without a graded prefix + grade chain: ILL lexes `4wood` apart', () => {
    const ill = calculus.loadILL();
    const p = buildParser(ill.constructors, {
      multiCharFreevars: true, numbers: true, application: true,
    });
    // NUMBER and IDENT stay separate tokens — an app chain, never a bang.
    assert.equal(Store.tag(p('4wood')), 'app');
  });
});
