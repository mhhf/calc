/**
 * Earley grammar generation tests.
 *
 * Verifies that two grammar construction paths produce identical Store hashes:
 *   1. Tables path: computeParserTables(constructors) → buildParserFromTables(tables + opts)
 *   2. Direct path: computeEarleyGrammar(constructors, opts) → buildParserFromGrammar(spec)
 *
 * Both paths use the Earley engine internally. The test ensures that
 * operator extraction from constructors matches the direct grammar generation.
 */

'use strict';

const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../lib/kernel/store');
const { computeParserTables, buildParserFromTables } = require('../lib/calculus/builders');
const { computeEarleyGrammar, buildParserFromGrammar } = require('../lib/parser/earley-grammar');

// ─── Test fixtures ───────────────────────────────────────────────────────────

// Load ILL constructors for real-world testing
let ill;
let tablesParse, directParse;

// Full ILL engine opts (same as convert.js)
const ILL_OPTS = {
  binders: { exists: 'exists', forall: 'forall' },
  multiCharFreevars: true,
  numbers: true,
  application: true,
  arrows: true,
  forwardRules: true,
  binaryNormalization: true,
};

// Minimal opts (same as meta-parser/loader.js bootstrap)
const BOOTSTRAP_OPTS = {
  arrows: true,
  application: true,
  multiCharFreevars: true,
};

before(async () => {
  const calculus = require('../lib/calculus');
  ill = await calculus.loadILL();
});

// ─── Hash equality helper ────────────────────────────────────────────────────

function assertSameHash(parseFn1, parseFn2, expr) {
  assert.equal(
    parseFn1(expr), parseFn2(expr),
    `Hash mismatch for: "${expr}"\n` +
    `  Tables: ${parseFn1(expr)} (${showHash(parseFn1(expr))})\n` +
    `  Direct: ${parseFn2(expr)} (${showHash(parseFn2(expr))})`,
  );
}

function showHash(h) {
  const node = Store.get(h);
  if (!node) return `<unknown:${h}>`;
  const tag = node.tag || '?';
  return `${tag}(${node.children.map(c => typeof c === 'number' ? showHash(c) : String(c)).join(', ')})`;
}

// ─── Tests ───────────────────────────────────────────────────────────────────

describe('Earley grammar generation', () => {
  describe('ILL engine parser (full features)', () => {
    beforeEach(() => {
      Store.clear();
      const tables = computeParserTables(ill.constructors);
      tablesParse = buildParserFromTables({ ...tables, ...ILL_OPTS });
      const gram = computeEarleyGrammar(ill.constructors, ILL_OPTS);
      directParse = buildParserFromGrammar(gram);
    });

    // Binary operators
    it('tensor: A * B', () => assertSameHash(tablesParse, directParse, 'A * B'));
    it('with: A & B', () => assertSameHash(tablesParse, directParse, 'A & B'));
    it('oplus: A + B', () => assertSameHash(tablesParse, directParse, 'A + B'));
    it('loli: A -o B', () => assertSameHash(tablesParse, directParse, 'A -o B'));
    it('arrow: A -> B', () => assertSameHash(tablesParse, directParse, 'A -> B'));

    // Precedence
    it('prec: A * B + C = A*(B+C)', () => assertSameHash(tablesParse, directParse, 'A * B + C'));
    it('prec: A + B & C = A+(B&C)', () => assertSameHash(tablesParse, directParse, 'A + B & C'));
    it('prec: A -o B * C = A -o (B*C)', () => assertSameHash(tablesParse, directParse, 'A -o B * C'));

    // Associativity
    it('left-assoc: A * B * C', () => assertSameHash(tablesParse, directParse, 'A * B * C'));
    it('right-assoc: A -o B -o C', () => assertSameHash(tablesParse, directParse, 'A -o B -o C'));
    it('right-assoc: A -> B -> C', () => assertSameHash(tablesParse, directParse, 'A -> B -> C'));

    // Unary prefix
    it('bang: !A', () => assertSameHash(tablesParse, directParse, '!A'));
    it('double bang: !!A', () => assertSameHash(tablesParse, directParse, '!!A'));
    it('bang with op: !A * B', () => assertSameHash(tablesParse, directParse, '!A * B'));

    // Nullary
    it('one: I', () => assertSameHash(tablesParse, directParse, 'I'));
    it('zero: zero', () => assertSameHash(tablesParse, directParse, 'zero'));

    // Parentheses
    it('parens: (A * B)', () => assertSameHash(tablesParse, directParse, '(A * B)'));
    it('nested parens: ((A))', () => assertSameHash(tablesParse, directParse, '((A))'));
    it('parens override prec: (A + B) * C', () =>
      assertSameHash(tablesParse, directParse, '(A + B) * C'));

    // Monad
    it('monad: {A}', () => assertSameHash(tablesParse, directParse, '{A}'));
    it('monad in expr: A -o {B}', () => assertSameHash(tablesParse, directParse, 'A -o {B}'));
    it('monad complex: A -o {B * C}', () => assertSameHash(tablesParse, directParse, 'A -o {B * C}'));

    // Binders
    it('forall: forall X. A', () => assertSameHash(tablesParse, directParse, 'forall X. A'));
    it('exists: exists X. A', () => assertSameHash(tablesParse, directParse, 'exists X. A'));
    it('multi-var binder: forall X Y. A', () =>
      assertSameHash(tablesParse, directParse, 'forall X Y. A'));
    it('nested binder: forall X. exists Y. A', () =>
      assertSameHash(tablesParse, directParse, 'forall X. exists Y. A'));
    it('binder with op: forall X. A * B', () =>
      assertSameHash(tablesParse, directParse, 'forall X. A * B'));
    it('binder scope: A * forall X. B', () =>
      assertSameHash(tablesParse, directParse, 'A * forall X. B'));

    // Application (flat predicate form)
    it('unary app: f X', () => assertSameHash(tablesParse, directParse, 'f X'));
    it('binary app: f X Y', () => assertSameHash(tablesParse, directParse, 'f X Y'));
    it('app with op: f X * g Y', () => assertSameHash(tablesParse, directParse, 'f X * g Y'));

    // Numbers
    it('decimal: 42', () => assertSameHash(tablesParse, directParse, '42'));
    it('hex: 0xFF', () => assertSameHash(tablesParse, directParse, '0xFF'));

    // Binary normalization
    it('binnorm e: e', () => assertSameHash(tablesParse, directParse, 'e'));
    it('binnorm (i e): (i e)', () => assertSameHash(tablesParse, directParse, '(i e)'));
    it('binnorm (o (i e)): (o (i e))', () =>
      assertSameHash(tablesParse, directParse, '(o (i e))'));

    // Identifiers
    it('atom: foo', () => assertSameHash(tablesParse, directParse, 'foo'));
    it('metavar: Abc', () => assertSameHash(tablesParse, directParse, 'Abc'));
    it('type keyword: type', () => assertSameHash(tablesParse, directParse, 'type'));

    // Arrays
    it('empty array: []', () => assertSameHash(tablesParse, directParse, '[]'));
    it('array: [A, B]', () => assertSameHash(tablesParse, directParse, '[A, B]'));

    // Complex expressions
    it('complex: !storage K V * gas N', () =>
      assertSameHash(tablesParse, directParse, '!storage K V * gas N'));
    it('complex: A -o {B * C}', () =>
      assertSameHash(tablesParse, directParse, 'A -o {B * C}'));
    it('forward rule: storage K V -o {storage K V2}', () =>
      assertSameHash(tablesParse, directParse, 'storage K V -o {storage K V2}'));
  });

  describe('bootstrap parser (minimal features)', () => {
    beforeEach(() => {
      Store.clear();
      tablesParse = buildParserFromTables({
        operators: [], nullary: {}, unaryPrefix: {},
        ...BOOTSTRAP_OPTS,
      });
      const gram = computeEarleyGrammar({}, BOOTSTRAP_OPTS);
      directParse = buildParserFromGrammar(gram);
    });

    it('atom: foo', () => assertSameHash(tablesParse, directParse, 'foo'));
    it('arrow: a -> b', () => assertSameHash(tablesParse, directParse, 'a -> b'));
    it('app: f x y', () => assertSameHash(tablesParse, directParse, 'f x y'));
    it('type: type', () => assertSameHash(tablesParse, directParse, 'type'));
    it('parens: (a -> b)', () => assertSameHash(tablesParse, directParse, '(a -> b)'));
    it('metavar: X', () => assertSameHash(tablesParse, directParse, 'X'));
  });
});
