/**
 * Earley grammar generation tests.
 *
 * Verifies that the Earley parser produces identical Store hashes
 * as the Pratt parser for all expression types.
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
let prattParse, earleyParseFn;

// Full ILL engine opts (same as convert.js ILL_ENGINE_TABLES)
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

function assertSameHash(pratt, earley, expr) {
  assert.equal(
    pratt(expr), earley(expr),
    `Hash mismatch for: "${expr}"\n` +
    `  Pratt:  ${pratt(expr)} (${showHash(pratt(expr))})\n` +
    `  Earley: ${earley(expr)} (${showHash(earley(expr))})`,
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
      prattParse = buildParserFromTables({ ...tables, ...ILL_OPTS });
      const gram = computeEarleyGrammar(ill.constructors, ILL_OPTS);
      earleyParseFn = buildParserFromGrammar(gram);
    });

    // Binary operators
    it('tensor: A * B', () => assertSameHash(prattParse, earleyParseFn, 'A * B'));
    it('with: A & B', () => assertSameHash(prattParse, earleyParseFn, 'A & B'));
    it('oplus: A + B', () => assertSameHash(prattParse, earleyParseFn, 'A + B'));
    it('loli: A -o B', () => assertSameHash(prattParse, earleyParseFn, 'A -o B'));
    it('arrow: A -> B', () => assertSameHash(prattParse, earleyParseFn, 'A -> B'));

    // Precedence
    it('prec: A * B + C = (A*B) + C', () => assertSameHash(prattParse, earleyParseFn, 'A * B + C'));
    it('prec: A + B & C = (A+B) & C', () => assertSameHash(prattParse, earleyParseFn, 'A + B & C'));
    it('prec: A -o B * C = A -o (B*C)', () => assertSameHash(prattParse, earleyParseFn, 'A -o B * C'));

    // Associativity
    it('left-assoc: A * B * C', () => assertSameHash(prattParse, earleyParseFn, 'A * B * C'));
    it('right-assoc: A -o B -o C', () => assertSameHash(prattParse, earleyParseFn, 'A -o B -o C'));
    it('right-assoc: A -> B -> C', () => assertSameHash(prattParse, earleyParseFn, 'A -> B -> C'));

    // Unary prefix
    it('bang: !A', () => assertSameHash(prattParse, earleyParseFn, '!A'));
    it('double bang: !!A', () => assertSameHash(prattParse, earleyParseFn, '!!A'));
    it('bang with op: !A * B', () => assertSameHash(prattParse, earleyParseFn, '!A * B'));

    // Nullary
    it('one: I', () => assertSameHash(prattParse, earleyParseFn, 'I'));
    it('zero: zero', () => assertSameHash(prattParse, earleyParseFn, 'zero'));

    // Parentheses
    it('parens: (A * B)', () => assertSameHash(prattParse, earleyParseFn, '(A * B)'));
    it('nested parens: ((A))', () => assertSameHash(prattParse, earleyParseFn, '((A))'));
    it('parens override prec: (A + B) * C', () =>
      assertSameHash(prattParse, earleyParseFn, '(A + B) * C'));

    // Monad
    it('monad: {A}', () => assertSameHash(prattParse, earleyParseFn, '{A}'));
    it('monad in expr: A -o {B}', () => assertSameHash(prattParse, earleyParseFn, 'A -o {B}'));
    it('monad complex: A -o {B * C}', () => assertSameHash(prattParse, earleyParseFn, 'A -o {B * C}'));

    // Binders
    it('forall: forall X. A', () => assertSameHash(prattParse, earleyParseFn, 'forall X. A'));
    it('exists: exists X. A', () => assertSameHash(prattParse, earleyParseFn, 'exists X. A'));
    it('multi-var binder: forall X Y. A', () =>
      assertSameHash(prattParse, earleyParseFn, 'forall X Y. A'));
    it('nested binder: forall X. exists Y. A', () =>
      assertSameHash(prattParse, earleyParseFn, 'forall X. exists Y. A'));
    it('binder with op: forall X. A * B', () =>
      assertSameHash(prattParse, earleyParseFn, 'forall X. A * B'));
    it('binder scope: A * forall X. B', () =>
      assertSameHash(prattParse, earleyParseFn, 'A * forall X. B'));

    // Application (flat predicate form)
    it('unary app: f X', () => assertSameHash(prattParse, earleyParseFn, 'f X'));
    it('binary app: f X Y', () => assertSameHash(prattParse, earleyParseFn, 'f X Y'));
    it('app with op: f X * g Y', () => assertSameHash(prattParse, earleyParseFn, 'f X * g Y'));

    // Numbers
    it('decimal: 42', () => assertSameHash(prattParse, earleyParseFn, '42'));
    it('hex: 0xFF', () => assertSameHash(prattParse, earleyParseFn, '0xFF'));

    // Binary normalization
    it('binnorm e: e', () => assertSameHash(prattParse, earleyParseFn, 'e'));
    it('binnorm (i e): (i e)', () => assertSameHash(prattParse, earleyParseFn, '(i e)'));
    it('binnorm (o (i e)): (o (i e))', () =>
      assertSameHash(prattParse, earleyParseFn, '(o (i e))'));

    // Identifiers
    it('atom: foo', () => assertSameHash(prattParse, earleyParseFn, 'foo'));
    it('metavar: Abc', () => assertSameHash(prattParse, earleyParseFn, 'Abc'));
    it('type keyword: type', () => assertSameHash(prattParse, earleyParseFn, 'type'));

    // Arrays
    it('empty array: []', () => assertSameHash(prattParse, earleyParseFn, '[]'));
    it('array: [A, B]', () => assertSameHash(prattParse, earleyParseFn, '[A, B]'));

    // Complex expressions
    it('complex: !storage K V * gas N', () =>
      assertSameHash(prattParse, earleyParseFn, '!storage K V * gas N'));
    it('complex: A -o {B * C}', () =>
      assertSameHash(prattParse, earleyParseFn, 'A -o {B * C}'));
    it('forward rule: storage K V -o {storage K V2}', () =>
      assertSameHash(prattParse, earleyParseFn, 'storage K V -o {storage K V2}'));
  });

  describe('bootstrap parser (minimal features)', () => {
    beforeEach(() => {
      Store.clear();
      prattParse = buildParserFromTables({
        operators: [], nullary: {}, unaryPrefix: {},
        ...BOOTSTRAP_OPTS,
      });
      const gram = computeEarleyGrammar({}, BOOTSTRAP_OPTS);
      earleyParseFn = buildParserFromGrammar(gram);
    });

    it('atom: foo', () => assertSameHash(prattParse, earleyParseFn, 'foo'));
    it('arrow: a -> b', () => assertSameHash(prattParse, earleyParseFn, 'a -> b'));
    it('app: f x y', () => assertSameHash(prattParse, earleyParseFn, 'f x y'));
    it('type: type', () => assertSameHash(prattParse, earleyParseFn, 'type'));
    it('parens: (a -> b)', () => assertSameHash(prattParse, earleyParseFn, '(a -> b)'));
    it('metavar: X', () => assertSameHash(prattParse, earleyParseFn, 'X'));
  });
});
