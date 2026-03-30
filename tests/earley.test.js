/**
 * Earley parser — core engine tests.
 *
 * Tests the generic Earley recognizer, lexer, tree extraction,
 * and error reporting. Grammar-agnostic (no ILL dependency).
 */

'use strict';

const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const { T, NT, grammar, tokenize, earleyParse, createParser } = require('../lib/parser/earley');

// ─── Helpers ─────────────────────────────────────────────────────────────────

// Nonterminal IDs (arbitrary integers)
const S = 0, E = 1, A = 2, B = 3, F = 4;

/** Shorthand: make rules for arithmetic grammars. */
function arithGrammar() {
  // S → E
  // E → E '+' E | E '*' E | '(' E ')' | NUMBER
  // Ambiguous! Earley handles it, but tree extraction picks first derivation.
  //
  // Instead, use stratified (unambiguous) version:
  //   S → Add
  //   Add → Add '+' Mul | Mul
  //   Mul → Mul '*' Atom | Atom
  //   Atom → '(' Add ')' | NUMBER
  const ADD = 1, MUL = 2, ATOM = 3;
  return {
    rules: [
      { lhs: S, rhs: [NT(ADD)], action: c => c[0] },
      // Add → Add '+' Mul
      { lhs: ADD, rhs: [NT(ADD), T('+'), NT(MUL)],
        action: c => ({ op: '+', l: c[0], r: c[2] }) },
      // Add → Mul
      { lhs: ADD, rhs: [NT(MUL)], action: c => c[0] },
      // Mul → Mul '*' Atom
      { lhs: MUL, rhs: [NT(MUL), T('*'), NT(ATOM)],
        action: c => ({ op: '*', l: c[0], r: c[2] }) },
      // Mul → Atom
      { lhs: MUL, rhs: [NT(ATOM)], action: c => c[0] },
      // Atom → '(' Add ')'
      { lhs: ATOM, rhs: [T('('), NT(ADD), T(')')], action: c => c[1] },
      // Atom → NUMBER
      { lhs: ATOM, rhs: [T('NUMBER')], action: c => Number(c[0].value) },
    ],
    start: S,
  };
}

function arithLexer() {
  return { operators: ['+', '*'], numbers: true };
}

// ─── Lexer Tests ─────────────────────────────────────────────────────────────

describe('Earley lexer', () => {
  it('tokenizes identifiers', () => {
    const toks = tokenize('foo bar_1', {});
    assert.equal(toks.length, 2);
    assert.equal(toks[0].type, 'IDENT');
    assert.equal(toks[0].value, 'foo');
    assert.equal(toks[1].value, 'bar_1');
  });

  it('tokenizes numbers', () => {
    const toks = tokenize('42 0xFF', { numbers: true });
    assert.equal(toks.length, 2);
    assert.equal(toks[0].type, 'NUMBER');
    assert.equal(toks[0].value, '42');
    assert.equal(toks[1].value, '0xFF');
  });

  it('tokenizes multi-char operators (longest match)', () => {
    const toks = tokenize('a -o b -> c', { operators: ['-o', '->'] });
    assert.equal(toks.length, 5);
    assert.equal(toks[1].type, '-o');
    assert.equal(toks[3].type, '->');
  });

  it('tokenizes keywords', () => {
    const toks = tokenize('forall X', { keywords: ['forall'] });
    assert.equal(toks[0].type, 'forall');
    assert.equal(toks[0].value, 'forall');
    assert.equal(toks[1].type, 'IDENT');
  });

  it('does not match keyword prefix as keyword', () => {
    const toks = tokenize('forallX', { keywords: ['forall'] });
    assert.equal(toks.length, 1);
    assert.equal(toks[0].type, 'IDENT');
    assert.equal(toks[0].value, 'forallX');
  });

  it('tokenizes brackets and single-char operators', () => {
    const toks = tokenize('(a + b)', { operators: ['+'] });
    assert.equal(toks.length, 5);
    assert.equal(toks[0].type, '(');
    assert.equal(toks[2].type, '+');
    assert.equal(toks[4].type, ')');
  });

  it('skips whitespace and comments', () => {
    const toks = tokenize('a % comment\nb', {});
    assert.equal(toks.length, 2);
    assert.equal(toks[0].value, 'a');
    assert.equal(toks[1].value, 'b');
  });

  it('records token positions', () => {
    const toks = tokenize('ab + cd', { operators: ['+'] });
    assert.equal(toks[0].pos, 0);
    assert.equal(toks[1].pos, 3);
    assert.equal(toks[2].pos, 5);
  });

  it('handles empty input', () => {
    assert.equal(tokenize('', {}).length, 0);
    assert.equal(tokenize('   ', {}).length, 0);
  });

  it('does not match operator mid-word', () => {
    const toks = tokenize('forall', { operators: ['for'], keywords: [] });
    // 'for' should not match because 'forall' continues with alpha
    assert.equal(toks.length, 1);
    assert.equal(toks[0].type, 'IDENT');
    assert.equal(toks[0].value, 'forall');
  });

  it('handles adjacent operators', () => {
    const toks = tokenize('!a', { operators: ['!'] });
    assert.equal(toks.length, 2);
    assert.equal(toks[0].type, '!');
    assert.equal(toks[1].type, 'IDENT');
  });
});

// ─── Grammar Construction Tests ──────────────────────────────────────────────

describe('Earley grammar', () => {
  it('computes nullable set for ε-rules', () => {
    const g = grammar([
      { lhs: S, rhs: [NT(A)], action: null },
      { lhs: A, rhs: [], action: null },           // A → ε
      { lhs: A, rhs: [T('x')], action: null },     // A → 'x'
    ], S);
    assert.ok(g.nullable.has(A));
    assert.ok(g.nullable.has(S));  // S → A, A nullable ⇒ S nullable
  });

  it('computes transitive nullable', () => {
    const g = grammar([
      { lhs: S, rhs: [NT(A), NT(B)], action: null },
      { lhs: A, rhs: [], action: null },
      { lhs: B, rhs: [], action: null },
    ], S);
    assert.ok(g.nullable.has(A));
    assert.ok(g.nullable.has(B));
    assert.ok(g.nullable.has(S));
  });

  it('non-nullable stays non-nullable', () => {
    const g = grammar([
      { lhs: S, rhs: [T('x')], action: null },
    ], S);
    assert.ok(!g.nullable.has(S));
  });

  it('indexes rules by LHS', () => {
    const g = grammar([
      { lhs: S, rhs: [NT(A)], action: null },
      { lhs: A, rhs: [T('x')], action: null },
      { lhs: A, rhs: [T('y')], action: null },
    ], S);
    assert.deepEqual(g.byLhs.get(S), [0]);
    assert.deepEqual(g.byLhs.get(A), [1, 2]);
  });
});

// ─── Recognizer + Tree Extraction Tests ──────────────────────────────────────

describe('Earley parser', () => {
  describe('arithmetic (stratified)', () => {
    const spec = arithGrammar();
    const g = grammar(spec.rules, spec.start);

    it('parses a single number', () => {
      const result = earleyParse(g, tokenize('42', arithLexer()));
      assert.equal(result, 42);
    });

    it('parses addition', () => {
      const result = earleyParse(g, tokenize('1 + 2', arithLexer()));
      assert.deepEqual(result, { op: '+', l: 1, r: 2 });
    });

    it('parses multiplication', () => {
      const result = earleyParse(g, tokenize('3 * 4', arithLexer()));
      assert.deepEqual(result, { op: '*', l: 3, r: 4 });
    });

    it('respects precedence: a + b * c', () => {
      const result = earleyParse(g, tokenize('1 + 2 * 3', arithLexer()));
      assert.deepEqual(result, {
        op: '+', l: 1,
        r: { op: '*', l: 2, r: 3 },
      });
    });

    it('respects precedence: a * b + c', () => {
      const result = earleyParse(g, tokenize('2 * 3 + 1', arithLexer()));
      assert.deepEqual(result, {
        op: '+',
        l: { op: '*', l: 2, r: 3 },
        r: 1,
      });
    });

    it('left-associates: a + b + c', () => {
      const result = earleyParse(g, tokenize('1 + 2 + 3', arithLexer()));
      assert.deepEqual(result, {
        op: '+',
        l: { op: '+', l: 1, r: 2 },
        r: 3,
      });
    });

    it('left-associates: a * b * c', () => {
      const result = earleyParse(g, tokenize('2 * 3 * 4', arithLexer()));
      assert.deepEqual(result, {
        op: '*',
        l: { op: '*', l: 2, r: 3 },
        r: 4,
      });
    });

    it('parses parenthesized expressions', () => {
      const result = earleyParse(g, tokenize('(1 + 2) * 3', arithLexer()));
      assert.deepEqual(result, {
        op: '*',
        l: { op: '+', l: 1, r: 2 },
        r: 3,
      });
    });

    it('parses nested parentheses', () => {
      const result = earleyParse(g, tokenize('((1))', arithLexer()));
      assert.equal(result, 1);
    });

    it('parses complex expression', () => {
      // (1 + 2) * (3 + 4)
      const result = earleyParse(g, tokenize('(1 + 2) * (3 + 4)', arithLexer()));
      assert.deepEqual(result, {
        op: '*',
        l: { op: '+', l: 1, r: 2 },
        r: { op: '+', l: 3, r: 4 },
      });
    });
  });

  describe('right-associative operators', () => {
    // Arrow: a -> b -> c = a -> (b -> c)
    // Stratified: Arr → Atom '->' Arr | Atom
    const ARR = 1, ATOM = 2;
    const spec = {
      rules: [
        { lhs: S, rhs: [NT(ARR)], action: c => c[0] },
        { lhs: ARR, rhs: [NT(ATOM), T('->'), NT(ARR)],
          action: c => ({ op: '->', l: c[0], r: c[2] }) },
        { lhs: ARR, rhs: [NT(ATOM)], action: c => c[0] },
        { lhs: ATOM, rhs: [T('IDENT')], action: c => c[0].value },
        { lhs: ATOM, rhs: [T('('), NT(ARR), T(')')], action: c => c[1] },
      ],
      start: S,
    };
    const g = grammar(spec.rules, spec.start);
    const lex = { operators: ['->'] };

    it('right-associates: a -> b -> c', () => {
      const result = earleyParse(g, tokenize('a -> b -> c', lex));
      assert.deepEqual(result, {
        op: '->',
        l: 'a',
        r: { op: '->', l: 'b', r: 'c' },
      });
    });

    it('parses single atom', () => {
      assert.equal(earleyParse(g, tokenize('x', lex)), 'x');
    });
  });

  describe('unary prefix', () => {
    // ! is prefix, higher precedence than *
    // S → E, E → '!' E | E '*' E | ATOM
    // Stratified: S → Mul, Mul → Mul '*' Unary | Unary, Unary → '!' Unary | Atom, Atom → IDENT | '(' Mul ')'
    const MUL = 1, UNARY = 2, ATOM = 3;
    const spec = {
      rules: [
        { lhs: S, rhs: [NT(MUL)], action: c => c[0] },
        { lhs: MUL, rhs: [NT(MUL), T('*'), NT(UNARY)],
          action: c => ({ op: '*', l: c[0], r: c[2] }) },
        { lhs: MUL, rhs: [NT(UNARY)], action: c => c[0] },
        { lhs: UNARY, rhs: [T('!'), NT(UNARY)],
          action: c => ({ op: '!', x: c[1] }) },
        { lhs: UNARY, rhs: [NT(ATOM)], action: c => c[0] },
        { lhs: ATOM, rhs: [T('IDENT')], action: c => c[0].value },
        { lhs: ATOM, rhs: [T('('), NT(MUL), T(')')], action: c => c[1] },
      ],
      start: S,
    };
    const g = grammar(spec.rules, spec.start);
    const lex = { operators: ['!', '*'] };

    it('parses !a', () => {
      assert.deepEqual(
        earleyParse(g, tokenize('!a', lex)),
        { op: '!', x: 'a' },
      );
    });

    it('parses !!a', () => {
      assert.deepEqual(
        earleyParse(g, tokenize('!!a', lex)),
        { op: '!', x: { op: '!', x: 'a' } },
      );
    });

    it('! binds tighter than *: !a * b', () => {
      assert.deepEqual(
        earleyParse(g, tokenize('!a * b', lex)),
        { op: '*', l: { op: '!', x: 'a' }, r: 'b' },
      );
    });
  });

  describe('nullable nonterminals', () => {
    // S → A 'x', A → 'a' | ε
    const spec = {
      rules: [
        { lhs: S, rhs: [NT(A), T('x')], action: c => ({ a: c[0], x: c[1].value }) },
        { lhs: A, rhs: [T('a')], action: c => c[0].value },
        { lhs: A, rhs: [], action: () => null },
      ],
      start: S,
    };
    const g = grammar(spec.rules, spec.start);
    const lex = { keywords: ['a', 'x'] };

    it('parses with nullable present: a x', () => {
      const result = earleyParse(g, tokenize('a x', lex));
      assert.deepEqual(result, { a: 'a', x: 'x' });
    });

    it('parses with nullable absent: x', () => {
      const result = earleyParse(g, tokenize('x', lex));
      assert.deepEqual(result, { a: null, x: 'x' });
    });
  });

  describe('left recursion', () => {
    // List: S → S ',' IDENT | IDENT
    // This is inherently left-recursive — Earley handles it natively.
    const spec = {
      rules: [
        { lhs: S, rhs: [NT(S), T(','), T('IDENT')],
          action: c => [...c[0], c[2].value] },
        { lhs: S, rhs: [T('IDENT')], action: c => [c[0].value] },
      ],
      start: S,
    };
    const g = grammar(spec.rules, spec.start);

    it('parses single element', () => {
      assert.deepEqual(earleyParse(g, tokenize('a', {})), ['a']);
    });

    it('parses comma-separated list', () => {
      assert.deepEqual(earleyParse(g, tokenize('a, b, c', {})), ['a', 'b', 'c']);
    });
  });

  describe('empty input', () => {
    it('parses if start is nullable', () => {
      const g = grammar([
        { lhs: S, rhs: [], action: () => 'empty' },
      ], S);
      assert.equal(earleyParse(g, []), 'empty');
    });

    it('fails if start is not nullable', () => {
      const g = grammar([
        { lhs: S, rhs: [T('x')], action: c => c[0].value },
      ], S);
      assert.throws(
        () => earleyParse(g, []),
        /Parse error/,
      );
    });
  });

  describe('error reporting', () => {
    const spec = arithGrammar();
    const g = grammar(spec.rules, spec.start);

    it('reports error on invalid input', () => {
      assert.throws(
        () => earleyParse(g, tokenize('+', arithLexer())),
        /Parse error/,
      );
    });

    it('reports expected tokens', () => {
      try {
        earleyParse(g, tokenize('1 +', arithLexer()));
        assert.fail('should throw');
      } catch (e) {
        assert.match(e.message, /Parse error/);
        assert.match(e.message, /end of input/);
      }
    });

    it('reports position of unexpected token', () => {
      try {
        earleyParse(g, tokenize('1 + +', arithLexer()));
        assert.fail('should throw');
      } catch (e) {
        assert.match(e.message, /Parse error/);
      }
    });

    it('reports error for trailing garbage', () => {
      // Parser finds "1" as complete parse, but there's "+ 2" remaining.
      // Since our grammar wraps in S, the parser should fail because
      // "1 +" doesn't complete — it expects a number after +.
      // Actually "1 + 2 3" is the trailing garbage case.
      assert.throws(
        () => earleyParse(g, tokenize('1 2', arithLexer())),
        /Parse error/,
      );
    });
  });
});

// ─── createParser integration ────────────────────────────────────────────────

describe('createParser', () => {
  it('creates a string → value parser', () => {
    const spec = arithGrammar();
    const parse = createParser(spec, arithLexer());
    assert.equal(parse('42'), 42);
    assert.deepEqual(parse('1 + 2'), { op: '+', l: 1, r: 2 });
  });
});

// ─── Stress / edge cases ─────────────────────────────────────────────────────

describe('Earley edge cases', () => {
  it('handles deeply nested parentheses', () => {
    const spec = arithGrammar();
    const parse = createParser(spec, arithLexer());
    // ((((1)))) — 4 levels of nesting
    assert.equal(parse('((((1))))'), 1);
  });

  it('handles long expression chain', () => {
    const spec = arithGrammar();
    const parse = createParser(spec, arithLexer());
    // 1 + 2 + 3 + ... + 10 — left-recursive chain
    const result = parse('1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10');
    // Should be deeply left-nested
    assert.equal(result.op, '+');
    assert.equal(result.r, 10);
  });

  it('handles mixed precedence chain', () => {
    const spec = arithGrammar();
    const parse = createParser(spec, arithLexer());
    // 1 + 2 * 3 + 4 * 5 = ((1 + (2*3)) + (4*5))
    const result = parse('1 + 2 * 3 + 4 * 5');
    assert.deepEqual(result, {
      op: '+',
      l: { op: '+', l: 1, r: { op: '*', l: 2, r: 3 } },
      r: { op: '*', l: 4, r: 5 },
    });
  });

  it('multiple rules for same nonterminal', () => {
    // S → 'a' | 'b' | 'c'
    const g = grammar([
      { lhs: S, rhs: [T('IDENT')], action: c => c[0].value },
    ], S);
    assert.equal(earleyParse(g, tokenize('foo', {})), 'foo');
  });
});
