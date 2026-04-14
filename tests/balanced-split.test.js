/**
 * Direct tests for balanced-split.js
 *
 * Covers: bracket depth tracking (parens, braces, brackets after C33 fix),
 * nested separators, edge cases.
 */
const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const { balancedSplit } = require('../lib/parser/balanced-split');

describe('balancedSplit', () => {
  it('splits simple comma-separated tokens', () => {
    assert.deepEqual(balancedSplit('A, B, C', ','), ['A', ' B', ' C']);
  });

  it('splits on multi-char separator', () => {
    assert.deepEqual(balancedSplit('A |- B', '|-'), ['A ', ' B']);
  });

  it('respects parenthesis depth', () => {
    assert.deepEqual(balancedSplit('f(A, B), C', ','), ['f(A, B)', ' C']);
  });

  it('respects nested parentheses', () => {
    assert.deepEqual(balancedSplit('f(g(A, B), h(C, D)), E', ','), ['f(g(A, B), h(C, D))', ' E']);
  });

  it('respects brace depth', () => {
    assert.deepEqual(balancedSplit('{A, B}, C', ','), ['{A, B}', ' C']);
  });

  it('respects bracket depth (C33 fix)', () => {
    assert.deepEqual(balancedSplit('[A, B], C', ','), ['[A, B]', ' C']);
  });

  it('handles mixed bracket types', () => {
    assert.deepEqual(balancedSplit('f([A, B], {C, D}), E', ','), ['f([A, B], {C, D})', ' E']);
  });

  it('handles |- inside parentheses (C32 fix)', () => {
    assert.deepEqual(balancedSplit('f(A |- B) |- C', '|-'), ['f(A |- B) ', ' C']);
  });

  it('handles |- inside brackets', () => {
    assert.deepEqual(balancedSplit('[A |- B] |- C', '|-'), ['[A |- B] ', ' C']);
  });

  it('handles empty string', () => {
    assert.deepEqual(balancedSplit('', ','), ['']);
  });

  it('handles no separator present', () => {
    assert.deepEqual(balancedSplit('ABC', ','), ['ABC']);
  });

  it('handles separator at start', () => {
    assert.deepEqual(balancedSplit(',A', ','), ['', 'A']);
  });

  it('handles separator at end', () => {
    assert.deepEqual(balancedSplit('A,', ','), ['A', '']);
  });

  it('handles consecutive separators', () => {
    assert.deepEqual(balancedSplit('A,,B', ','), ['A', '', 'B']);
  });

  it('does not split on partial multi-char separator', () => {
    assert.deepEqual(balancedSplit('A | B |- C', '|-'), ['A | B ', ' C']);
  });

  it('handles deeply nested brackets', () => {
    const input = '([{A, B}], C), D';
    assert.deepEqual(balancedSplit(input, ','), ['([{A, B}], C)', ' D']);
  });
});
