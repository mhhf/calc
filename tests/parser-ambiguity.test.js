/**
 * Ambiguity instrument (TODO_0268 §5a) — per-parse detection in the Earley
 * core. Static CFG ambiguity is undecidable; the instrument reports what
 * THIS input exposed: dual-derivation chart items (first-wins sites) and
 * multiple accepting items. Strict mode turns either into a parse error.
 */

import { describe, it, afterEach } from 'node:test';
import assert from 'node:assert/strict';
import { T, NT, grammar, tokenize, earleyParse, setStrictAmbiguity, ambiguityStats } from '../lib/parser/earley.js';

afterEach(() => setStrictAmbiguity(false));

// E → E '+' E | IDENT — the canonical ambiguous expression grammar.
const ambiguous = grammar([
  { lhs: 0, rhs: [NT(0), T('+'), NT(0)], action: c => ['+', c[0], c[2]] },
  { lhs: 0, rhs: [T('IDENT')], action: c => c[0].value },
], 0);

// E → E '+' F | F; F → IDENT — same language, stratified (unambiguous).
const stratified = grammar([
  { lhs: 0, rhs: [NT(0), T('+'), NT(1)], action: c => ['+', c[0], c[2]] },
  { lhs: 0, rhs: [NT(1)], action: c => c[0] },
  { lhs: 1, rhs: [T('IDENT')], action: c => c[0].value },
], 0);

// S → A | B; A → IDENT; B → IDENT — two accepting items, no dual backs.
const dualAccept = grammar([
  { lhs: 0, rhs: [NT(1)], action: c => ['A', c[0]] },
  { lhs: 0, rhs: [NT(2)], action: c => ['B', c[0]] },
  { lhs: 1, rhs: [T('IDENT')], action: c => c[0].value },
  { lhs: 2, rhs: [T('IDENT')], action: c => c[0].value },
], 0);

const toks = (s) => tokenize(s, { operators: ['+'] });

describe('ambiguity instrument (§5a)', () => {
  it('counts dual-derivation items on an ambiguous input (first-wins preserved)', () => {
    const result = earleyParse(ambiguous, toks('a + b + c'));
    assert.ok(Array.isArray(result), 'still produces a (first-wins) parse');
    assert.ok(ambiguityStats().dupItems > 0, 'dual-derivation item detected');
  });

  it('reports zero on the same input under a stratified grammar', () => {
    const result = earleyParse(stratified, toks('a + b + c'));
    assert.deepEqual(result, ['+', ['+', 'a', 'b'], 'c']);
    const s = ambiguityStats();
    assert.equal(s.dupItems, 0);
    assert.equal(s.accepts, 1);
  });

  it('detects multiple accepting items', () => {
    earleyParse(dualAccept, toks('a'));
    assert.equal(ambiguityStats().accepts, 2);
  });

  it('strict mode throws on either signal, stays silent when unambiguous', () => {
    setStrictAmbiguity(true);
    assert.throws(() => earleyParse(ambiguous, toks('a + b + c')), /Ambiguous parse/);
    assert.throws(() => earleyParse(dualAccept, toks('a')), /Ambiguous parse/);
    assert.deepEqual(earleyParse(stratified, toks('a + b')), ['+', 'a', 'b']);
  });

  it('stats reset per parse', () => {
    earleyParse(ambiguous, toks('a + b + c'));
    assert.ok(ambiguityStats().dupItems > 0);
    earleyParse(stratified, toks('a'));
    assert.equal(ambiguityStats().dupItems, 0);
  });
});
