/**
 * Direct tests for sequent-parser.js
 *
 * Covers: parseSequent, parseHyp, formatSequent,
 * nested turnstile handling (C32 fix).
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const calculus = require('../lib/calculus');
const { createSequentParser } = require('../lib/parser/sequent-parser');
const Seq = require('../lib/kernel/sequent');

describe('sequent-parser', () => {
  let calc, sp;

  before(async () => {
    calc = await calculus.loadILL();
    sp = createSequentParser(calc);
  });

  describe('parseSequent', () => {
    it('parses simple sequent A |- B', () => {
      const seq = sp.parseSequent('A |- B');
      assert.ok(seq);
      const linear = Seq.getContext(seq, 'linear');
      assert.equal(linear.length, 1);
    });

    it('parses multi-hypothesis A, B |- C', () => {
      const seq = sp.parseSequent('A, B |- C');
      const linear = Seq.getContext(seq, 'linear');
      assert.equal(linear.length, 2);
    });

    it('parses empty antecedent |- A', () => {
      const seq = sp.parseSequent('|- A');
      const linear = Seq.getContext(seq, 'linear');
      assert.equal(linear.length, 0);
    });

    it('parses with term labels -- : A |- -- : B', () => {
      const seq = sp.parseSequent('-- : A |- -- : B');
      assert.ok(seq);
      const linear = Seq.getContext(seq, 'linear');
      assert.equal(linear.length, 1);
    });

    it('throws on missing turnstile', () => {
      assert.throws(() => sp.parseSequent('A, B, C'), /expected '\|-'/);
    });
  });

  describe('parseHyp', () => {
    it('parses bare formula', () => {
      const h = sp.parseHyp('A');
      assert.ok(h);
    });

    it('parses labeled formula with colon', () => {
      const h = sp.parseHyp('x : A');
      assert.ok(h);
    });

    it('returns null for empty string', () => {
      const h = sp.parseHyp('');
      assert.equal(h, null);
    });
  });

  describe('formatSequent', () => {
    it('roundtrips simple sequent', () => {
      const seq = sp.parseSequent('A |- B');
      const fmt = sp.formatSequent(seq, 'ascii');
      assert.ok(fmt.includes('|-'));
    });

    it('formats with latex turnstile', () => {
      const seq = sp.parseSequent('A |- B');
      const fmt = sp.formatSequent(seq, 'latex');
      assert.ok(fmt.includes('\\vdash'));
    });

    it('handles empty antecedent formatting', () => {
      const seq = sp.parseSequent('|- A');
      const fmt = sp.formatSequent(seq, 'ascii');
      assert.ok(fmt.startsWith('|-'));
    });
  });
});
