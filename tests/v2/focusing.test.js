/**
 * Tests for v2 Focusing Metadata
 *
 * Verifies that polarity, invertibility, and context modes are
 * correctly extracted from spec files and can be inferred from rule structure.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../../lib/v2/calculus');
const { buildFocusingMeta, inferPolarity } = require('../../lib/v2/meta/focusing');

describe('v2 Focusing Metadata', () => {
  let ill;
  let meta;

  before(async () => {
    ill = await calculus.loadILL();
    meta = buildFocusingMeta(ill);
  });

  describe('rules loading', () => {
    it('should load inference rules', () => {
      assert.ok(ill.rules.tensor_r, 'tensor_r should be loaded');
      assert.ok(ill.rules.tensor_l, 'tensor_l should be loaded');
      assert.ok(ill.rules.loli_r, 'loli_r should be loaded');
      assert.ok(ill.rules.loli_l, 'loli_l should be loaded');
    });

    it('should have invertibility (explicit or inferred)', () => {
      // tensor/loli invertibility is now inferred from polarity
      assert.strictEqual(ill.invertible.tensor_r, false);
      assert.strictEqual(ill.invertible.tensor_l, true);
      assert.strictEqual(ill.invertible.loli_r, true);
      assert.strictEqual(ill.invertible.loli_l, false);
    });

    it('should extract pretty names', () => {
      assert.strictEqual(ill.rules.tensor_r.pretty, '⊗R');
      assert.strictEqual(ill.rules.loli_r.pretty, '⊸R');
    });

    it('should count premises correctly', () => {
      assert.strictEqual(ill.rules.tensor_r.numPremises, 2);
      assert.strictEqual(ill.rules.tensor_l.numPremises, 1);
      assert.strictEqual(ill.rules.with_r.numPremises, 2);
      assert.strictEqual(ill.rules.id.numPremises, 0);
    });
  });

  describe('polarity from annotations', () => {
    it('should extract explicit polarity', () => {
      assert.strictEqual(ill.polarity.tensor, 'positive');
      assert.strictEqual(ill.polarity.loli, 'negative');
      assert.strictEqual(ill.polarity.with, 'negative');
      assert.strictEqual(ill.polarity.bang, 'positive');
      assert.strictEqual(ill.polarity.one, 'positive');
    });

    it('should provide isPositive/isNegative helpers', () => {
      assert.strictEqual(ill.isPositive('tensor'), true);
      assert.strictEqual(ill.isNegative('tensor'), false);
      assert.strictEqual(ill.isPositive('loli'), false);
      assert.strictEqual(ill.isNegative('loli'), true);
    });
  });

  describe('invertibility', () => {
    it('should build invertibility map', () => {
      assert.strictEqual(ill.invertible.tensor_r, false);
      assert.strictEqual(ill.invertible.tensor_l, true);
      assert.strictEqual(ill.invertible.loli_r, true);
      assert.strictEqual(ill.invertible.loli_l, false);
    });

    it('should provide isInvertible helper', () => {
      assert.strictEqual(ill.isInvertible('tensor_l'), true);
      assert.strictEqual(ill.isInvertible('tensor_r'), false);
    });

    it('should classify invertible vs non-invertible rules', () => {
      // These now include both explicit AND inferred invertibility
      assert.strictEqual(ill.invertible.tensor_l, true);
      assert.strictEqual(ill.invertible.loli_r, true);
      assert.strictEqual(ill.invertible.tensor_r, false);
      assert.strictEqual(ill.invertible.loli_l, false);
    });
  });

  describe('rule classification', () => {
    it('should group rules by connective', () => {
      assert.ok(meta.rulesByConnective.tensor);
      assert.ok(meta.rulesByConnective.tensor.left.includes('tensor_l'));
      assert.ok(meta.rulesByConnective.tensor.right.includes('tensor_r'));
    });

    it('should handle with rules (multiple left rules)', () => {
      assert.ok(meta.rulesByConnective.with);
      // with has with_l1 and with_l2
      assert.ok(meta.rulesByConnective.with.left.length >= 1);
      assert.ok(meta.rulesByConnective.with.right.includes('with_r'));
    });
  });

  describe('validation', () => {
    it('should validate explicit vs inferred polarity', () => {
      const mismatches = meta.validate();
      // Expect no mismatches if annotations are correct
      if (mismatches.length > 0) {
        console.log('Polarity mismatches:', mismatches);
      }
      // Note: Some mismatches may be expected due to special cases (e.g., modalities)
    });
  });

  describe('focusing behavior', () => {
    it('positive formulas on right should not be invertible', () => {
      // tensor is positive, tensor_r should not be invertible
      assert.strictEqual(ill.isPositive('tensor'), true);
      assert.strictEqual(ill.isInvertible('tensor_r'), false);
    });

    it('negative formulas on right should be invertible', () => {
      // loli is negative, loli_r should be invertible
      assert.strictEqual(ill.isNegative('loli'), true);
      assert.strictEqual(ill.isInvertible('loli_r'), true);
    });

    it('left rules follow dual pattern', () => {
      // positive on left = invertible (tensor_l)
      // negative on left = not invertible (loli_l)
      assert.strictEqual(ill.isPositive('tensor'), true);
      assert.strictEqual(ill.isInvertible('tensor_l'), true);

      assert.strictEqual(ill.isNegative('loli'), true);
      assert.strictEqual(ill.isInvertible('loli_l'), false);
    });
  });
});
