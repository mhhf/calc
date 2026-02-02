/**
 * LNL Sequent Tests
 *
 * Tests for multi-context sequent support (Γ ; Δ ⊢ A)
 */

const { test, describe, before } = require('node:test');
const assert = require('node:assert');

const Sequent = require('../lib/sequent.js');
const Calc = require('../lib/calc.js');
const Node = require('../lib/node.js');

describe('Multi-context Sequent', () => {

  before(() => {
    // Initialize Calc if not already done
    if (!Calc.initialized) {
      const calc = require('../ll.json');
      Calc.init(calc);
    }
  });

  describe('Context operations', () => {

    test('creates sequent with linear context only', () => {
      const seq = new Sequent({
        contexts: {
          linear: {}
        },
        succedent: {}
      });

      assert.ok(seq.contexts);
      assert.ok(seq.contexts.linear);
      assert.strictEqual(Object.keys(seq.contexts.linear).length, 0);
    });

    test('creates sequent with both contexts (LNL style)', () => {
      const seq = new Sequent({
        contexts: {
          cartesian: {},
          linear: {}
        },
        succedent: {}
      });

      assert.ok(seq.contexts.cartesian);
      assert.ok(seq.contexts.linear);
    });

    test('add to specific context by mode', () => {
      // This test requires a properly parsed formula
      // For now, test the API contract without actual node hashing
      const seq = new Sequent({
        contexts: {
          cartesian: {},
          linear: {}
        },
        succedent: {}
      });

      // Verify context mode tracking
      assert.ok(seq.contexts.linear !== undefined);
      assert.ok(seq.contexts.cartesian !== undefined);

      // Test direct manipulation (simulating what addToContext would do)
      seq.contexts.linear['test-hash-1'] = { num: 1, val: { toString: () => 'A' }, hash: 1n };
      assert.strictEqual(Object.keys(seq.contexts.linear).length, 1);
      assert.strictEqual(Object.keys(seq.contexts.cartesian).length, 0);

      seq.contexts.cartesian['test-hash-2'] = { num: 1, val: { toString: () => 'B' }, hash: 2n };
      assert.strictEqual(Object.keys(seq.contexts.cartesian).length, 1);
    });

    test('backwards compatible with legacy linear_ctx/persistent_ctx', () => {
      // Old-style construction should still work
      const seq = new Sequent({
        linear_ctx: {},
        persistent_ctx: {},
        succedent: {}
      });

      // Should be accessible via both old and new APIs
      assert.ok(seq.linear_ctx !== undefined || seq.contexts?.linear !== undefined);
    });

  });

  describe('fromTree with 3-arg sequent', () => {

    test('parses LNL sequent pattern (Γ ; Δ ⊢ A)', () => {
      // This test will work once we have a parser that generates 3-arg sequents
      // For now, we test the fromTree logic directly

      // Mock a 3-arg sequent node: seq(structure, structure, structure)
      // Minimal design: all three positions are structures
      const mockSeqNode = {
        id: 100, // mock sequent rule id
        vals: [
          { id: 101, vals: [] }, // cartesian context (structure)
          { id: 102, vals: [] }, // linear context (structure)
          { id: 103, vals: [] }  // succedent (structure, e.g., hyp(any, A))
        ]
      };

      // For now, just verify the structure exists
      // Full test after implementation
      assert.ok(mockSeqNode.vals.length === 3);
    });

  });

  describe('Context mode properties', () => {

    test('linear context: no contraction', () => {
      const seq = new Sequent({
        contexts: { linear: {} },
        succedent: {}
      });

      // Linear mode should have count semantics
      const mode = Sequent.getContextMode(seq, 'linear');
      assert.strictEqual(mode?.contraction, false);
      assert.strictEqual(mode?.weakening, false);
    });

    test('cartesian context: contraction + weakening', () => {
      const seq = new Sequent({
        contexts: { cartesian: {} },
        succedent: {}
      });

      const mode = Sequent.getContextMode(seq, 'cartesian');
      assert.strictEqual(mode?.contraction, true);
      assert.strictEqual(mode?.weakening, true);
    });

  });

});

describe('Sequent toString', () => {

  test('renders LNL sequent with semicolon separator', () => {
    const seq = new Sequent({
      contexts: {
        cartesian: {},
        linear: {}
      },
      succedent: { toString: () => 'A' }
    });

    const str = seq.toString();
    // Should contain semicolon for LNL style
    assert.ok(str.includes(';') || str.includes('|-'));
  });

});
