/**
 * Direct tests for calculus/modes.js
 *
 * Validates monad_r/monad_l descriptor structure.
 */
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { monadRules } from '../lib/calculus/modes.js';
describe('monadRules', () => {
  const rules = monadRules();

  describe('monad_r', () => {
    it('has correct name and descriptor connective', () => {
      assert.equal(rules.monad_r.name, 'monad_r');
      assert.equal(rules.monad_r.descriptor.connective, 'monad');
    });

    it('is a right rule', () => {
      assert.equal(rules.monad_r.descriptor.side, 'r');
    });

    it('has arity 2 (graded monad, D6 merge-back)', () => {
      assert.equal(rules.monad_r.descriptor.arity, 2);
    });

    it('is invertible (negative polarity)', () => {
      assert.equal(rules.monad_r.invertible, true);
    });

    it('has zero premises (mode shift)', () => {
      assert.equal(rules.monad_r.numPremises, 0);
      assert.deepEqual(rules.monad_r.descriptor.premises, []);
    });

    it('has modeShift flag', () => {
      assert.equal(rules.monad_r.descriptor.modeShift, true);
    });

    it('contextFlow is axiom', () => {
      assert.equal(rules.monad_r.descriptor.contextFlow, 'axiom');
    });
  });

  describe('monad_l', () => {
    it('has correct name and descriptor connective', () => {
      assert.equal(rules.monad_l.name, 'monad_l');
      assert.equal(rules.monad_l.descriptor.connective, 'monad');
    });

    it('is a left rule', () => {
      assert.equal(rules.monad_l.descriptor.side, 'l');
    });

    it('is NOT invertible', () => {
      assert.equal(rules.monad_l.invertible, false);
    });

    it('has one premise with the body child (bodyIdx 1)', () => {
      assert.equal(rules.monad_l.numPremises, 1);
      assert.deepEqual(rules.monad_l.descriptor.premises, [{ linear: [1] }]);
    });

    it('requires succedent to be monad (sticky)', () => {
      assert.equal(rules.monad_l.descriptor.requiresSuccedentTag, 'monad');
    });

    it('contextFlow is preserved', () => {
      assert.equal(rules.monad_l.descriptor.contextFlow, 'preserved');
    });
  });
});
