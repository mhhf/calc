/**
 * Regression test for loli_match handler in check-term.js (C2 fix).
 *
 * Verifies: a guided-mode proof term containing loli_match validates
 * through check-term.js without returning 'unknown rule'.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const Seq = require('../../lib/kernel/sequent');
const { createChecker } = require('../../lib/prover/check-term');

describe('check-term loli_match (C2)', () => {
  let checker;

  before(async () => {
    Store.clear();
    const calculus = require('../../lib/calculus');
    const calc = await calculus.loadILL();
    checker = createChecker(calc);
  });

  it('loli_match handler exists — does not return unknown rule', () => {
    // Build: loli(A, monad(B)) in delta
    const atomA = Store.put('atom', ['test_a']);
    const atomB = Store.put('atom', ['test_b']);
    const monadB = Store.put('monad', [atomB]);
    const loliType = Store.put('loli', [atomA, monadB]);

    // Build a minimal loli_match proof term
    const term = {
      rule: 'loli_match',
      principal: loliType,
      groundAntecedent: atomA,
      groundFacts: [atomB],
      subterms: [
        { rule: 'id', principal: atomA, subterms: [] },
        { rule: 'id', principal: atomB, subterms: [] },
      ],
    };

    // Build sequent: loliType, atomA |- atomB
    const seq = Seq.fromArrays([loliType, atomA], [], atomB);
    const result = checker.check(term, seq);
    if (!result.valid) {
      assert.ok(!result.error.includes('unknown rule'),
        `Should not fail with 'unknown rule', got: ${result.error}`);
    }
  });

  it('loli_match rejects missing principal', () => {
    const term = {
      rule: 'loli_match',
      principal: null,
      groundAntecedent: Store.put('atom', ['a']),
      groundFacts: [Store.put('atom', ['b'])],
      subterms: [
        { rule: 'id', principal: null, subterms: [] },
        { rule: 'id', principal: null, subterms: [] },
      ],
    };

    // Empty sequent — the checker should fail before context check
    const seq = Seq.fromArrays([], [], Store.put('atom', ['b']));
    const result = checker.check(term, seq);
    assert.equal(result.valid, false);
    assert.ok(result.error.includes('no principal'));
  });
});
