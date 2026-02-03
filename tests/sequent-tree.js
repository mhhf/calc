/**
 * TreeSequent Tests
 *
 * Tests for the generic tree-based sequent representation.
 */

const { test, describe } = require('node:test');
const assert = require('node:assert');

const { TreeSequent, LNLTreeSequent, computeHash } = require('../lib/v1/sequent-tree.js');

// Mock node for testing
function mockNode(id, vals = [], str = null) {
  return {
    id,
    vals,
    copy: () => mockNode(id, vals.map(v => v?.copy?.() || v), str),
    toString: () => str || `node_${id}`
  };
}

describe('TreeSequent - Generic', () => {

  test('creates empty sequent', () => {
    const seq = new TreeSequent();
    assert.strictEqual(seq.antecedent, null);
    assert.strictEqual(seq.succedent, null);
  });

  test('creates sequent with antecedent and succedent', () => {
    const ant = mockNode(1, [], 'A, B');
    const succ = mockNode(2, [], 'C');

    const seq = new TreeSequent({
      antecedent: ant,
      succedent: succ
    });

    assert.ok(seq.antecedent);
    assert.ok(seq.succedent);
    assert.strictEqual(seq.toString(), 'A, B |- C');
  });

  test('computes hash', () => {
    const ant = mockNode(1, [], 'A');
    const succ = mockNode(2, [], 'B');

    const seq = new TreeSequent({
      antecedent: ant,
      succedent: succ
    });

    const hash = seq.getHash();
    assert.ok(hash !== null);
    assert.ok(typeof hash === 'bigint' || typeof hash === 'number');
  });

  test('hash is cached', () => {
    const seq = new TreeSequent({
      antecedent: mockNode(1),
      succedent: mockNode(2)
    });

    const hash1 = seq.getHash();
    const hash2 = seq.getHash();
    assert.strictEqual(hash1, hash2);
  });

  test('equal sequents have same hash', () => {
    const ant1 = mockNode(1, [], 'A');
    const succ1 = mockNode(2, [], 'B');
    const ant2 = mockNode(1, [], 'A');
    const succ2 = mockNode(2, [], 'B');

    const seq1 = new TreeSequent({ antecedent: ant1, succedent: succ1 });
    const seq2 = new TreeSequent({ antecedent: ant2, succedent: succ2 });

    assert.strictEqual(seq1.getHash(), seq2.getHash());
    assert.ok(seq1.equals(seq2));
  });

  test('different sequents have different hash', () => {
    const seq1 = new TreeSequent({
      antecedent: mockNode(1),
      succedent: mockNode(2)
    });
    const seq2 = new TreeSequent({
      antecedent: mockNode(3),
      succedent: mockNode(4)
    });

    assert.notStrictEqual(seq1.getHash(), seq2.getHash());
    assert.ok(!seq1.equals(seq2));
  });

  test('copy creates independent copy', () => {
    const ant = mockNode(1, [], 'A');
    const succ = mockNode(2, [], 'B');

    const seq1 = new TreeSequent({ antecedent: ant, succedent: succ });
    const seq2 = seq1.copy();

    assert.ok(seq1.equals(seq2));
    assert.notStrictEqual(seq1, seq2);
    assert.notStrictEqual(seq1.antecedent, seq2.antecedent);
  });

  test('toString renders correctly', () => {
    const seq = new TreeSequent({
      antecedent: mockNode(1, [], 'X'),
      succedent: mockNode(2, [], 'Y')
    });

    assert.strictEqual(seq.toString(), 'X |- Y');
  });

  test('toString with latex style', () => {
    const seq = new TreeSequent({
      antecedent: mockNode(1, [], 'X'),
      succedent: mockNode(2, [], 'Y')
    });

    assert.strictEqual(seq.toString({ style: 'latex' }), 'X \\vdash Y');
  });

});

describe('LNLTreeSequent - LNL Family', () => {

  test('creates LNL sequent with both contexts', () => {
    const cart = mockNode(1, [], 'G');
    const lin = mockNode(2, [], 'D');
    const succ = mockNode(3, [], 'A');

    const seq = new LNLTreeSequent({
      cartesian: cart,
      linear: lin,
      succedent: succ
    });

    assert.ok(seq.cartesian);
    assert.ok(seq.linear);
    assert.ok(seq.succedent);
  });

  test('inherits from TreeSequent', () => {
    const seq = new LNLTreeSequent({});
    assert.ok(seq instanceof TreeSequent);
  });

  test('toString renders LNL style (Gamma ; Delta |- A)', () => {
    const seq = new LNLTreeSequent({
      cartesian: mockNode(1, [], 'G'),
      linear: mockNode(2, [], 'D'),
      succedent: mockNode(3, [], 'A')
    });

    const str = seq.toString();
    assert.ok(str.includes(';'), `Expected semicolon in: ${str}`);
    assert.ok(str.includes('|-'), `Expected turnstile in: ${str}`);
  });

  test('toString omits empty cartesian context', () => {
    const seq = new LNLTreeSequent({
      cartesian: mockNode(1, [], '·'),
      linear: mockNode(2, [], 'D'),
      succedent: mockNode(3, [], 'A')
    });

    const str = seq.toString();
    // When cartesian is empty (·), should just show D |- A
    assert.ok(str.includes('|-'));
    assert.ok(!str.includes(';'));
  });

  test('computes hash from all three parts', () => {
    const seq1 = new LNLTreeSequent({
      cartesian: mockNode(1),
      linear: mockNode(2),
      succedent: mockNode(3)
    });

    const seq2 = new LNLTreeSequent({
      cartesian: mockNode(1),
      linear: mockNode(2),
      succedent: mockNode(4) // Different succedent
    });

    assert.notStrictEqual(seq1.getHash(), seq2.getHash());
  });

  test('copy preserves all fields', () => {
    const seq1 = new LNLTreeSequent({
      cartesian: mockNode(1, [], 'G'),
      linear: mockNode(2, [], 'D'),
      succedent: mockNode(3, [], 'A')
    });

    const seq2 = seq1.copy();

    assert.ok(seq1.equals(seq2));
    assert.notStrictEqual(seq1.cartesian, seq2.cartesian);
    assert.notStrictEqual(seq1.linear, seq2.linear);
    assert.notStrictEqual(seq1.succedent, seq2.succedent);
  });

});

describe('TreeSequent.fromTree', () => {

  test('parses 2-arg sequent tree', () => {
    const tree = {
      vals: [
        mockNode(1, [], 'Ctx'),
        mockNode(2, [], 'Formula')
      ]
    };

    const seq = TreeSequent.fromTree(tree, {});

    assert.ok(seq instanceof TreeSequent);
    assert.ok(!(seq instanceof LNLTreeSequent));
    assert.ok(seq.antecedent);
    assert.ok(seq.succedent);
  });

  test('parses 3-arg sequent tree as LNLTreeSequent', () => {
    const tree = {
      vals: [
        mockNode(1, [], 'CartCtx'),
        mockNode(2, [], 'LinCtx'),
        mockNode(3, [], 'Formula')
      ]
    };

    const seq = TreeSequent.fromTree(tree, {});

    assert.ok(seq instanceof LNLTreeSequent);
    assert.ok(seq.cartesian);
    assert.ok(seq.linear);
    assert.ok(seq.succedent);
  });

  test('throws for unknown arity', () => {
    const tree = { vals: [mockNode(1)] }; // 1-arg

    assert.throws(() => {
      TreeSequent.fromTree(tree, {});
    }, /Unknown sequent arity/);
  });

});

describe('TreeSequent.isDisplayed', () => {

  test('returns true when formula is exactly the antecedent', () => {
    const formula = mockNode(1, [], 'A');
    const seq = new TreeSequent({
      antecedent: formula,
      succedent: mockNode(2, [], 'B')
    });

    assert.ok(TreeSequent.isDisplayed(seq, formula));
  });

  test('returns true when formula is exactly the succedent', () => {
    const formula = mockNode(2, [], 'B');
    const seq = new TreeSequent({
      antecedent: mockNode(1, [], 'A'),
      succedent: formula
    });

    assert.ok(TreeSequent.isDisplayed(seq, formula));
  });

  test('returns false when formula is nested', () => {
    const formula = mockNode(1, [], 'A');
    const nested = mockNode(3, [formula, mockNode(2)], 'A, B');
    const seq = new TreeSequent({
      antecedent: nested,
      succedent: mockNode(4, [], 'C')
    });

    // A is nested inside (A, B), not displayed
    assert.ok(!TreeSequent.isDisplayed(seq, formula));
  });

});
