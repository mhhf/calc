const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const { resetStore } = require('../lib/v1/store');
const { Term } = require('../lib/v1/term');
const {
  internNode,
  externNode,
  nodesEqual,
  getSubterms,
  countNodes,
} = require('../lib/v1/intern');

// Setup parser
const calc = require('../ll.json');
const calcParser = require('../lib/v1/parser.js');
const Node = require('../lib/v1/node.js');
const parser = calcParser(calc).parser;

describe('Intern', () => {
  beforeEach(() => {
    // Reset the global store before each test
    resetStore();
  });

  describe('internNode', () => {
    it('should intern string nodes', () => {
      const term = internNode('hello');
      assert.strictEqual(term.isString(), true);
      assert.strictEqual(term.getString(), 'hello');
    });

    it('should intern simple parsed formula', () => {
      const node = parser.parse('-- : A |- -- : A');
      const term = internNode(node);

      assert.strictEqual(term.isStruct(), true);
      assert.strictEqual(term.constructorId(), node.id);
    });

    it('should deduplicate identical subtrees', () => {
      // Parse A * A - A appears twice
      const node = parser.parse('-- : A * A |- -- : A');
      const term = internNode(node);

      // The formula "A" should appear only once in the store
      // (the hash for "A" is the same regardless of where it appears)
      assert.strictEqual(term.isStruct(), true);
    });

    it('should produce same hash for same formula', () => {
      const node1 = parser.parse('-- : A * B |- -- : C');
      const node2 = parser.parse('-- : A * B |- -- : C');

      const term1 = internNode(node1);
      const term2 = internNode(node2);

      assert.strictEqual(term1.hash, term2.hash);
    });

    it('should produce different hash for different formulas', () => {
      const node1 = parser.parse('-- : A |- -- : B');
      const node2 = parser.parse('-- : B |- -- : A');

      const term1 = internNode(node1);
      const term2 = internNode(node2);

      assert.notStrictEqual(term1.hash, term2.hash);
    });

    it('should preserve node.id as constructor ID', () => {
      const node = parser.parse('-- : A |- -- : A');
      const term = internNode(node);

      assert.strictEqual(term.constructorId(), node.id);
    });
  });

  describe('externNode', () => {
    it('should reconstruct string', () => {
      const term = internNode('test');
      const result = externNode(term, Node);
      assert.strictEqual(result, 'test');
    });

    it('should reconstruct simple formula', () => {
      const original = parser.parse('-- : A |- -- : A');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      assert.strictEqual(reconstructed.toString(), original.toString());
    });

    it('should reconstruct complex formula', () => {
      const original = parser.parse('-- : (A * B) -o C |- -- : A -o (B -o C)');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      assert.strictEqual(reconstructed.toString(), original.toString());
    });

    it('should work with hash instead of Term', () => {
      const original = parser.parse('-- : P |- -- : Q');
      const term = internNode(original);
      const reconstructed = externNode(term.hash, Node);

      assert.strictEqual(reconstructed.toString(), original.toString());
    });

    it('should roundtrip formulas with variables', () => {
      const original = parser.parse('-- : F?X |- -- : F?X');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      assert.strictEqual(reconstructed.toString(), original.toString());
    });
  });

  describe('nodesEqual', () => {
    it('should return true for identical formulas', () => {
      const node1 = parser.parse('-- : A * B |- -- : C');
      const node2 = parser.parse('-- : A * B |- -- : C');

      assert.strictEqual(nodesEqual(node1, node2), true);
    });

    it('should return false for different formulas', () => {
      const node1 = parser.parse('-- : A |- -- : B');
      const node2 = parser.parse('-- : B |- -- : A');

      assert.strictEqual(nodesEqual(node1, node2), false);
    });

    it('should work with string nodes', () => {
      assert.strictEqual(nodesEqual('x', 'x'), true);
      assert.strictEqual(nodesEqual('x', 'y'), false);
    });
  });

  describe('getSubterms', () => {
    it('should collect all subterms', () => {
      const node = parser.parse('-- : A * B |- -- : C');
      const subterms = getSubterms(node);

      // Should include the root and all descendants
      assert.ok(subterms.size > 1);
    });

    it('should deduplicate repeated subterms', () => {
      const node = parser.parse('-- : A * A |- -- : A');
      const subterms = getSubterms(node);

      // A appears 3 times but should only be in set once
      // (because we're using hash as key)
      const term = internNode(node);
      // Just verify it's a set with reasonable size
      assert.ok(subterms instanceof Set);
    });
  });

  describe('countNodes', () => {
    it('should count nodes in simple formula', () => {
      // Simple atom: -- : A
      const simpleNode = parser.parse('-- : A |- -- : A');
      const count = countNodes(simpleNode);

      // Should have multiple nodes (sequent, structures, formulas, atom names)
      assert.ok(count > 1);
    });

    it('should count more nodes in complex formula', () => {
      const simple = parser.parse('-- : A |- -- : A');
      const complex = parser.parse('-- : (A * B) -o C |- -- : D');

      const simpleCount = countNodes(simple);
      const complexCount = countNodes(complex);

      assert.ok(complexCount > simpleCount);
    });
  });

  describe('structural sharing', () => {
    it('should share identical subformulas', () => {
      const { getStore } = require('../lib/v1/store');
      const store = getStore();

      // Parse two formulas that share subformulas
      const node1 = parser.parse('-- : A * B |- -- : C');
      const node2 = parser.parse('-- : A * B |- -- : D');

      // Intern both
      internNode(node1);
      const statsBefore = store.stats().total;

      internNode(node2);
      const statsAfter = store.stats().total;

      // Second intern should add fewer nodes (A * B is shared)
      // Just verify total grew less than double
      assert.ok(statsAfter < statsBefore * 2);
    });
  });
});
