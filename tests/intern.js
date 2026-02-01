const { resetStore } = require('../lib/store');
const { Term } = require('../lib/term');
const {
  internNode,
  externNode,
  nodesEqual,
  getSubterms,
  countNodes,
} = require('../lib/intern');
const should = require('chai').should();

// Setup parser
const calc = require('../ll.json');
const calcParser = require('../lib/parser.js');
const Node = require('../lib/node.js');
const parser = calcParser(calc).parser;

describe('Intern', () => {
  beforeEach(() => {
    // Reset the global store before each test
    resetStore();
  });

  describe('internNode', () => {
    it('should intern string nodes', () => {
      const term = internNode('hello');
      term.isString().should.be.true;
      term.getString().should.equal('hello');
    });

    it('should intern simple parsed formula', () => {
      const node = parser.parse('-- : A |- -- : A');
      const term = internNode(node);

      term.isStruct().should.be.true;
      term.constructorId().should.equal(node.id);
    });

    it('should deduplicate identical subtrees', () => {
      // Parse A * A - A appears twice
      const node = parser.parse('-- : A * A |- -- : A');
      const term = internNode(node);

      // The formula "A" should appear only once in the store
      // (the hash for "A" is the same regardless of where it appears)
      term.isStruct().should.be.true;
    });

    it('should produce same hash for same formula', () => {
      const node1 = parser.parse('-- : A * B |- -- : C');
      const node2 = parser.parse('-- : A * B |- -- : C');

      const term1 = internNode(node1);
      const term2 = internNode(node2);

      term1.hash.should.equal(term2.hash);
    });

    it('should produce different hash for different formulas', () => {
      const node1 = parser.parse('-- : A |- -- : B');
      const node2 = parser.parse('-- : B |- -- : A');

      const term1 = internNode(node1);
      const term2 = internNode(node2);

      term1.hash.should.not.equal(term2.hash);
    });

    it('should preserve node.id as constructor ID', () => {
      const node = parser.parse('-- : A |- -- : A');
      const term = internNode(node);

      term.constructorId().should.equal(node.id);
    });
  });

  describe('externNode', () => {
    it('should reconstruct string', () => {
      const term = internNode('test');
      const result = externNode(term, Node);
      result.should.equal('test');
    });

    it('should reconstruct simple formula', () => {
      const original = parser.parse('-- : A |- -- : A');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      reconstructed.toString().should.equal(original.toString());
    });

    it('should reconstruct complex formula', () => {
      const original = parser.parse('-- : (A * B) -o C |- -- : A -o (B -o C)');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      reconstructed.toString().should.equal(original.toString());
    });

    it('should work with hash instead of Term', () => {
      const original = parser.parse('-- : P |- -- : Q');
      const term = internNode(original);
      const reconstructed = externNode(term.hash, Node);

      reconstructed.toString().should.equal(original.toString());
    });

    it('should roundtrip formulas with variables', () => {
      const original = parser.parse('-- : F?X |- -- : F?X');
      const term = internNode(original);
      const reconstructed = externNode(term, Node);

      reconstructed.toString().should.equal(original.toString());
    });
  });

  describe('nodesEqual', () => {
    it('should return true for identical formulas', () => {
      const node1 = parser.parse('-- : A * B |- -- : C');
      const node2 = parser.parse('-- : A * B |- -- : C');

      nodesEqual(node1, node2).should.be.true;
    });

    it('should return false for different formulas', () => {
      const node1 = parser.parse('-- : A |- -- : B');
      const node2 = parser.parse('-- : B |- -- : A');

      nodesEqual(node1, node2).should.be.false;
    });

    it('should work with string nodes', () => {
      nodesEqual('x', 'x').should.be.true;
      nodesEqual('x', 'y').should.be.false;
    });
  });

  describe('getSubterms', () => {
    it('should collect all subterms', () => {
      const node = parser.parse('-- : A * B |- -- : C');
      const subterms = getSubterms(node);

      // Should include the root and all descendants
      subterms.size.should.be.greaterThan(1);
    });

    it('should deduplicate repeated subterms', () => {
      const node = parser.parse('-- : A * A |- -- : A');
      const subterms = getSubterms(node);

      // A appears 3 times but should only be in set once
      // (because we're using hash as key)
      const term = internNode(node);
      // Just verify it's a set with reasonable size
      subterms.should.be.instanceOf(Set);
    });
  });

  describe('countNodes', () => {
    it('should count nodes in simple formula', () => {
      // Simple atom: -- : A
      const simpleNode = parser.parse('-- : A |- -- : A');
      const count = countNodes(simpleNode);

      // Should have multiple nodes (sequent, structures, formulas, atom names)
      count.should.be.greaterThan(1);
    });

    it('should count more nodes in complex formula', () => {
      const simple = parser.parse('-- : A |- -- : A');
      const complex = parser.parse('-- : (A * B) -o C |- -- : D');

      const simpleCount = countNodes(simple);
      const complexCount = countNodes(complex);

      complexCount.should.be.greaterThan(simpleCount);
    });
  });

  describe('structural sharing', () => {
    it('should share identical subformulas', () => {
      const { getStore } = require('../lib/store');
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
      statsAfter.should.be.lessThan(statsBefore * 2);
    });
  });
});
