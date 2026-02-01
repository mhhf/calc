const { Store } = require('../lib/store');
const { Term } = require('../lib/term');
const should = require('chai').should();

describe('Term', () => {
  let store;

  beforeEach(() => {
    store = new Store();
  });

  describe('creation', () => {
    it('should create from hash', () => {
      const hash = store.internString('test');
      const term = Term.fromHash(store, hash);
      term.hash.should.equal(hash);
    });

    it('should create from string', () => {
      const term = Term.fromString(store, 'hello');
      term.isString().should.be.true;
      term.getString().should.equal('hello');
    });

    it('should create from bigint', () => {
      const term = Term.fromBigInt(store, 42n);
      term.isBigInt().should.be.true;
      term.getBigInt().should.equal(42n);
    });

    it('should create struct from Terms', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const term = Term.struct(store, 1, [a, b]);

      term.isStruct().should.be.true;
      term.constructorId().should.equal(1);
      term.arity().should.equal(2);
    });

    it('should create struct from hashes', () => {
      const aHash = store.internString('a');
      const bHash = store.internString('b');
      const term = Term.struct(store, 1, [aHash, bHash]);

      term.isStruct().should.be.true;
      term.childHashes().should.deep.equal([aHash, bHash]);
    });
  });

  describe('type checking', () => {
    it('should identify strings', () => {
      const term = Term.fromString(store, 'x');
      term.isString().should.be.true;
      term.isBigInt().should.be.false;
      term.isStruct().should.be.false;
    });

    it('should identify bigints', () => {
      const term = Term.fromBigInt(store, 123n);
      term.isBigInt().should.be.true;
      term.isString().should.be.false;
      term.isStruct().should.be.false;
    });

    it('should identify structs', () => {
      const term = Term.struct(store, 1, []);
      term.isStruct().should.be.true;
      term.isString().should.be.false;
      term.isBigInt().should.be.false;
    });
  });

  describe('equality', () => {
    it('should be equal for same content', () => {
      const t1 = Term.fromString(store, 'same');
      const t2 = Term.fromString(store, 'same');
      t1.equals(t2).should.be.true;
    });

    it('should not be equal for different content', () => {
      const t1 = Term.fromString(store, 'a');
      const t2 = Term.fromString(store, 'b');
      t1.equals(t2).should.be.false;
    });

    it('should be equal for structurally identical trees', () => {
      const a = Term.fromString(store, 'leaf');
      const t1 = Term.struct(store, 1, [a]);
      const t2 = Term.struct(store, 1, [a]);
      t1.equals(t2).should.be.true;
    });

    it('should return false for non-Term', () => {
      const term = Term.fromString(store, 'x');
      term.equals('x').should.be.false;
      term.equals(null).should.be.false;
    });
  });

  describe('children', () => {
    it('should return children as Terms', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const parent = Term.struct(store, 1, [a, b]);

      const children = parent.children();
      children.should.have.length(2);
      children[0].should.be.instanceOf(Term);
      children[0].equals(a).should.be.true;
      children[1].equals(b).should.be.true;
    });

    it('should return empty array for non-struct', () => {
      const term = Term.fromString(store, 'leaf');
      term.children().should.deep.equal([]);
    });

    it('should return correct arity', () => {
      const term = Term.struct(store, 1, [
        Term.fromString(store, 'a'),
        Term.fromString(store, 'b'),
        Term.fromString(store, 'c'),
      ]);
      term.arity().should.equal(3);
    });
  });

  describe('map', () => {
    it('should transform leaf nodes', () => {
      const term = Term.fromString(store, 'x');
      const mapped = term.map(t => {
        if (t.isString()) {
          return Term.fromString(store, t.getString().toUpperCase());
        }
        return t;
      });
      mapped.getString().should.equal('X');
    });

    it('should transform tree nodes', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const tree = Term.struct(store, 1, [a, b]);

      const mapped = tree.map(t => {
        if (t.isString()) {
          return Term.fromString(store, t.getString().toUpperCase());
        }
        return t;
      });

      mapped.isStruct().should.be.true;
      mapped.children()[0].getString().should.equal('A');
      mapped.children()[1].getString().should.equal('B');
    });

    it('should preserve structure when nothing changes', () => {
      const a = Term.fromString(store, 'a');
      const tree = Term.struct(store, 1, [a]);

      const mapped = tree.map(t => t);
      mapped.hash.should.equal(tree.hash);
    });
  });

  describe('fold', () => {
    it('should accumulate over leaves', () => {
      const term = Term.fromString(store, 'x');
      const result = term.fold((acc, t) => acc + 1, 0);
      result.should.equal(1);
    });

    it('should accumulate over tree', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const tree = Term.struct(store, 1, [a, b]);

      // Count all nodes
      const count = tree.fold((acc, t) => acc + 1, 0);
      count.should.equal(3); // a, b, and the struct
    });

    it('should collect strings', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const tree = Term.struct(store, 1, [a, b]);

      const strings = tree.fold((acc, t) => {
        if (t.isString()) acc.push(t.getString());
        return acc;
      }, []);

      strings.should.deep.equal(['a', 'b']);
    });
  });

  describe('contains', () => {
    it('should find itself', () => {
      const term = Term.fromString(store, 'x');
      term.contains(term.hash).should.be.true;
    });

    it('should find child', () => {
      const child = Term.fromString(store, 'child');
      const parent = Term.struct(store, 1, [child]);
      parent.contains(child.hash).should.be.true;
    });

    it('should find deep child', () => {
      const leaf = Term.fromString(store, 'leaf');
      const inner = Term.struct(store, 1, [leaf]);
      const outer = Term.struct(store, 2, [inner]);
      outer.contains(leaf.hash).should.be.true;
    });

    it('should return false for non-existent', () => {
      const term = Term.fromString(store, 'x');
      const other = Term.fromString(store, 'y');
      term.contains(other.hash).should.be.false;
    });
  });

  describe('toString', () => {
    it('should format string', () => {
      const term = Term.fromString(store, 'hello');
      term.toString().should.include('String');
      term.toString().should.include('hello');
    });

    it('should format bigint', () => {
      const term = Term.fromBigInt(store, 42n);
      term.toString().should.include('BigInt');
      term.toString().should.include('42');
    });

    it('should format struct', () => {
      const a = Term.fromString(store, 'a');
      const term = Term.struct(store, 7, [a]);
      term.toString().should.include('Struct');
      term.toString().should.include('7');
    });
  });
});
