const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const { Store } = require('../lib/store');
const { Term } = require('../lib/term');

describe('Term', () => {
  let store;

  beforeEach(() => {
    store = new Store();
  });

  describe('creation', () => {
    it('should create from hash', () => {
      const hash = store.internString('test');
      const term = Term.fromHash(store, hash);
      assert.strictEqual(term.hash, hash);
    });

    it('should create from string', () => {
      const term = Term.fromString(store, 'hello');
      assert.strictEqual(term.isString(), true);
      assert.strictEqual(term.getString(), 'hello');
    });

    it('should create from bigint', () => {
      const term = Term.fromBigInt(store, 42n);
      assert.strictEqual(term.isBigInt(), true);
      assert.strictEqual(term.getBigInt(), 42n);
    });

    it('should create struct from Terms', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const term = Term.struct(store, 1, [a, b]);

      assert.strictEqual(term.isStruct(), true);
      assert.strictEqual(term.constructorId(), 1);
      assert.strictEqual(term.arity(), 2);
    });

    it('should create struct from hashes', () => {
      const aHash = store.internString('a');
      const bHash = store.internString('b');
      const term = Term.struct(store, 1, [aHash, bHash]);

      assert.strictEqual(term.isStruct(), true);
      assert.deepStrictEqual(term.childHashes(), [aHash, bHash]);
    });
  });

  describe('type checking', () => {
    it('should identify strings', () => {
      const term = Term.fromString(store, 'x');
      assert.strictEqual(term.isString(), true);
      assert.strictEqual(term.isBigInt(), false);
      assert.strictEqual(term.isStruct(), false);
    });

    it('should identify bigints', () => {
      const term = Term.fromBigInt(store, 123n);
      assert.strictEqual(term.isBigInt(), true);
      assert.strictEqual(term.isString(), false);
      assert.strictEqual(term.isStruct(), false);
    });

    it('should identify structs', () => {
      const term = Term.struct(store, 1, []);
      assert.strictEqual(term.isStruct(), true);
      assert.strictEqual(term.isString(), false);
      assert.strictEqual(term.isBigInt(), false);
    });
  });

  describe('equality', () => {
    it('should be equal for same content', () => {
      const t1 = Term.fromString(store, 'same');
      const t2 = Term.fromString(store, 'same');
      assert.strictEqual(t1.equals(t2), true);
    });

    it('should not be equal for different content', () => {
      const t1 = Term.fromString(store, 'a');
      const t2 = Term.fromString(store, 'b');
      assert.strictEqual(t1.equals(t2), false);
    });

    it('should be equal for structurally identical trees', () => {
      const a = Term.fromString(store, 'leaf');
      const t1 = Term.struct(store, 1, [a]);
      const t2 = Term.struct(store, 1, [a]);
      assert.strictEqual(t1.equals(t2), true);
    });

    it('should return false for non-Term', () => {
      const term = Term.fromString(store, 'x');
      assert.strictEqual(term.equals('x'), false);
      assert.strictEqual(term.equals(null), false);
    });
  });

  describe('children', () => {
    it('should return children as Terms', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const parent = Term.struct(store, 1, [a, b]);

      const children = parent.children();
      assert.strictEqual(children.length, 2);
      assert.ok(children[0] instanceof Term);
      assert.strictEqual(children[0].equals(a), true);
      assert.strictEqual(children[1].equals(b), true);
    });

    it('should return empty array for non-struct', () => {
      const term = Term.fromString(store, 'leaf');
      assert.deepStrictEqual(term.children(), []);
    });

    it('should return correct arity', () => {
      const term = Term.struct(store, 1, [
        Term.fromString(store, 'a'),
        Term.fromString(store, 'b'),
        Term.fromString(store, 'c'),
      ]);
      assert.strictEqual(term.arity(), 3);
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
      assert.strictEqual(mapped.getString(), 'X');
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

      assert.strictEqual(mapped.isStruct(), true);
      assert.strictEqual(mapped.children()[0].getString(), 'A');
      assert.strictEqual(mapped.children()[1].getString(), 'B');
    });

    it('should preserve structure when nothing changes', () => {
      const a = Term.fromString(store, 'a');
      const tree = Term.struct(store, 1, [a]);

      const mapped = tree.map(t => t);
      assert.strictEqual(mapped.hash, tree.hash);
    });
  });

  describe('fold', () => {
    it('should accumulate over leaves', () => {
      const term = Term.fromString(store, 'x');
      const result = term.fold((acc, t) => acc + 1, 0);
      assert.strictEqual(result, 1);
    });

    it('should accumulate over tree', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const tree = Term.struct(store, 1, [a, b]);

      // Count all nodes
      const count = tree.fold((acc, t) => acc + 1, 0);
      assert.strictEqual(count, 3); // a, b, and the struct
    });

    it('should collect strings', () => {
      const a = Term.fromString(store, 'a');
      const b = Term.fromString(store, 'b');
      const tree = Term.struct(store, 1, [a, b]);

      const strings = tree.fold((acc, t) => {
        if (t.isString()) acc.push(t.getString());
        return acc;
      }, []);

      assert.deepStrictEqual(strings, ['a', 'b']);
    });
  });

  describe('contains', () => {
    it('should find itself', () => {
      const term = Term.fromString(store, 'x');
      assert.strictEqual(term.contains(term.hash), true);
    });

    it('should find child', () => {
      const child = Term.fromString(store, 'child');
      const parent = Term.struct(store, 1, [child]);
      assert.strictEqual(parent.contains(child.hash), true);
    });

    it('should find deep child', () => {
      const leaf = Term.fromString(store, 'leaf');
      const inner = Term.struct(store, 1, [leaf]);
      const outer = Term.struct(store, 2, [inner]);
      assert.strictEqual(outer.contains(leaf.hash), true);
    });

    it('should return false for non-existent', () => {
      const term = Term.fromString(store, 'x');
      const other = Term.fromString(store, 'y');
      assert.strictEqual(term.contains(other.hash), false);
    });
  });

  describe('toString', () => {
    it('should format string', () => {
      const term = Term.fromString(store, 'hello');
      assert.ok(term.toString().includes('String'));
      assert.ok(term.toString().includes('hello'));
    });

    it('should format bigint', () => {
      const term = Term.fromBigInt(store, 42n);
      assert.ok(term.toString().includes('BigInt'));
      assert.ok(term.toString().includes('42'));
    });

    it('should format struct', () => {
      const a = Term.fromString(store, 'a');
      const term = Term.struct(store, 7, [a]);
      assert.ok(term.toString().includes('Struct'));
      assert.ok(term.toString().includes('7'));
    });
  });
});
