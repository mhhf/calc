const { Store, ScopedStore, NodeType } = require('../lib/store');
const should = require('chai').should();

describe('Store', () => {
  let store;

  beforeEach(() => {
    store = new Store();
  });

  describe('string interning', () => {
    it('should intern and retrieve strings', () => {
      const hash = store.internString('hello');
      store.getString(hash).should.equal('hello');
    });

    it('should return same hash for same string', () => {
      const h1 = store.internString('test');
      const h2 = store.internString('test');
      h1.should.equal(h2);
    });

    it('should return different hash for different strings', () => {
      const h1 = store.internString('foo');
      const h2 = store.internString('bar');
      h1.should.not.equal(h2);
    });

    it('should mark string type correctly', () => {
      const hash = store.internString('test');
      store.isString(hash).should.be.true;
      store.isBigInt(hash).should.be.false;
      store.isStruct(hash).should.be.false;
    });
  });

  describe('bigint interning', () => {
    it('should intern and retrieve bigints', () => {
      const hash = store.internBigInt(42n);
      store.getBigInt(hash).should.equal(42n);
    });

    it('should return same hash for same bigint', () => {
      const h1 = store.internBigInt(12345n);
      const h2 = store.internBigInt(12345n);
      h1.should.equal(h2);
    });

    it('should mark bigint type correctly', () => {
      const hash = store.internBigInt(99n);
      store.isBigInt(hash).should.be.true;
      store.isString(hash).should.be.false;
    });
  });

  describe('struct interning', () => {
    it('should intern and retrieve structs', () => {
      const childHash = store.internString('x');
      const hash = store.internStruct(7, [childHash]);

      const struct = store.getStruct(hash);
      struct.constructorId.should.equal(7);
      struct.children[0].should.equal(childHash);
    });

    it('should return same hash for same struct', () => {
      const child = store.internString('x');
      const h1 = store.internStruct(5, [child]);
      const h2 = store.internStruct(5, [child]);
      h1.should.equal(h2);
    });

    it('should return different hash for different constructor', () => {
      const child = store.internString('x');
      const h1 = store.internStruct(1, [child]);
      const h2 = store.internStruct(2, [child]);
      h1.should.not.equal(h2);
    });

    it('should return different hash for different children', () => {
      const c1 = store.internString('a');
      const c2 = store.internString('b');
      const h1 = store.internStruct(1, [c1]);
      const h2 = store.internStruct(1, [c2]);
      h1.should.not.equal(h2);
    });

    it('should mark struct type correctly', () => {
      const hash = store.internStruct(1, []);
      store.isStruct(hash).should.be.true;
      store.isString(hash).should.be.false;
    });

    it('should handle nested structs', () => {
      const leaf = store.internString('x');
      const inner = store.internStruct(1, [leaf]);
      const outer = store.internStruct(2, [inner]);

      store.isStruct(outer).should.be.true;
      const outerStruct = store.getStruct(outer);
      outerStruct.children[0].should.equal(inner);
    });
  });

  describe('equality', () => {
    it('should use O(1) hash comparison', () => {
      const h1 = store.internString('test');
      const h2 = store.internString('test');
      store.equal(h1, h2).should.be.true;
    });

    it('should detect inequality', () => {
      const h1 = store.internString('a');
      const h2 = store.internString('b');
      store.equal(h1, h2).should.be.false;
    });
  });

  describe('has', () => {
    it('should return true for interned values', () => {
      const hash = store.internString('exists');
      store.has(hash).should.be.true;
    });

    it('should return false for unknown hashes', () => {
      store.has(99999n).should.be.false;
    });
  });

  describe('getConstructorId', () => {
    it('should return constructor ID for struct', () => {
      const hash = store.internStruct(42, []);
      store.getConstructorId(hash).should.equal(42);
    });

    it('should return undefined for non-struct', () => {
      const hash = store.internString('not-struct');
      should.not.exist(store.getConstructorId(hash));
    });
  });

  describe('getChildren', () => {
    it('should return children for struct', () => {
      const c1 = store.internString('a');
      const c2 = store.internString('b');
      const hash = store.internStruct(1, [c1, c2]);

      const children = store.getChildren(hash);
      children.should.have.length(2);
      children[0].should.equal(c1);
      children[1].should.equal(c2);
    });

    it('should return empty array for non-struct', () => {
      const hash = store.internString('leaf');
      store.getChildren(hash).should.deep.equal([]);
    });
  });

  describe('stats', () => {
    it('should track counts', () => {
      store.internString('a');
      store.internString('b');
      store.internBigInt(1n);
      store.internStruct(1, []);

      const stats = store.stats();
      stats.strings.should.equal(2);
      stats.bigints.should.equal(1);
      stats.structs.should.equal(1);
      stats.total.should.equal(4);
    });

    it('should not double-count duplicates', () => {
      store.internString('same');
      store.internString('same');
      store.internString('same');

      store.stats().strings.should.equal(1);
    });
  });
});

describe('ScopedStore', () => {
  let root;
  let scoped;

  beforeEach(() => {
    root = new Store();
    scoped = new ScopedStore(root);
  });

  describe('inheritance', () => {
    it('should see parent values', () => {
      const hash = root.internString('parent');
      scoped.getString(hash).should.equal('parent');
    });

    it('should see local values', () => {
      const hash = scoped.internString('local');
      scoped.getString(hash).should.equal('local');
    });

    it('should not add to parent when interning locally', () => {
      scoped.internString('local-only');
      root.stats().strings.should.equal(0);
    });

    it('should reuse parent hash if exists', () => {
      const parentHash = root.internString('shared');
      const scopedHash = scoped.internString('shared');
      parentHash.should.equal(scopedHash);
      scoped.local.stats().strings.should.equal(0);
    });
  });

  describe('fork', () => {
    it('should create nested scope', () => {
      const child = scoped.fork();
      child.should.be.instanceOf(ScopedStore);
      child.parent.should.equal(scoped);
    });

    it('should see grandparent values', () => {
      const hash = root.internString('grandparent');
      const child = scoped.fork();
      child.getString(hash).should.equal('grandparent');
    });
  });

  describe('commit', () => {
    it('should merge local to parent', () => {
      const hash = scoped.internString('will-commit');
      root.has(hash).should.be.false;

      scoped.commit();
      root.has(hash).should.be.true;
      root.getString(hash).should.equal('will-commit');
    });

    it('should merge nested commits', () => {
      const child = scoped.fork();
      const hash = child.internString('deep');

      root.has(hash).should.be.false;
      scoped.has(hash).should.be.false;

      child.commit();
      scoped.has(hash).should.be.true;

      scoped.commit();
      root.has(hash).should.be.true;
    });
  });

  describe('discard', () => {
    it('should clear local values', () => {
      const hash = scoped.internString('will-discard');
      scoped.has(hash).should.be.true;

      scoped.discard();
      // Hash computed from string, so scoped.has checks local (now empty) and parent
      scoped.local.has(hash).should.be.false;
    });

    it('should not affect parent', () => {
      const parentHash = root.internString('parent-safe');
      scoped.internString('local-discard');

      scoped.discard();
      root.getString(parentHash).should.equal('parent-safe');
    });
  });

  describe('has', () => {
    it('should check local and parent', () => {
      const parentHash = root.internString('in-parent');
      const localHash = scoped.internString('in-local');

      scoped.has(parentHash).should.be.true;
      scoped.has(localHash).should.be.true;
      scoped.has(99999n).should.be.false;
    });
  });

  describe('struct operations', () => {
    it('should intern struct locally', () => {
      const child = scoped.internString('x');
      const hash = scoped.internStruct(1, [child]);

      scoped.isStruct(hash).should.be.true;
      scoped.getConstructorId(hash).should.equal(1);
    });

    it('should see parent structs', () => {
      const child = root.internString('x');
      const hash = root.internStruct(1, [child]);

      scoped.isStruct(hash).should.be.true;
      scoped.getChildren(hash).should.deep.equal([child]);
    });
  });
});
