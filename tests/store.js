const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const { Store, ScopedStore, NodeType } = require('../lib/v1/store');

describe('Store', () => {
  let store;

  beforeEach(() => {
    store = new Store();
  });

  describe('string interning', () => {
    it('should intern and retrieve strings', () => {
      const hash = store.internString('hello');
      assert.strictEqual(store.getString(hash), 'hello');
    });

    it('should return same hash for same string', () => {
      const h1 = store.internString('test');
      const h2 = store.internString('test');
      assert.strictEqual(h1, h2);
    });

    it('should return different hash for different strings', () => {
      const h1 = store.internString('foo');
      const h2 = store.internString('bar');
      assert.notStrictEqual(h1, h2);
    });

    it('should mark string type correctly', () => {
      const hash = store.internString('test');
      assert.strictEqual(store.isString(hash), true);
      assert.strictEqual(store.isBigInt(hash), false);
      assert.strictEqual(store.isStruct(hash), false);
    });
  });

  describe('bigint interning', () => {
    it('should intern and retrieve bigints', () => {
      const hash = store.internBigInt(42n);
      assert.strictEqual(store.getBigInt(hash), 42n);
    });

    it('should return same hash for same bigint', () => {
      const h1 = store.internBigInt(12345n);
      const h2 = store.internBigInt(12345n);
      assert.strictEqual(h1, h2);
    });

    it('should mark bigint type correctly', () => {
      const hash = store.internBigInt(99n);
      assert.strictEqual(store.isBigInt(hash), true);
      assert.strictEqual(store.isString(hash), false);
    });
  });

  describe('struct interning', () => {
    it('should intern and retrieve structs', () => {
      const childHash = store.internString('x');
      const hash = store.internStruct(7, [childHash]);

      const struct = store.getStruct(hash);
      assert.strictEqual(struct.constructorId, 7);
      assert.strictEqual(struct.children[0], childHash);
    });

    it('should return same hash for same struct', () => {
      const child = store.internString('x');
      const h1 = store.internStruct(5, [child]);
      const h2 = store.internStruct(5, [child]);
      assert.strictEqual(h1, h2);
    });

    it('should return different hash for different constructor', () => {
      const child = store.internString('x');
      const h1 = store.internStruct(1, [child]);
      const h2 = store.internStruct(2, [child]);
      assert.notStrictEqual(h1, h2);
    });

    it('should return different hash for different children', () => {
      const c1 = store.internString('a');
      const c2 = store.internString('b');
      const h1 = store.internStruct(1, [c1]);
      const h2 = store.internStruct(1, [c2]);
      assert.notStrictEqual(h1, h2);
    });

    it('should mark struct type correctly', () => {
      const hash = store.internStruct(1, []);
      assert.strictEqual(store.isStruct(hash), true);
      assert.strictEqual(store.isString(hash), false);
    });

    it('should handle nested structs', () => {
      const leaf = store.internString('x');
      const inner = store.internStruct(1, [leaf]);
      const outer = store.internStruct(2, [inner]);

      assert.strictEqual(store.isStruct(outer), true);
      const outerStruct = store.getStruct(outer);
      assert.strictEqual(outerStruct.children[0], inner);
    });
  });

  describe('equality', () => {
    it('should use O(1) hash comparison', () => {
      const h1 = store.internString('test');
      const h2 = store.internString('test');
      assert.strictEqual(store.equal(h1, h2), true);
    });

    it('should detect inequality', () => {
      const h1 = store.internString('a');
      const h2 = store.internString('b');
      assert.strictEqual(store.equal(h1, h2), false);
    });
  });

  describe('has', () => {
    it('should return true for interned values', () => {
      const hash = store.internString('exists');
      assert.strictEqual(store.has(hash), true);
    });

    it('should return false for unknown hashes', () => {
      assert.strictEqual(store.has(99999n), false);
    });
  });

  describe('getConstructorId', () => {
    it('should return constructor ID for struct', () => {
      const hash = store.internStruct(42, []);
      assert.strictEqual(store.getConstructorId(hash), 42);
    });

    it('should return undefined for non-struct', () => {
      const hash = store.internString('not-struct');
      assert.strictEqual(store.getConstructorId(hash), undefined);
    });
  });

  describe('getChildren', () => {
    it('should return children for struct', () => {
      const c1 = store.internString('a');
      const c2 = store.internString('b');
      const hash = store.internStruct(1, [c1, c2]);

      const children = store.getChildren(hash);
      assert.strictEqual(children.length, 2);
      assert.strictEqual(children[0], c1);
      assert.strictEqual(children[1], c2);
    });

    it('should return empty array for non-struct', () => {
      const hash = store.internString('leaf');
      assert.deepStrictEqual(store.getChildren(hash), []);
    });
  });

  describe('stats', () => {
    it('should track counts', () => {
      store.internString('a');
      store.internString('b');
      store.internBigInt(1n);
      store.internStruct(1, []);

      const stats = store.stats();
      assert.strictEqual(stats.strings, 2);
      assert.strictEqual(stats.bigints, 1);
      assert.strictEqual(stats.structs, 1);
      assert.strictEqual(stats.total, 4);
    });

    it('should not double-count duplicates', () => {
      store.internString('same');
      store.internString('same');
      store.internString('same');

      assert.strictEqual(store.stats().strings, 1);
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
      assert.strictEqual(scoped.getString(hash), 'parent');
    });

    it('should see local values', () => {
      const hash = scoped.internString('local');
      assert.strictEqual(scoped.getString(hash), 'local');
    });

    it('should not add to parent when interning locally', () => {
      scoped.internString('local-only');
      assert.strictEqual(root.stats().strings, 0);
    });

    it('should reuse parent hash if exists', () => {
      const parentHash = root.internString('shared');
      const scopedHash = scoped.internString('shared');
      assert.strictEqual(parentHash, scopedHash);
      assert.strictEqual(scoped.local.stats().strings, 0);
    });
  });

  describe('fork', () => {
    it('should create nested scope', () => {
      const child = scoped.fork();
      assert.ok(child instanceof ScopedStore);
      assert.strictEqual(child.parent, scoped);
    });

    it('should see grandparent values', () => {
      const hash = root.internString('grandparent');
      const child = scoped.fork();
      assert.strictEqual(child.getString(hash), 'grandparent');
    });
  });

  describe('commit', () => {
    it('should merge local to parent', () => {
      const hash = scoped.internString('will-commit');
      assert.strictEqual(root.has(hash), false);

      scoped.commit();
      assert.strictEqual(root.has(hash), true);
      assert.strictEqual(root.getString(hash), 'will-commit');
    });

    it('should merge nested commits', () => {
      const child = scoped.fork();
      const hash = child.internString('deep');

      assert.strictEqual(root.has(hash), false);
      assert.strictEqual(scoped.has(hash), false);

      child.commit();
      assert.strictEqual(scoped.has(hash), true);

      scoped.commit();
      assert.strictEqual(root.has(hash), true);
    });
  });

  describe('discard', () => {
    it('should clear local values', () => {
      const hash = scoped.internString('will-discard');
      assert.strictEqual(scoped.has(hash), true);

      scoped.discard();
      // Hash computed from string, so scoped.has checks local (now empty) and parent
      assert.strictEqual(scoped.local.has(hash), false);
    });

    it('should not affect parent', () => {
      const parentHash = root.internString('parent-safe');
      scoped.internString('local-discard');

      scoped.discard();
      assert.strictEqual(root.getString(parentHash), 'parent-safe');
    });
  });

  describe('has', () => {
    it('should check local and parent', () => {
      const parentHash = root.internString('in-parent');
      const localHash = scoped.internString('in-local');

      assert.strictEqual(scoped.has(parentHash), true);
      assert.strictEqual(scoped.has(localHash), true);
      assert.strictEqual(scoped.has(99999n), false);
    });
  });

  describe('struct operations', () => {
    it('should intern struct locally', () => {
      const child = scoped.internString('x');
      const hash = scoped.internStruct(1, [child]);

      assert.strictEqual(scoped.isStruct(hash), true);
      assert.strictEqual(scoped.getConstructorId(hash), 1);
    });

    it('should see parent structs', () => {
      const child = root.internString('x');
      const hash = root.internStruct(1, [child]);

      assert.strictEqual(scoped.isStruct(hash), true);
      assert.deepStrictEqual(scoped.getChildren(hash), [child]);
    });
  });
});
