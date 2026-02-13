/**
 * Tests for v2 Sequent (generic) and focused/context (multiset)
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const Seq = require('../lib/kernel/sequent');
const Context = require('../lib/prover/context');
const calculus = require('../lib/calculus');
const Store = require('../lib/kernel/store');

describe('v2 Sequent (generic arrays)', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('fromArrays', () => {
    it('should create sequent with arrays', () => {
      const s = Seq.fromArrays(
        [AST.freevar('A'), AST.freevar('B')],
        [],
        AST.freevar('C')
      );
      assert.strictEqual(Seq.getContext(s, 'linear').length, 2);
    });

    it('should preserve duplicates', () => {
      const f = AST.freevar('A');
      const s = Seq.fromArrays([f, f, f], [], AST.freevar('B'));
      const ctx = Seq.getContext(s, 'linear');
      assert.strictEqual(ctx.length, 3);
    });
  });

  describe('addToContext', () => {
    it('should add formula to context', () => {
      const s = Seq.empty(['linear', 'cartesian']);
      const s2 = Seq.addToContext(s, 'linear', AST.freevar('A'));
      const ctx = Seq.getContext(s2, 'linear');
      assert.strictEqual(ctx.length, 1);
      // Formulas are now hashes - use Store.tag to inspect
      assert.strictEqual(Store.tag(ctx[0]), 'freevar');
    });

    it('should append duplicates', () => {
      const f = AST.freevar('A');
      let s = Seq.empty(['linear', 'cartesian']);
      s = Seq.addToContext(s, 'linear', f);
      s = Seq.addToContext(s, 'linear', f);
      const ctx = Seq.getContext(s, 'linear');
      assert.strictEqual(ctx.length, 2);
    });

    it('should be immutable', () => {
      const s = Seq.empty(['linear', 'cartesian']);
      const s2 = Seq.addToContext(s, 'linear', AST.freevar('A'));
      assert.strictEqual(Seq.getContext(s, 'linear').length, 0);
      assert.strictEqual(Seq.getContext(s2, 'linear').length, 1);
    });
  });

  describe('removeAtIndex', () => {
    it('should remove formula at index', () => {
      const s = Seq.fromArrays(
        [AST.freevar('A'), AST.freevar('B')],
        [],
        AST.freevar('C')
      );
      const s2 = Seq.removeAtIndex(s, 'linear', 0);
      assert.strictEqual(Seq.getContext(s2, 'linear').length, 1);
      // Formulas are now hashes - use Store.child to access children
      assert.strictEqual(Store.child(Seq.getContext(s2, 'linear')[0], 0), 'B');
    });

    it('should return null for invalid index', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('B'));
      assert.strictEqual(Seq.removeAtIndex(s, 'linear', 5), null);
      assert.strictEqual(Seq.removeAtIndex(s, 'linear', -1), null);
    });
  });

  describe('copy', () => {
    it('should deep copy sequent', () => {
      const s = Seq.fromArrays(
        [AST.freevar('A'), AST.freevar('B')],
        [AST.freevar('C')],
        AST.freevar('D')
      );
      const s2 = Seq.copy(s);
      assert.strictEqual(Seq.eq(s, s2), true);
      assert.notStrictEqual(s, s2);
    });
  });

  describe('substitute', () => {
    it('should apply substitution', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('B'));
      const theta = [[AST.freevar('A'), AST.freevar('X')]];
      const s2 = Seq.substitute(s, theta);
      const ctx = Seq.getContext(s2, 'linear');
      // Formulas are now hashes - use Store.child to access children
      assert.strictEqual(Store.child(ctx[0], 0), 'X');
    });
  });

  describe('freeVars', () => {
    it('should collect free variables from all contexts', () => {
      const s = Seq.fromArrays(
        [AST.freevar('A'), AST.tensor(AST.freevar('B'), AST.freevar('C'))],
        [AST.freevar('D')],
        AST.freevar('E')
      );
      const vars = Seq.freeVars(s);
      assert.deepStrictEqual(vars.sort(), ['A', 'B', 'C', 'D', 'E']);
    });
  });

  describe('renameVars', () => {
    it('should rename variables to unique names', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const { seq: s2, theta } = Seq.renameVars(s);
      const vars = Seq.freeVars(s2);
      assert.strictEqual(vars.length, 1);
      assert.ok(vars[0].startsWith('_V'));
    });
  });
});

describe('v2 focused/context (multiset)', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('fromArray', () => {
    it('should create multiset from array', () => {
      const arr = [AST.freevar('A'), AST.freevar('B'), AST.freevar('A')];
      const ms = Context.fromArray(arr);
      assert.strictEqual(Object.keys(ms).length, 2);
    });

    it('should count duplicates', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f, f, f]);
      const entries = Context.entries(ms);
      assert.strictEqual(entries.length, 1);
      // entries returns [hash, count] arrays
      assert.strictEqual(entries[0][1], 3);
    });
  });

  describe('toArray', () => {
    it('should convert multiset to array', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f, f]);
      const arr = Context.toArray(ms);
      assert.strictEqual(arr.length, 2);
    });
  });

  describe('add', () => {
    it('should add formula to multiset', () => {
      const ms = Context.empty();
      const ms2 = Context.add(ms, AST.freevar('A'));
      assert.strictEqual(Context.size(ms2), 1);
    });

    it('should increment count for duplicate', () => {
      const f = AST.freevar('A');
      let ms = Context.empty();
      ms = Context.add(ms, f);
      ms = Context.add(ms, f);
      const entries = Context.entries(ms);
      assert.strictEqual(entries.length, 1);
      // entries returns [hash, count] arrays
      assert.strictEqual(entries[0][1], 2);
    });

    it('should be immutable', () => {
      const ms = Context.empty();
      const ms2 = Context.add(ms, AST.freevar('A'));
      assert.strictEqual(Context.size(ms), 0);
      assert.strictEqual(Context.size(ms2), 1);
    });
  });

  describe('remove', () => {
    it('should remove formula from multiset', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f]);
      // f IS the hash now (content-addressed)
      const ms2 = Context.remove(ms, f);
      assert.strictEqual(Context.size(ms2), 0);
    });

    it('should decrement count', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f, f, f]);
      // f IS the hash now (content-addressed)
      const ms2 = Context.remove(ms, f, 2);
      const entries = Context.entries(ms2);
      // entries returns [hash, count] arrays
      assert.strictEqual(entries[0][1], 1);
    });

    it('should return null if not enough', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f]);
      // f IS the hash now (content-addressed)
      const ms2 = Context.remove(ms, f, 2);
      assert.strictEqual(ms2, null);
    });

    it('should return null if not found', () => {
      const ms = Context.fromArray([AST.freevar('A')]);
      // Formulas ARE hashes now - AST.freevar('X') IS the hash
      const ms2 = Context.remove(ms, AST.freevar('X'));
      assert.strictEqual(ms2, null);
    });
  });

  describe('has', () => {
    it('should return true if formula exists', () => {
      const f = AST.freevar('A');
      const ms = Context.fromArray([f]);
      assert.strictEqual(Context.has(ms, f), true);
    });

    it('should return false if formula not found', () => {
      const ms = Context.fromArray([AST.freevar('A')]);
      assert.strictEqual(Context.has(ms, AST.freevar('X')), false);
    });
  });

  describe('merge', () => {
    it('should merge two multisets', () => {
      const ms1 = Context.fromArray([AST.freevar('A')]);
      const ms2 = Context.fromArray([AST.freevar('B')]);
      const merged = Context.merge(ms1, ms2);
      assert.strictEqual(Context.size(merged), 2);
    });

    it('should add counts for duplicates', () => {
      const f = AST.freevar('A');
      const ms1 = Context.fromArray([f, f]);
      const ms2 = Context.fromArray([f]);
      const merged = Context.merge(ms1, ms2);
      const entries = Context.entries(merged);
      // entries returns [hash, count] arrays
      assert.strictEqual(entries[0][1], 3);
    });
  });

  describe('subtract', () => {
    it('should subtract multiset from another', () => {
      const ms1 = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      const ms2 = Context.fromArray([AST.freevar('A')]);
      const result = Context.subtract(ms1, ms2);
      assert.strictEqual(Context.size(result), 1);
    });

    it('should return null if not enough', () => {
      const ms1 = Context.fromArray([AST.freevar('A')]);
      const ms2 = Context.fromArray([AST.freevar('A'), AST.freevar('A')]);
      const result = Context.subtract(ms1, ms2);
      assert.strictEqual(result, null);
    });
  });

  describe('contains', () => {
    it('should return true if contains all', () => {
      const ms1 = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      const ms2 = Context.fromArray([AST.freevar('A')]);
      assert.strictEqual(Context.contains(ms1, ms2), true);
    });

    it('should return false if missing', () => {
      const ms1 = Context.fromArray([AST.freevar('A')]);
      const ms2 = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      assert.strictEqual(Context.contains(ms1, ms2), false);
    });
  });

  describe('eq', () => {
    it('should return true for equal multisets', () => {
      const ms1 = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      const ms2 = Context.fromArray([AST.freevar('B'), AST.freevar('A')]);
      assert.strictEqual(Context.eq(ms1, ms2), true);
    });

    it('should return false for different multisets', () => {
      const ms1 = Context.fromArray([AST.freevar('A')]);
      const ms2 = Context.fromArray([AST.freevar('B')]);
      assert.strictEqual(Context.eq(ms1, ms2), false);
    });

    it('should compare counts', () => {
      const f = AST.freevar('A');
      const ms1 = Context.fromArray([f, f]);
      const ms2 = Context.fromArray([f]);
      assert.strictEqual(Context.eq(ms1, ms2), false);
    });
  });

  describe('filter', () => {
    it('should filter formulas by predicate', () => {
      const ms = Context.fromArray([
        AST.freevar('A'),
        AST.tensor(AST.freevar('B'), AST.freevar('C'))
      ]);
      // Formulas are hashes - use Store.tag to inspect
      const filtered = Context.filter(ms, h => Store.tag(h) === 'freevar');
      assert.strictEqual(Context.size(filtered), 1);
    });
  });

  describe('find', () => {
    it('should find formula matching predicate', () => {
      const ms = Context.fromArray([
        AST.freevar('A'),
        AST.tensor(AST.freevar('B'), AST.freevar('C'))
      ]);
      // Formulas are hashes - use Store.tag to inspect
      // find() returns the hash directly or null
      const found = Context.find(ms, h => Store.tag(h) === 'tensor');
      assert.ok(found !== null);
      assert.strictEqual(Store.tag(found), 'tensor');
    });

    it('should return null if not found', () => {
      const ms = Context.fromArray([AST.freevar('A')]);
      const found = Context.find(ms, h => Store.tag(h) === 'tensor');
      assert.strictEqual(found, null);
    });
  });

  describe('substitute', () => {
    it('should apply substitution to all formulas', () => {
      const ms = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      const theta = [[AST.freevar('A'), AST.freevar('X')]];
      const ms2 = Context.substitute(ms, theta);
      // Formulas ARE hashes now - direct comparison works
      assert.strictEqual(Context.has(ms2, AST.freevar('X')), true);
      assert.strictEqual(Context.has(ms2, AST.freevar('A')), false);
    });

    it('should handle collision (merge when same hash after sub)', () => {
      const ms = Context.fromArray([AST.freevar('A'), AST.freevar('B')]);
      const theta = [
        [AST.freevar('A'), AST.freevar('X')],
        [AST.freevar('B'), AST.freevar('X')]
      ];
      const ms2 = Context.substitute(ms, theta);
      const entries = Context.entries(ms2);
      assert.strictEqual(entries.length, 1);
      // entries returns [hash, count] arrays
      assert.strictEqual(entries[0][1], 2);
    });
  });
});
