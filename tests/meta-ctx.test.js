const { describe, it } = require('node:test');
const assert = require('node:assert');

const { MetaCtx } = require('../lib/prover/meta-ctx');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const { freshMetavar, resetMetavar } = require('../lib/kernel/fresh');

describe('MetaCtx', () => {
  it('bind + resolve direct metavar', () => {
    const mc = new MetaCtx();
    resetMetavar(100);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    mc.bind(mv, a);
    assert.strictEqual(mc.resolve(mv), a);
  });

  it('resolve returns input for ground terms', () => {
    const mc = new MetaCtx();
    const a = Store.put('atom', ['a']);
    assert.strictEqual(mc.resolve(a), a);
  });

  it('resolve compound term containing metavar', () => {
    const mc = new MetaCtx();
    resetMetavar(200);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const t_mv = Store.put('tensor', [mv, b]);  // mv ⊗ b
    const t_a = Store.put('tensor', [a, b]);     // a ⊗ b
    mc.bind(mv, a);
    assert.strictEqual(mc.resolve(t_mv), t_a);
  });

  it('save/restore undoes bindings', () => {
    const mc = new MetaCtx();
    resetMetavar(300);
    const mv1 = freshMetavar();
    const mv2 = freshMetavar();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);

    mc.bind(mv1, a);
    const mark = mc.save();
    mc.bind(mv2, b);

    assert.strictEqual(mc.resolve(mv2), b);
    mc.restore(mark);
    // mv2 binding undone
    assert.strictEqual(mc.resolve(mv2), mv2);
    // mv1 binding preserved
    assert.strictEqual(mc.resolve(mv1), a);
  });

  it('absorbTheta from unify result', () => {
    const mc = new MetaCtx();
    resetMetavar(400);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    mc.absorbTheta([[mv, a]]);
    assert.strictEqual(mc.resolve(mv), a);
  });

  it('resolveSeq produces ground sequent', () => {
    const mc = new MetaCtx();
    resetMetavar(500);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    const seq = Seq.fromArrays([mv], [], a);
    mc.bind(mv, a);
    const resolved = mc.resolveSeq(seq);
    const linear = Seq.getContext(resolved, 'linear');
    assert.strictEqual(linear[0], a);
    assert.strictEqual(resolved.succedent, a);
  });

  it('hasBindings returns false when empty, true after bind', () => {
    const mc = new MetaCtx();
    assert.strictEqual(mc.hasBindings(), false);
    resetMetavar(600);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    mc.bind(mv, a);
    assert.strictEqual(mc.hasBindings(), true);
  });

  it('hasBindings returns false after all bindings restored', () => {
    const mc = new MetaCtx();
    resetMetavar(700);
    const mv = freshMetavar();
    const a = Store.put('atom', ['a']);
    const mark = mc.save();
    mc.bind(mv, a);
    assert.strictEqual(mc.hasBindings(), true);
    mc.restore(mark);
    assert.strictEqual(mc.hasBindings(), false);
  });
});
