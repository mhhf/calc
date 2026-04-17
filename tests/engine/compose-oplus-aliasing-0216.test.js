/**
 * TODO_0216 Phase 0 H2 — fusePairEx oplus-projection aliasing canary
 *
 * Locks the contract that, when a producer has an oplus in its consequent,
 * fusePairEx projects each branch into its own rule and fuses each against
 * the consumer without cross-branch metavar aliasing.
 *
 * Must PASS on HEAD. Phase 4 (B — pool-disjoint invariant) preserves this
 * behaviour by special-casing the non-first branch of fusePairEx; if that
 * special-case is ever skipped, this test catches it.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { fusePairEx } = require('../../lib/engine/compose');
const { resolveConn } = require('../../lib/engine/compile');
const { collectMetavars } = require('../../lib/engine/pattern-utils');

describe('TODO_0216 H2 — fusePairEx oplus branch metavar disjointness', () => {
  let rc;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
    const ccfg = require('../../lib/engine/ill/calculus-config');
    rc = resolveConn(ccfg.connectives);
  });

  it('two oplus branches with shared producer metavar yield disjoint producer-derived metavars', () => {
    // Producer: gas(a) -o { pc(X) oplus pc(X) }
    //   Shared metavar X across branches is the adversarial case: each
    //   branch must get a FRESH rename of X, else the two fused rules
    //   would alias on X at the compose layer.
    //
    // Note: the consumer's metavar M naturally appears in both fused rules
    // (same consumer object fused into each branch). Soundness lives in
    // the producer side — that's what we assert.
    const a = Store.put('atom', ['a']);
    const pAnte = Store.put('gas', [a]);

    const mvX = Store.put('metavar', ['X']);
    const pcX_left = Store.put('pc', [mvX]);
    const pcX_right = Store.put('pc', [mvX]);
    const choice = Store.put('oplus', [pcX_left, pcX_right]);
    const producer = {
      name: 'prod',
      hash: Store.put('loli', [pAnte, Store.put('monad', [choice])]),
    };

    const mvM = Store.put('metavar', ['M']);
    const cAnte = Store.put('pc', [mvM]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = {
      name: 'cons',
      hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]),
    };

    const consumerMvs = new Set();
    collectMetavars(consumer.hash, consumerMvs);

    const results = fusePairEx(producer, consumer, 'pc', rc, null);
    assert.ok(Array.isArray(results) && results.length >= 2,
      `fusePairEx should yield ≥2 branches, got ${results ? results.length : 'null'}`);

    // Producer-derived metavars = fused_rule.metavars \ consumer.metavars
    const producerDerived = results.map(r => {
      const all = new Set();
      collectMetavars(r.hash, all);
      for (const m of consumerMvs) all.delete(m);
      return all;
    });

    // None of the fused rules should still contain the original producer X —
    // alphaRename must have replaced it.
    for (let i = 0; i < results.length; i++) {
      assert.ok(!producerDerived[i].has(mvX),
        `branch ${i}: original producer metavar X survived (alphaRename missed)`);
    }

    // Producer-derived sets should be pairwise disjoint (fresh rename per branch).
    for (let i = 0; i < producerDerived.length; i++) {
      for (let j = i + 1; j < producerDerived.length; j++) {
        const inter = [...producerDerived[i]].filter(mv => producerDerived[j].has(mv));
        assert.strictEqual(inter.length, 0,
          `branches ${i}/${j} share producer-derived metavars: ${inter.join(',')}`);
      }
    }
  });

  it('three oplus branches yield pairwise-disjoint producer-derived metavars', () => {
    const a = Store.put('atom', ['a']);
    const pAnte = Store.put('gas', [a]);
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);
    const mvZ = Store.put('metavar', ['Z']);
    const pcX = Store.put('pc', [mvX]);
    const pcY = Store.put('pc', [mvY]);
    const pcZ = Store.put('pc', [mvZ]);
    const inner = Store.put('oplus', [pcY, pcZ]);
    const choice = Store.put('oplus', [pcX, inner]);
    const producer = {
      name: 'prod3',
      hash: Store.put('loli', [pAnte, Store.put('monad', [choice])]),
    };

    const mvM = Store.put('metavar', ['M']);
    const cAnte = Store.put('pc', [mvM]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = {
      name: 'cons3',
      hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]),
    };

    const consumerMvs = new Set();
    collectMetavars(consumer.hash, consumerMvs);

    const results = fusePairEx(producer, consumer, 'pc', rc, null);
    assert.ok(Array.isArray(results) && results.length === 3,
      `expected 3 fused branches, got ${results ? results.length : 'null'}`);

    const producerDerived = results.map(r => {
      const all = new Set();
      collectMetavars(r.hash, all);
      for (const m of consumerMvs) all.delete(m);
      return all;
    });

    for (let i = 0; i < producerDerived.length; i++) {
      for (const orig of [mvX, mvY, mvZ]) {
        assert.ok(!producerDerived[i].has(orig),
          `branch ${i}: original producer metavar survived`);
      }
    }

    for (let i = 0; i < producerDerived.length; i++) {
      for (let j = i + 1; j < producerDerived.length; j++) {
        const inter = [...producerDerived[i]].filter(mv => producerDerived[j].has(mv));
        assert.strictEqual(inter.length, 0,
          `branches ${i}/${j} share producer-derived metavars`);
      }
    }
  });

  it('producer without oplus falls through to single fusePair result', () => {
    // Sanity: the canary's precondition (detecting oplus) must work.
    const a = Store.put('atom', ['a']);
    const pAnte = Store.put('gas', [a]);
    const pcX = Store.put('pc', [Store.put('metavar', ['X'])]);
    const producer = { name: 'flat', hash: Store.put('loli', [pAnte, Store.put('monad', [pcX])]) };

    const mvM = Store.put('metavar', ['M']);
    const cAnte = Store.put('pc', [mvM]);
    const cConseq = Store.put('stack', [mvM]);
    const consumer = { name: 'c', hash: Store.put('loli', [cAnte, Store.put('monad', [cConseq])]) };

    const results = fusePairEx(producer, consumer, 'pc', rc, null);
    assert.ok(Array.isArray(results) && results.length === 1,
      `flat producer should yield 1 fused rule, got ${results ? results.length : 'null'}`);
  });
});
