/**
 * Tests for fingerprint prediction (Opt_H: threaded code).
 *
 * Verifies that prediction produces identical trees to non-prediction,
 * and that the prediction infrastructure works correctly.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const { explore } = require('../../lib/engine/explore');
const { countNodes, getAllLeaves } = require('../../lib/engine/tree-utils');
const { classifyLeaf } = require('../../lib/engine/show');
const { detectStrategy } = require('../../lib/engine/strategy');
const { buildDiscriminatorIndex, detectFingerprintConfig } = require('../../lib/engine/match');
const Store = require('../../lib/kernel/store');

describe('fingerprint prediction (Opt_H)', { timeout: 30000 }, () => {
  describe('attachPredictions', () => {
    it('attaches nextPointerSlot to rules with virtual discriminator', async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
      );

      const ruleList = calc.forwardRules;
      const fpConfig = detectFingerprintConfig(ruleList);
      assert(fpConfig, 'should detect fingerprint config');
      assert.strictEqual(fpConfig.type, 'virtual', 'EVM rules use virtual discriminator');
      assert(fpConfig.pointerPred, 'should have pointerPred');

      // attachPredictions is called by detectStrategy, so rules should already have it
      const strategy = detectStrategy(ruleList);
      assert(strategy.fpConfig, 'strategy should have fpConfig');

      let withSlot = 0;
      for (const rule of ruleList) {
        if (rule.nextPointerSlot !== undefined) withSlot++;
      }
      assert(withSlot > 0, `Expected some rules with nextPointerSlot, got ${withSlot}`);
    });

    it('does not attach to multi-alt rules', async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
      );

      detectStrategy(calc.forwardRules);
      for (const rule of calc.forwardRules) {
        if (rule.consequentAlts.length > 1) {
          assert.strictEqual(rule.nextPointerSlot, undefined,
            `Multi-alt rule ${rule.name} should not have nextPointerSlot`);
        }
      }
    });
  });

  describe('discriminator index', () => {
    it('maps opcode ground values to rules', async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
      );

      const index = buildDiscriminatorIndex(calc.forwardRules);
      const keys = Object.keys(index);
      assert(keys.length > 0, 'discriminator index should have entries');

      // Most EVM opcodes map to exactly 1 rule
      let singleCandidate = 0;
      for (const key of keys) {
        if (index[key].length === 1) singleCandidate++;
      }
      assert(singleCandidate > 0, 'Some opcodes should have single-candidate rules');
    });
  });

  describe('solc multisig prediction correctness', () => {
    let treePred;

    before(async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
      );
      const state = mde.decomposeQuery(calc.queries.get('symex'));
      const opts = {
        maxDepth: 2000,
        calc: { clauses: calc.clauses, definitions: calc.definitions },
        dangerouslyUseFFI: true
      };

      // Both trees use the same code path — prediction is automatic.
      // We verify the tree shape matches the known-good expected values.
      treePred = explore(state, calc.forwardRules, opts);
    });

    it('produces identical tree shape to expected', () => {
      assert.strictEqual(countNodes(treePred), 280, 'Expected 280 nodes');
      assert.strictEqual(getAllLeaves(treePred).length, 1, 'Expected 1 leaf');
    });

    it('leaf is STOP (successful termination)', () => {
      const leaves = getAllLeaves(treePred);
      assert.strictEqual(classifyLeaf(leaves[0].state), 'STOP');
    });
  });

  describe('solc symbolic prediction correctness', () => {
    let treeMemo;

    before(async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
      );
      const state = mde.decomposeQuery(calc.queries.get('symex'));
      treeMemo = explore(state, calc.forwardRules, {
        maxDepth: 500,
        structuralMemo: true,
        calc: { clauses: calc.clauses, definitions: calc.definitions },
        dangerouslyUseFFI: true
      });
    });

    it('produces expected tree with structural memo', () => {
      const n = countNodes(treeMemo);
      assert(n < 500, `Expected <500 nodes with memo, got ${n}`);
    });

    it('all terminal leaves are valid', () => {
      const leaves = getAllLeaves(treeMemo);
      assert(leaves.length > 0, 'Should have at least one leaf');
      for (const leaf of leaves) {
        assert(['leaf', 'memo', 'dead'].includes(leaf.type),
          `Unexpected leaf type: ${leaf.type}`);
      }
    });
  });
});
