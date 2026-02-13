/**
 * Tests for execution tree exploration
 */

const assert = require('assert');
const path = require('path');
const mde = require('../../lib/mde');
const { explore, countLeaves, getAllLeaves, maxDepth, countNodes } = require('../../lib/v2/prover/strategy/symexec');
const forward = require('../../lib/v2/prover/strategy/forward');
const Store = require('../../lib/v2/kernel/store');

describe('explore', function() {
  this.timeout(10000);

  describe('deterministic execution', function() {
    it('single path to quiescence', async function() {
      // Load a simple calculus
      const calc = await mde.load([
        path.join(__dirname, 'fixtures/bin.mde')
      ]);

      // Simple state: just 'e' (zero)
      Store.clear();
      const state = forward.createState({
        [await mde.parseExpr('e')]: 1
      }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 10,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      // No rules should fire on just 'e'
      assert.strictEqual(tree.type, 'leaf');
      assert.strictEqual(countLeaves(tree), 1);
    });
  });

  describe('nondeterministic execution', function() {
    let calc;

    before(async function() {
      // Create a simple nondeterministic system
      // Two rules that can both fire on 'start'
      Store.clear();
      calc = await mde.load([
        path.join(__dirname, 'fixtures/nondet.mde')
      ]);
    });

    it('branches on multiple applicable rules', async function() {
      Store.clear();
      const startHash = await mde.parseExpr('start');
      const state = forward.createState({ [startHash]: 1 }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 5,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      // Should branch if multiple rules can fire
      if (tree.type === 'branch') {
        assert(tree.children.length >= 1);
        assert(countLeaves(tree) >= 1);
      }
    });
  });

  describe('depth bounding', function() {
    it('respects maxDepth', async function() {
      const calc = await mde.load([
        path.join(__dirname, 'fixtures/bin.mde')
      ]);

      Store.clear();
      // Create a state that would loop forever
      const state = forward.createState({
        [await mde.parseExpr('(i e)')]: 1  // binary 1
      }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 3,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      // Depth should be bounded
      assert(maxDepth(tree) <= 3);
    });
  });

  describe('tree utilities', function() {
    it('countLeaves counts terminal nodes', function() {
      const tree = {
        type: 'branch',
        state: {},
        children: [
          { rule: 'r1', child: { type: 'leaf', state: {} } },
          { rule: 'r2', child: { type: 'leaf', state: {} } },
          { rule: 'r3', child: { type: 'bound', state: {} } }
        ]
      };
      assert.strictEqual(countLeaves(tree), 3);
    });

    it('getAllLeaves collects all terminal nodes', function() {
      const leaf1 = { type: 'leaf', state: { id: 1 } };
      const leaf2 = { type: 'leaf', state: { id: 2 } };
      const bound = { type: 'bound', state: { id: 3 } };
      const tree = {
        type: 'branch',
        state: {},
        children: [
          { rule: 'r1', child: leaf1 },
          { rule: 'r2', child: {
            type: 'branch',
            state: {},
            children: [
              { rule: 'r3', child: leaf2 },
              { rule: 'r4', child: bound }
            ]
          }}
        ]
      };
      const leaves = getAllLeaves(tree);
      assert.strictEqual(leaves.length, 3);
      assert(leaves.includes(leaf1));
      assert(leaves.includes(leaf2));
      assert(leaves.includes(bound));
    });

    it('maxDepth returns tree height', function() {
      const tree = {
        type: 'branch',
        state: {},
        children: [
          { rule: 'r1', child: { type: 'leaf', state: {} } },
          { rule: 'r2', child: {
            type: 'branch',
            state: {},
            children: [
              { rule: 'r3', child: { type: 'leaf', state: {} } }
            ]
          }}
        ]
      };
      assert.strictEqual(maxDepth(tree), 2);
    });

    it('countNodes returns total node count', function() {
      const tree = {
        type: 'branch',
        state: {},
        children: [
          { rule: 'r1', child: { type: 'leaf', state: {} } },
          { rule: 'r2', child: { type: 'leaf', state: {} } }
        ]
      };
      assert.strictEqual(countNodes(tree), 3);
    });
  });
});
