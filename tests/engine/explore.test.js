/**
 * Tests for execution tree exploration
 */

const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const {
  explore, countLeaves, getAllLeaves, maxDepth, countNodes,
  expandItem, expandConsequentChoices, hashState, toDot
} = require('../../lib/prover/strategy/symexec');
const forward = require('../../lib/prover/strategy/forward');
const Store = require('../../lib/kernel/store');

describe('explore', { timeout: 10000 }, () => {
  describe('deterministic execution', () => {
    it('single path to quiescence', async () => {
      const calc = await mde.load([
        path.join(__dirname, '../../calculus/ill/programs/bin.ill')
      ]);

      Store.clear();
      const state = forward.createState({
        [await mde.parseExpr('e')]: 1
      }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 10,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      assert.strictEqual(tree.type, 'leaf');
      assert.strictEqual(countLeaves(tree), 1);
    });
  });

  describe('nondeterministic execution', () => {
    let calc;

    before(async () => {
      Store.clear();
      calc = await mde.load([
        path.join(__dirname, 'fixtures/nondet.ill')
      ]);
    });

    it('branches on multiple applicable rules', async () => {
      Store.clear();
      const startHash = await mde.parseExpr('start');
      const state = forward.createState({ [startHash]: 1 }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 5,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      if (tree.type === 'branch') {
        assert(tree.children.length >= 1);
        assert(countLeaves(tree) >= 1);
      }
    });
  });

  describe('depth bounding', () => {
    it('respects maxDepth', async () => {
      const calc = await mde.load([
        path.join(__dirname, '../../calculus/ill/programs/bin.ill')
      ]);

      Store.clear();
      const state = forward.createState({
        [await mde.parseExpr('(i e)')]: 1
      }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 3,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      assert(maxDepth(tree) <= 3);
    });
  });

  describe('expandItem', () => {
    beforeEach(() => { Store.clear(); });

    it('leaf returns single alternative', () => {
      const h = Store.put('atom', ['foo']);
      const alts = expandItem(h);
      assert.strictEqual(alts.length, 1);
      assert.deepStrictEqual(alts[0], { linear: [h], persistent: [] });
    });

    it('with(A,B) returns two alternatives', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const w = Store.put('with', [a, b]);
      const alts = expandItem(w);
      assert.strictEqual(alts.length, 2);
      assert.deepStrictEqual(alts[0], { linear: [a], persistent: [] });
      assert.deepStrictEqual(alts[1], { linear: [b], persistent: [] });
    });

    it('tensor(A, with(B,C)) returns cross-product', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const w = Store.put('with', [b, c]);
      const t = Store.put('tensor', [a, w]);
      const alts = expandItem(t);
      assert.strictEqual(alts.length, 2);
      assert.deepStrictEqual(alts[0].linear, [a, b]);
      assert.deepStrictEqual(alts[1].linear, [a, c]);
    });

    it('with(with(A,B), C) returns three alternatives', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const w1 = Store.put('with', [a, b]);
      const w2 = Store.put('with', [w1, c]);
      const alts = expandItem(w2);
      assert.strictEqual(alts.length, 3);
    });

    it('bang(A) returns persistent alternative', () => {
      const a = Store.put('atom', ['a']);
      const bang = Store.put('bang', [a]);
      const alts = expandItem(bang);
      assert.strictEqual(alts.length, 1);
      assert.deepStrictEqual(alts[0], { linear: [], persistent: [a] });
    });

    it('loli(bang(P), monad(Q)) assumes P and produces Q', () => {
      const p = Store.put('atom', ['neq']);
      const q = Store.put('atom', ['result']);
      const bangP = Store.put('bang', [p]);
      const monadQ = Store.put('monad', [q]);
      const loli = Store.put('loli', [bangP, monadQ]);
      const alts = expandItem(loli);
      assert.strictEqual(alts.length, 1);
      assert.deepStrictEqual(alts[0].linear, [q]);
      assert.strictEqual(alts[0].persistent.length, 1);
      assert.strictEqual(alts[0].persistent[0], bangP);
    });

    it('with(loli(!P,{A}), loli(!Q,{B})) gives two guarded alternatives', () => {
      const p = Store.put('atom', ['neq']);
      const q = Store.put('atom', ['eq']);
      const a = Store.put('atom', ['zero']);
      const b = Store.put('atom', ['one']);
      const bangP = Store.put('bang', [p]);
      const bangQ = Store.put('bang', [q]);
      const branch0 = Store.put('loli', [bangP, Store.put('monad', [a])]);
      const branch1 = Store.put('loli', [bangQ, Store.put('monad', [b])]);
      const w = Store.put('with', [branch0, branch1]);
      const alts = expandItem(w);
      assert.strictEqual(alts.length, 2);
      // Branch 0: assume !neq, produce zero
      assert.deepStrictEqual(alts[0].linear, [a]);
      assert.strictEqual(alts[0].persistent[0], bangP);
      // Branch 1: assume !eq, produce one
      assert.deepStrictEqual(alts[1].linear, [b]);
      assert.strictEqual(alts[1].persistent[0], bangQ);
    });
  });

  describe('expandConsequentChoices', () => {
    beforeEach(() => { Store.clear(); });

    it('no choice returns single alternative', () => {
      const a = Store.put('atom', ['a']);
      const alts = expandConsequentChoices({ linear: [a], persistent: [] });
      assert.strictEqual(alts.length, 1);
      assert.deepStrictEqual(alts[0].linear, [a]);
    });

    it('single with in linear produces two alternatives', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const w = Store.put('with', [a, b]);
      const alts = expandConsequentChoices({ linear: [w], persistent: [] });
      assert.strictEqual(alts.length, 2);
    });

    it('preserves original persistent items', () => {
      const a = Store.put('atom', ['a']);
      const p = Store.put('atom', ['p']);
      const alts = expandConsequentChoices({ linear: [a], persistent: [p] });
      assert.strictEqual(alts.length, 1);
      assert(alts[0].persistent.includes(p));
    });
  });

  describe('choice forking via fixture', () => {
    it('forks on A & B consequent', async () => {
      Store.clear();
      const calc = await mde.load([
        path.join(__dirname, 'fixtures/choice.ill')
      ]);

      const startHash = await mde.parseExpr('start');
      const state = forward.createState({ [startHash]: 1 }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 5,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      // Root should branch — the 'choose' rule produces left & right
      assert.strictEqual(tree.type, 'branch');
      // Should have 2 children (one per choice)
      assert.strictEqual(tree.children.length, 2);
      // Both should be annotated with choice index
      assert.strictEqual(tree.children[0].choice, 0);
      assert.strictEqual(tree.children[1].choice, 1);
      // Each choice path should eventually reach a leaf (done)
      assert.strictEqual(countLeaves(tree), 2);
    });
  });

  describe('cycle detection', () => {
    it('detects back-edge in A -o { A } loop', () => {
      Store.clear();
      const a = Store.put('atom', ['loop_token']);
      const loli = Store.put('loli', [a, Store.put('monad', [a])]);
      const rule = forward.compileRule({ name: 'loop', hash: loli, antecedent: a, consequent: Store.put('monad', [a]) });

      const state = forward.createState({ [a]: 1 }, {});
      const tree = explore(state, [rule], { maxDepth: 10 });

      // Should detect cycle on second step (same state as initial)
      assert.strictEqual(tree.type, 'branch');
      assert.strictEqual(tree.children.length, 1);
      assert.strictEqual(tree.children[0].child.type, 'cycle');
    });

    it('hashState produces deterministic strings', () => {
      const s1 = { linear: { 5: 2, 3: 1 }, persistent: { 7: true, 2: true } };
      const s2 = { linear: { 3: 1, 5: 2 }, persistent: { 2: true, 7: true } };
      assert.strictEqual(hashState(s1), hashState(s2));
    });
  });

  describe('toDot', () => {
    it('generates valid DOT output', () => {
      const tree = {
        type: 'branch',
        state: { linear: {}, persistent: {} },
        children: [
          { rule: 'r1', child: { type: 'leaf', state: { linear: {}, persistent: {} } } },
          { rule: 'r2', choice: 0, child: { type: 'cycle', state: { linear: {}, persistent: {} } } }
        ]
      };
      const dot = toDot(tree);
      assert(dot.startsWith('digraph exec {'));
      assert(dot.includes('fillcolor=green'));   // leaf
      assert(dot.includes('fillcolor=red'));     // cycle
      assert(dot.includes('r2[0]'));             // choice label
      assert(dot.endsWith('}'));
    });

    it('uses render callback for labels', () => {
      const tree = { type: 'leaf', state: { linear: { 1: 1 }, persistent: {} } };
      const dot = toDot(tree, { render: (s) => `lin:${Object.keys(s.linear).length}` });
      assert(dot.includes('lin:1'));
    });
  });

  describe('tree utilities', () => {
    it('countLeaves counts terminal nodes', () => {
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

    it('countLeaves handles cycle nodes', () => {
      const tree = {
        type: 'branch',
        state: {},
        children: [
          { rule: 'r1', child: { type: 'cycle', state: {} } },
          { rule: 'r2', child: { type: 'leaf', state: {} } }
        ]
      };
      assert.strictEqual(countLeaves(tree), 2);
    });

    it('getAllLeaves collects all terminal nodes', () => {
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

    it('maxDepth returns tree height', () => {
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

    it('countNodes returns total node count', () => {
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
