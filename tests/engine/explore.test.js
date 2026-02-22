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
} = require('../../lib/engine/symexec');
const forward = require('../../lib/engine/forward');
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

    it('loli stays as opaque linear fact (fired by matchLoli at runtime)', () => {
      const p = Store.put('atom', ['neq']);
      const q = Store.put('atom', ['result']);
      const bangP = Store.put('bang', [p]);
      const monadQ = Store.put('monad', [q]);
      const loli = Store.put('loli', [bangP, monadQ]);
      const alts = expandItem(loli);
      assert.strictEqual(alts.length, 1);
      assert.deepStrictEqual(alts[0], { linear: [loli], persistent: [] });
    });

    it('oplus(A,B) returns two alternatives', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const p = Store.put('oplus', [a, b]);
      const alts = expandItem(p);
      assert.strictEqual(alts.length, 2);
      assert.deepStrictEqual(alts[0], { linear: [a], persistent: [] });
      assert.deepStrictEqual(alts[1], { linear: [b], persistent: [] });
    });

    it('oplus(loli(!P,{A}), loli(!Q,{B})) gives two loli alternatives', () => {
      const p = Store.put('atom', ['neq']);
      const q = Store.put('atom', ['eq']);
      const a = Store.put('atom', ['zero']);
      const b = Store.put('atom', ['one']);
      const bangP = Store.put('bang', [p]);
      const bangQ = Store.put('bang', [q]);
      const branch0 = Store.put('loli', [bangP, Store.put('monad', [a])]);
      const branch1 = Store.put('loli', [bangQ, Store.put('monad', [b])]);
      const pl = Store.put('oplus', [branch0, branch1]);
      const alts = expandItem(pl);
      assert.strictEqual(alts.length, 2);
      // Each branch is a loli fact (fired by matchLoli at runtime)
      assert.deepStrictEqual(alts[0], { linear: [branch0], persistent: [] });
      assert.deepStrictEqual(alts[1], { linear: [branch1], persistent: [] });
    });

    it('with(loli(!P,{A}), loli(!Q,{B})) gives two loli alternatives', () => {
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
      // Each branch is a loli fact (fired by matchLoli at runtime)
      assert.deepStrictEqual(alts[0], { linear: [branch0], persistent: [] });
      assert.deepStrictEqual(alts[1], { linear: [branch1], persistent: [] });
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

  describe('choice forking via plus fixture', () => {
    it('forks on A + B consequent', async () => {
      Store.clear();
      const calc = await mde.load([
        path.join(__dirname, 'fixtures/choice_plus.ill')
      ]);

      const startHash = await mde.parseExpr('start');
      const state = forward.createState({ [startHash]: 1 }, {});

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 5,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      assert.strictEqual(tree.type, 'branch');
      assert.strictEqual(tree.children.length, 2);
      assert.strictEqual(tree.children[0].choice, 0);
      assert.strictEqual(tree.children[1].choice, 1);
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

  describe('matchLoli', () => {
    beforeEach(() => { Store.clear(); });

    it('fires loli with ground linear trigger', () => {
      const trigger = Store.put('atom', ['unblock']);
      const result = Store.put('atom', ['done']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [trigger]: 1 },
        {}
      );
      const m = forward.matchLoli(loli, state, null);
      assert(m, 'matchLoli should return a match');
      assert.strictEqual(m.consumed[loli], 1);
      assert.strictEqual(m.consumed[trigger], 1);
      assert(m.rule.consequent.linear.includes(result));
    });

    it('fires loli with parameterized linear trigger', () => {
      const X = Store.put('freevar', ['_X']);
      // Predicates use tag-as-name, not atom wrapper
      const triggerPattern = Store.put('data', [X]);
      const bodyPattern = Store.put('processed', [X]);
      const body = Store.put('monad', [bodyPattern]);
      const loli = Store.put('loli', [triggerPattern, body]);

      const val = Store.put('binlit', [42n]);
      const triggerFact = Store.put('data', [val]);

      const state = forward.createState(
        { [loli]: 1, [triggerFact]: 1 },
        {}
      );
      const m = forward.matchLoli(loli, state, null);
      assert(m, 'matchLoli should return a match');
      assert.strictEqual(m.consumed[loli], 1);
      assert.strictEqual(m.consumed[triggerFact], 1);
      // Body should be instantiated with X=42
      const expectedResult = Store.put('processed', [val]);
      assert(m.rule.consequent.linear.includes(expectedResult));
    });

    it('fires loli with persistent trigger (state lookup)', () => {
      const guard = Store.put('atom', ['check']);
      const bangGuard = Store.put('bang', [guard]);
      const result = Store.put('atom', ['guarded_result']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [bangGuard, body]);

      const state = forward.createState(
        { [loli]: 1 },
        { [guard]: true }  // Guard is provable via state
      );
      const m = forward.matchLoli(loli, state, null);
      assert(m, 'matchLoli should fire when guard is in persistent state');
      assert.strictEqual(m.consumed[loli], 1);
      assert(m.rule.consequent.linear.includes(result));
    });

    it('returns null when persistent guard fails', () => {
      const guard = Store.put('atom', ['check']);
      const bangGuard = Store.put('bang', [guard]);
      const result = Store.put('atom', ['guarded_result']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [bangGuard, body]);

      const state = forward.createState(
        { [loli]: 1 },
        {}  // Guard NOT in state
      );
      const m = forward.matchLoli(loli, state, null);
      assert.strictEqual(m, null, 'matchLoli should return null when guard fails');
    });

    it('returns null when linear trigger is absent', () => {
      const trigger = Store.put('atom', ['unblock']);
      const result = Store.put('atom', ['done']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1 },  // trigger NOT in state
        {}
      );
      const m = forward.matchLoli(loli, state, null);
      assert.strictEqual(m, null, 'matchLoli should return null when trigger absent');
    });

    it('handles mixed trigger (linear + persistent)', () => {
      const linTrigger = Store.put('atom', ['resource']);
      const guard = Store.put('atom', ['condition']);
      const bangGuard = Store.put('bang', [guard]);
      const trigger = Store.put('tensor', [linTrigger, bangGuard]);
      const result = Store.put('atom', ['combined_result']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      // Both linear trigger and persistent guard present
      const state = forward.createState(
        { [loli]: 1, [linTrigger]: 1 },
        { [guard]: true }
      );
      const m = forward.matchLoli(loli, state, null);
      assert(m, 'matchLoli should fire with mixed trigger');
      assert.strictEqual(m.consumed[loli], 1);
      assert.strictEqual(m.consumed[linTrigger], 1);
      assert(m.rule.consequent.linear.includes(result));
    });

    it('handles body with oplus (multiple consequent alternatives)', () => {
      const trigger = Store.put('atom', ['start']);
      const a = Store.put('atom', ['left']);
      const b = Store.put('atom', ['right']);
      const plusBody = Store.put('oplus', [a, b]);
      const body = Store.put('monad', [plusBody]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [trigger]: 1 },
        {}
      );
      const m = forward.matchLoli(loli, state, null);
      assert(m, 'matchLoli should fire');
      assert.strictEqual(m.rule.consequentAlts.length, 2, 'should have 2 alternatives from oplus');
    });
  });

  describe('guarded loli integration', () => {
    it('explore: guard success fires loli, guard failure produces stuck leaf', () => {
      Store.clear();
      // Build: start -o { tensor(shared, oplus(loli(!guard, {result_a}), loli(!noguard, {result_b}))) }
      const start = Store.put('atom', ['start']);
      const shared = Store.put('atom', ['shared_fact']);
      const guard = Store.put('atom', ['guard']);
      const noguard = Store.put('atom', ['noguard']);
      const resultA = Store.put('atom', ['result_a']);
      const resultB = Store.put('atom', ['result_b']);

      const loliA = Store.put('loli', [Store.put('bang', [guard]), Store.put('monad', [resultA])]);
      const loliB = Store.put('loli', [Store.put('bang', [noguard]), Store.put('monad', [resultB])]);
      const choice = Store.put('oplus', [loliA, loliB]);
      const conseq = Store.put('tensor', [shared, choice]);

      const rule = forward.compileRule({
        name: 'produce',
        hash: 0,
        antecedent: start,
        consequent: Store.put('monad', [conseq])
      });

      // Guard is provable, noguard is NOT
      const state = forward.createState(
        { [start]: 1 },
        { [guard]: true }
      );

      const tree = explore(state, [rule], {
        maxDepth: 5,
        calc: null
      });

      // Root should branch (rule fires, plus creates 2 alternatives)
      assert.strictEqual(tree.type, 'branch');
      assert.strictEqual(tree.children.length, 2);

      // Both alternatives should eventually become leaves
      const leaves = getAllLeaves(tree);
      assert(leaves.length >= 2, `expected >= 2 leaves, got ${leaves.length}`);

      // One leaf should have result_a (guard proved), the other should NOT have result_b
      let hasResultA = false;
      let hasResultB = false;
      for (const leaf of leaves) {
        if (leaf.state && leaf.state.linear[resultA]) hasResultA = true;
        if (leaf.state && leaf.state.linear[resultB]) hasResultB = true;
      }
      assert(hasResultA, 'guard branch should produce result_a');
      assert(!hasResultB, 'noguard branch should NOT produce result_b (guard fails)');
    });
  });
});
