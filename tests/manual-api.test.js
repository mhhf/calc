/**
 * Test ManualProofAPI - single source of truth for interactive proofs
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/calculus');
const { createManualProofAPI } = require('../lib/prover/strategy/manual');
const Seq = require('../lib/kernel/sequent');
const Store = require('../lib/kernel/store');

describe('ManualProofAPI', () => {
  let calc;
  let api;

  before(async () => {
    calc = await calculus.loadILL();
    api = createManualProofAPI(calc);
  });

  describe('state creation', () => {
    it('should create initial proof state', () => {
      // Create test sequent: A -o B, C |- D
      const A = Store.put('atom', ['A']);
      const B = Store.put('atom', ['B']);
      const C = Store.put('atom', ['C']);
      const D = Store.put('atom', ['D']);
      const loli = Store.put('loli', [A, B]);
      const seq = Seq.fromArrays([loli, C], [], D);

      const state = api.createProofState(seq);
      assert.strictEqual(state.focus, null, 'Initial state should have no focus');
      assert.ok(state.conclusion, 'State should have conclusion');
      assert.strictEqual(state.premisses.length, 0, 'Initial state has no premises');
    });
  });

  describe('applicable actions', () => {
    it('should show focus actions in inversion phase', () => {
      const A = Store.put('atom', ['A']);
      const B = Store.put('atom', ['B']);
      const C = Store.put('atom', ['C']);
      const D = Store.put('atom', ['D']);
      const loli = Store.put('loli', [A, B]);
      const seq = Seq.fromArrays([loli, C], [], D);

      const state = api.createProofState(seq);
      const actions = api.getApplicableActions(state);

      // Should have focus actions (loli is negative, focusable on left)
      const focusActions = actions.filter(a => a.type === 'focus');
      assert.ok(focusActions.length > 0, 'Should have focus actions');

      const focusAtZero = focusActions.find(a => a.index === 0);
      assert.ok(focusAtZero, 'Should have focus action for loli at index 0');
    });

    it('should show loli_l after focusing', () => {
      const A = Store.put('atom', ['A']);
      const B = Store.put('atom', ['B']);
      const C = Store.put('atom', ['C']);
      const D = Store.put('atom', ['D']);
      const loli = Store.put('loli', [A, B]);
      const seq = Seq.fromArrays([loli, C], [], D);

      const state = api.createProofState(seq);
      const actions = api.getApplicableActions(state);

      // Apply focus on loli
      const focusAction = actions.find(a => a.type === 'focus' && a.index === 0);
      assert.ok(focusAction, 'Should find focus action');

      const focusedState = api.applyAction(state, focusAction);
      assert.ok(focusedState.premisses[0].focus, 'Child state should have focus');

      // Get actions with focus
      const childState = focusedState.premisses[0];
      const focusedActions = api.getApplicableActions(childState);

      const loliRule = focusedActions.find(a => a.name === 'loli_l');
      assert.ok(loliRule, 'Should have loli_l action');
      assert.strictEqual(loliRule.needsContextSplit, true, 'loli_l should need context split');
    });
  });

  describe('context entries for split', () => {
    it('should provide context entries for splitting rules', () => {
      const A = Store.put('atom', ['A']);
      const B = Store.put('atom', ['B']);
      const C = Store.put('atom', ['C']);
      const D = Store.put('atom', ['D']);
      const loli = Store.put('loli', [A, B]);
      const seq = Seq.fromArrays([loli, C], [], D);

      const state = api.createProofState(seq);
      state.focus = { position: 'L', index: 0, hash: loli };

      const actions = api.getApplicableActions(state);
      const loliRule = actions.find(a => a.name === 'loli_l');

      assert.ok(loliRule, 'Should have loli_l');
      assert.ok(loliRule.contextEntries, 'Should have context entries');
      assert.strictEqual(loliRule.contextEntries.length, 1, 'Should have 1 context entry (C)');
    });
  });

  describe('rendering', () => {
    it('should render sequent with focus highlighting', () => {
      const A = Store.put('atom', ['A']);
      const B = Store.put('atom', ['B']);
      const C = Store.put('atom', ['C']);
      const loli = Store.put('loli', [A, B]);
      const seq = Seq.fromArrays([loli, C], [], C);

      const rendered = api.renderSequent(seq, 'latex', { position: 'L', index: 0 });
      assert.ok(rendered.includes('['), 'Should have focus brackets');
      assert.ok(rendered.includes(']'), 'Should have closing bracket');
    });
  });

  describe('abstract rules', () => {
    it('should provide Focus_L schema', () => {
      const schema = api.getAbstractRule('Focus_L');
      assert.ok(schema.conclusion, 'Should have conclusion');
      assert.ok(schema.premises, 'Should have premises');
      assert.ok(schema.premises.length > 0, 'Focus_L should have premises');
    });

    it('should provide loli_l schema', () => {
      const schema = api.getAbstractRule('loli_l');
      assert.ok(schema.conclusion, 'Should have conclusion');
      assert.ok(schema.premises, 'Should have premises');
      assert.strictEqual(schema.premises.length, 2, 'loli_l should have 2 premises');
    });
  });
});
