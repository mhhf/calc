/**
 * Comprehensive tests for ManualProofAPI logic
 *
 * Tests rule suggestions and proof flows in both focused and unfocused modes.
 * Uses the core API directly (no UI dependency).
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/v2/calculus');
const { createManualProofAPI } = require('../lib/v2/prover/manual');
const Seq = require('../lib/v2/kernel/sequent');
const Store = require('../lib/v2/kernel/store');

describe('ManualProofAPI - Rule Suggestions', () => {
  let calc, AST, api;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    api = createManualProofAPI(calc);
  });

  // Helper: create sequent from AST formulas
  const mkSeq = (linear, succ) => Seq.fromArrays(linear, [], succ);
  const mkSeqCart = (linear, cart, succ) => Seq.fromArrays(linear, cart, succ);

  // Helper: get action names from state
  const ruleNames = (state, opts) =>
    api.getApplicableActions(state, opts)
      .filter(a => a.type === 'rule')
      .map(a => a.name)
      .sort();

  const focusTargets = (state, opts) =>
    api.getApplicableActions(state, opts)
      .filter(a => a.type === 'focus')
      .map(a => ({ name: a.name, pos: a.position, idx: a.index }));

  const allActionNames = (state, opts) =>
    api.getApplicableActions(state, opts).map(a => a.name).sort();

  // =========================================================================
  // Unfocused mode: all structurally applicable rules
  // =========================================================================
  describe('unfocused mode', () => {
    it('identity: A |- A', () => {
      const A = AST.freevar('A');
      const state = api.createProofState(mkSeq([A], A));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['id']);
    });

    it('loli on right: |- A -o B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.loli(A, B)));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['loli_r']);
    });

    it('loli on left: A -o B |- C', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.loli(A, B)], C));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['loli_l']);
    });

    it('tensor on right: |- A * B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.tensor(A, B)));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['tensor_r']);
    });

    it('tensor on left: A * B |- C', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.tensor(A, B)], C));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['tensor_l']);
    });

    it('with on right: |- A & B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.with(A, B)));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['with_r']);
    });

    it('with on left: A & B |- C', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.with(A, B)], C));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['with_l1', 'with_l2']);
    });

    it('distribution: P -o (R & Q) |- (P -o Q) & (P -o R)', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const state = api.createProofState(mkSeq(
        [AST.loli(P, AST.with(R, Q))],
        AST.with(AST.loli(P, Q), AST.loli(P, R))
      ));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['loli_l', 'with_r']);
    });

    it('no Focus actions in unfocused mode', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([AST.loli(A, B)], AST.freevar('C')));
      const focuses = focusTargets(state, { mode: 'unfocused' });
      assert.strictEqual(focuses.length, 0, 'No focus actions in unfocused mode');
    });

    it('multiple context formulas: A -o B, C * D |- E', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const D = AST.freevar('D');
      const E = AST.freevar('E');
      const state = api.createProofState(mkSeq(
        [AST.loli(A, B), AST.tensor(C, D)],
        E
      ));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['loli_l', 'tensor_l']);
    });

    it('atoms only: P, Q |- R - no rules', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const state = api.createProofState(mkSeq([P, Q], R));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, []);
    });

    it('one on right: |- I', () => {
      const state = api.createProofState(mkSeq([], AST.one()));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['one_r']);
    });

    it('one on left: I |- C', () => {
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.one()], C));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['one_l']);
    });

    it('bang on right: |- !A', () => {
      const A = AST.freevar('A');
      const state = api.createProofState(mkSeq([], AST.bang(A)));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['bang_r']);
    });

    it('bang on left: !A |- C', () => {
      const A = AST.freevar('A');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.bang(A)], C));
      const names = ruleNames(state, { mode: 'unfocused' });
      assert.deepStrictEqual(names, ['bang_l']);
    });
  });

  // =========================================================================
  // Focused mode: inversion phase
  // =========================================================================
  describe('focused mode - inversion phase', () => {
    it('with_r invertible: (P -o Q) & (P -o R) on right', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const state = api.createProofState(mkSeq(
        [AST.loli(P, AST.with(R, Q))],
        AST.with(AST.loli(P, Q), AST.loli(P, R))
      ));
      const names = ruleNames(state, { mode: 'focused' });
      assert.deepStrictEqual(names, ['with_r'], 'Only invertible with_r in inversion');
    });

    it('Focus_L on loli in inversion', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const state = api.createProofState(mkSeq(
        [AST.loli(P, AST.with(R, Q))],
        AST.with(AST.loli(P, Q), AST.loli(P, R))
      ));
      const focuses = focusTargets(state, { mode: 'focused' });
      assert.strictEqual(focuses.length, 1, 'One focus target');
      assert.strictEqual(focuses[0].pos, 'L');
      assert.strictEqual(focuses[0].idx, 0);
      assert.strictEqual(focuses[0].name, 'Focus_L');
    });

    it('loli_r invertible on right', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.loli(A, B)));
      const names = ruleNames(state, { mode: 'focused' });
      assert.deepStrictEqual(names, ['loli_r']);
    });

    it('tensor_l invertible on left', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.tensor(A, B)], C));
      const names = ruleNames(state, { mode: 'focused' });
      assert.deepStrictEqual(names, ['tensor_l']);
    });

    it('tensor_r NOT shown (not invertible)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.tensor(A, B)));
      const names = ruleNames(state, { mode: 'focused' });
      assert.deepStrictEqual(names, [], 'tensor_r is not invertible');
      // But Focus_R should be shown
      const focuses = focusTargets(state, { mode: 'focused' });
      assert.ok(focuses.some(f => f.pos === 'R'), 'Focus_R should be offered');
    });

    it('loli_l NOT shown in inversion (not invertible)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.loli(A, B)], C));
      const names = ruleNames(state, { mode: 'focused' });
      assert.deepStrictEqual(names, [], 'loli_l is not invertible');
      const focuses = focusTargets(state, { mode: 'focused' });
      assert.ok(focuses.some(f => f.pos === 'L'), 'Focus_L should be offered');
    });

    it('Focus_R on atom', () => {
      const A = AST.freevar('A');
      const state = api.createProofState(mkSeq([A], A));
      const focuses = focusTargets(state, { mode: 'focused' });
      assert.ok(focuses.some(f => f.pos === 'R'), 'Focus_R on atom');
    });
  });

  // =========================================================================
  // Focused mode: focused phase (after applying Focus)
  // =========================================================================
  describe('focused mode - focused phase', () => {
    it('loli_l after Focus_L on loli', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const loli = AST.loli(A, B);
      const state = api.createProofState(mkSeq([loli, C], AST.freevar('D')));

      // Apply Focus_L
      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const focusAction = actions.find(a => a.type === 'focus' && a.position === 'L' && a.index === 0);
      assert.ok(focusAction, 'Focus_L on loli should be available');

      const afterFocus = api.applyAction(state, focusAction);
      const childState = afterFocus.premisses[0];
      assert.ok(childState.focus, 'Child should have focus set');

      // After focus: only loli_l should be shown
      const focusedActions = api.getApplicableActions(childState, { mode: 'focused' });
      const rnames = focusedActions.filter(a => a.type === 'rule').map(a => a.name);
      assert.deepStrictEqual(rnames, ['loli_l'], 'Only loli_l in focused phase');

      // No Focus actions when already focused
      const focusActionsAfter = focusedActions.filter(a => a.type === 'focus');
      assert.strictEqual(focusActionsAfter.length, 0, 'No Focus when already focused');
    });

    it('tensor_r after Focus_R on tensor', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const tensor = AST.tensor(A, B);
      const state = api.createProofState(mkSeq([A, B], tensor));

      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const focusAction = actions.find(a => a.type === 'focus' && a.position === 'R');
      assert.ok(focusAction, 'Focus_R on tensor should be available');

      const afterFocus = api.applyAction(state, focusAction);
      const childState = afterFocus.premisses[0];

      const focusedActions = api.getApplicableActions(childState, { mode: 'focused' });
      const rnames = focusedActions.filter(a => a.type === 'rule').map(a => a.name);
      assert.deepStrictEqual(rnames, ['tensor_r']);
    });

    it('with_l1/with_l2 after Focus_L on with', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const w = AST.with(A, B);
      const state = api.createProofState(mkSeq([w], C));

      // with is negative → focusable on left
      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const focusAction = actions.find(a => a.type === 'focus' && a.position === 'L');
      assert.ok(focusAction, 'Focus_L on with should be available');

      const afterFocus = api.applyAction(state, focusAction);
      const childState = afterFocus.premisses[0];

      const focusedActions = api.getApplicableActions(childState, { mode: 'focused' });
      const rnames = focusedActions.filter(a => a.type === 'rule').map(a => a.name).sort();
      assert.deepStrictEqual(rnames, ['with_l1', 'with_l2']);
    });

    it('id after Focus_R on atom matching context', () => {
      const A = AST.freevar('A');
      const state = api.createProofState(mkSeq([A], A));

      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const focusAction = actions.find(a => a.type === 'focus' && a.position === 'R');
      assert.ok(focusAction, 'Focus_R on atom');

      const afterFocus = api.applyAction(state, focusAction);
      const childState = afterFocus.premisses[0];

      const focusedActions = api.getApplicableActions(childState, { mode: 'focused' });
      const rnames = focusedActions.filter(a => a.type === 'rule').map(a => a.name);
      assert.deepStrictEqual(rnames, ['id']);
    });
  });

  // =========================================================================
  // Context splitting
  // =========================================================================
  describe('context splitting', () => {
    it('loli_l needs split when extra context', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const D = AST.freevar('D');
      const loli = AST.loli(A, B);
      const state = api.createProofState(mkSeq([loli, C], D));
      state.focus = { position: 'L', index: 0, hash: loli };

      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const loliL = actions.find(a => a.name === 'loli_l');
      assert.ok(loliL, 'loli_l available');
      assert.strictEqual(loliL.needsContextSplit, true, 'needs split');
      assert.strictEqual(loliL.contextEntries.length, 1, '1 entry (C)');
    });

    it('loli_l no split when only principal', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const loli = AST.loli(A, B);
      const state = api.createProofState(mkSeq([loli], C));
      state.focus = { position: 'L', index: 0, hash: loli };

      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const loliL = actions.find(a => a.name === 'loli_l');
      assert.ok(loliL, 'loli_l available');
      assert.strictEqual(loliL.needsContextSplit, false, 'no split needed');
    });

    it('tensor_r needs split when context present', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const tensor = AST.tensor(A, B);
      const state = api.createProofState(mkSeq([C], tensor));
      // In unfocused mode, tensor_r shows directly
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const tensorR = actions.find(a => a.name === 'tensor_r');
      assert.ok(tensorR, 'tensor_r available');
      assert.strictEqual(tensorR.needsContextSplit, true, 'needs split (C in context)');
    });

    it('tensor_r no split when empty context', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const tensor = AST.tensor(A, B);
      const state = api.createProofState(mkSeq([], tensor));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const tensorR = actions.find(a => a.name === 'tensor_r');
      assert.ok(tensorR, 'tensor_r available');
      assert.strictEqual(tensorR.needsContextSplit, false, 'no split (empty context)');
    });

    it('with_r copies context (no split)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const w = AST.with(A, B);
      const state = api.createProofState(mkSeq([C], w));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const withR = actions.find(a => a.name === 'with_r');
      assert.ok(withR, 'with_r available');
      assert.strictEqual(withR.needsContextSplit, false, 'with_r copies context, no split');
      assert.strictEqual(withR.copyContext, true);
    });
  });

  // =========================================================================
  // Premise computation
  // =========================================================================
  describe('premise computation', () => {
    it('with_r produces two premises with same context', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const state = api.createProofState(mkSeq(
        [AST.loli(P, AST.with(R, Q))],
        AST.with(AST.loli(P, Q), AST.loli(P, R))
      ));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const withR = actions.find(a => a.name === 'with_r');
      assert.ok(withR, 'with_r available');
      assert.strictEqual(withR.premises.length, 2, '2 premises');

      // Both premises should have the loli in their context
      const p1Linear = Seq.getContext(withR.premises[0], 'linear');
      const p2Linear = Seq.getContext(withR.premises[1], 'linear');
      assert.strictEqual(p1Linear.length, 1, 'premise 1 has 1 context formula');
      assert.strictEqual(p2Linear.length, 1, 'premise 2 has 1 context formula');
      // Succedents should be different (P -o Q vs P -o R)
      assert.notStrictEqual(withR.premises[0].succedent, withR.premises[1].succedent);
    });

    it('loli_r adds antecedent to context', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.loli(A, B)));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const loliR = actions.find(a => a.name === 'loli_r');
      assert.ok(loliR, 'loli_r available');
      assert.strictEqual(loliR.premises.length, 1, '1 premise');
      const premiseLinear = Seq.getContext(loliR.premises[0], 'linear');
      assert.strictEqual(premiseLinear.length, 1, 'A added to context');
      assert.strictEqual(premiseLinear[0], A, 'A is in context');
      assert.strictEqual(loliR.premises[0].succedent, B, 'succedent is B');
    });

    it('tensor_l decomposes into components', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const state = api.createProofState(mkSeq([AST.tensor(A, B)], C));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const tensorL = actions.find(a => a.name === 'tensor_l');
      assert.ok(tensorL, 'tensor_l available');
      assert.strictEqual(tensorL.premises.length, 1, '1 premise');
      const premiseLinear = Seq.getContext(tensorL.premises[0], 'linear');
      assert.strictEqual(premiseLinear.length, 2, 'A and B in context');
    });

    it('one_r closes goal (no premises)', () => {
      const state = api.createProofState(mkSeq([], AST.one()));
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const oneR = actions.find(a => a.name === 'one_r');
      assert.ok(oneR, 'one_r available');
      assert.strictEqual(oneR.premises.length, 0, 'no premises');
      assert.strictEqual(oneR.closesGoal, true);
    });
  });

  // =========================================================================
  // Action application
  // =========================================================================
  describe('action application', () => {
    it('applyAction with focus creates child with focus state', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const loli = AST.loli(A, B);
      const state = api.createProofState(mkSeq([loli], AST.freevar('C')));

      const actions = api.getApplicableActions(state, { mode: 'focused' });
      const focusAction = actions.find(a => a.type === 'focus' && a.position === 'L');
      assert.ok(focusAction, 'Focus_L available');
      const newState = api.applyAction(state, focusAction);

      assert.strictEqual(newState.rule, 'Focus_L');
      assert.strictEqual(newState.premisses.length, 1);
      assert.ok(newState.premisses[0].focus, 'child has focus');
      assert.strictEqual(newState.premisses[0].focus.position, 'L');
    });

    it('applyAction with rule creates children', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const state = api.createProofState(mkSeq([], AST.loli(A, B)));

      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const loliR = actions.find(a => a.name === 'loli_r');
      const newState = api.applyAction(state, loliR);

      assert.strictEqual(newState.rule, 'loli_r');
      assert.strictEqual(newState.premisses.length, 1);
      assert.strictEqual(newState.premisses[0].focus, null, 'no focus after rule');
    });

    it('applyAction with id closes goal', () => {
      const A = AST.freevar('A');
      const state = api.createProofState(mkSeq([A], A));

      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const id = actions.find(a => a.name === 'id');
      const newState = api.applyAction(state, id);

      assert.strictEqual(newState.rule, 'id');
      assert.strictEqual(newState.premisses.length, 0);
      assert.strictEqual(newState.proven, true);
    });
  });
});
