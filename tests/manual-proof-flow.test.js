/**
 * Integration tests for manual proof flows via browser module.
 *
 * Simulates the full UI flow using ASCII sequent parsing.
 * Tests both focused and unfocused complete proof paths.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const browser = require('../lib/browser');
const Seq = require('../lib/kernel/sequent');
const Store = require('../lib/kernel/store');

describe('Manual Proof Flows (browser simulation)', () => {
  let api;

  before(() => {
    const bundle = require('../out/ill.json');
    browser.initFromBundle(bundle);
    api = browser.getManualProofAPI();
  });

  // Helper: parse and create initial state
  const startProof = (input) => {
    const seq = browser.parseSequent(input);
    return api.createProofState(seq);
  };

  // Helper: find rule by name in actions
  const findRule = (actions, name) => actions.find(a => a.name === name);
  const findFocus = (actions, pos) => actions.find(a => a.type === 'focus' && a.position === pos);

  // Helper: render sequent for debug
  const render = (seq) => browser.render(seq, 'ascii');

  // =========================================================================
  // Unfocused mode: complete proofs
  // =========================================================================
  describe('unfocused complete proofs', () => {
    it('identity: P |- P', () => {
      const state = startProof('P |- P');
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const id = findRule(actions, 'id');
      assert.ok(id, 'id available');
      const result = api.applyAction(state, id);
      assert.strictEqual(result.proven, true);
    });

    it('modus ponens: P, P -o Q |- Q', () => {
      let state = startProof('P, P -o Q |- Q');

      // Step 1: loli_l on P -o Q (index 1)
      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const loliL = findRule(actions, 'loli_l');
      assert.ok(loliL, 'loli_l available');
      assert.strictEqual(loliL.needsContextSplit, true, 'P needs to be split');

      // Apply with split: P goes to premise 1
      const p1Hash = Seq.getContext(state.conclusion, 'linear')[0]; // P
      const newState = api.applyAction(state, loliL, {
        split: { premise1: [p1Hash], premise2: [] }
      });
      assert.strictEqual(newState.premisses.length, 2);

      // Premise 1: P |- P → id
      const p1 = newState.premisses[0];
      const p1Actions = api.getApplicableActions(p1, { mode: 'unfocused' });
      assert.ok(findRule(p1Actions, 'id'), 'id on premise 1');

      // Premise 2: Q |- Q → id
      const p2 = newState.premisses[1];
      const p2Actions = api.getApplicableActions(p2, { mode: 'unfocused' });
      assert.ok(findRule(p2Actions, 'id'), 'id on premise 2');
    });

    it('with_r: A |- A & A', () => {
      let state = startProof('A |- A & A');

      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const withR = findRule(actions, 'with_r');
      assert.ok(withR, 'with_r available');

      state = api.applyAction(state, withR);
      assert.strictEqual(state.premisses.length, 2, 'with_r has 2 premises');

      // Both premises should be A |- A
      for (const p of state.premisses) {
        const pActions = api.getApplicableActions(p, { mode: 'unfocused' });
        assert.ok(findRule(pActions, 'id'), 'id on premise');
      }
    });

    it('tensor_l + tensor_r: P * Q |- Q * P', () => {
      let state = startProof('P * Q |- Q * P');

      // Step 1: tensor_l decomposes left
      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const tensorL = findRule(actions, 'tensor_l');
      assert.ok(tensorL, 'tensor_l available');

      state = api.applyAction(state, tensorL);
      assert.strictEqual(state.premisses.length, 1);
      const p1 = state.premisses[0];

      // After tensor_l: P, Q |- Q * P
      let p1Actions = api.getApplicableActions(p1, { mode: 'unfocused' });
      const tensorR = findRule(p1Actions, 'tensor_r');
      assert.ok(tensorR, 'tensor_r available');
      assert.strictEqual(tensorR.needsContextSplit, true, 'P,Q need splitting');
    });

    it('loli_r: |- A -o A', () => {
      let state = startProof('|- A -o A');

      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const loliR = findRule(actions, 'loli_r');
      assert.ok(loliR, 'loli_r available');

      state = api.applyAction(state, loliR);
      assert.strictEqual(state.premisses.length, 1);

      // After loli_r: A |- A → id
      const pActions = api.getApplicableActions(state.premisses[0], { mode: 'unfocused' });
      assert.ok(findRule(pActions, 'id'), 'id available');
    });

    it('one_l + one_r: I |- I', () => {
      let state = startProof('I |- I');

      // id should work directly (I = I)
      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const id = findRule(actions, 'id');
      assert.ok(id, 'id available (I matches I)');
    });
  });

  // =========================================================================
  // Focused mode: complete proofs
  // =========================================================================
  describe('focused complete proofs', () => {
    it('identity via Focus_R: P |- P', () => {
      let state = startProof('P |- P');

      // Inversion: no invertible rules on atoms
      let actions = api.getApplicableActions(state, { mode: 'focused' });
      assert.strictEqual(findRule(actions, 'id'), undefined, 'no id in inversion');

      // Focus_R on P (atom, positive)
      const focusR = findFocus(actions, 'R');
      assert.ok(focusR, 'Focus_R available');

      state = api.applyAction(state, focusR);
      const focused = state.premisses[0];

      // After focus: id should be available
      actions = api.getApplicableActions(focused, { mode: 'focused' });
      const id = findRule(actions, 'id');
      assert.ok(id, 'id available after focus');

      const result = api.applyAction(focused, id);
      assert.strictEqual(result.proven, true);
    });

    it('distribution: P -o (R & Q) |- (P -o Q) & (P -o R)', () => {
      let state = startProof('P -o (R & Q) |- (P -o Q) & (P -o R)');

      // Step 1: Inversion - with_r (& is negative, invertible on right)
      let actions = api.getApplicableActions(state, { mode: 'focused' });
      const withR = findRule(actions, 'with_r');
      assert.ok(withR, 'with_r in inversion');

      state = api.applyAction(state, withR);
      assert.strictEqual(state.premisses.length, 2);

      // Step 2: Both premises have loli_r (invertible on right)
      for (let pi = 0; pi < 2; pi++) {
        let premise = state.premisses[pi];
        actions = api.getApplicableActions(premise, { mode: 'focused' });
        const loliR = findRule(actions, 'loli_r');
        assert.ok(loliR, `loli_r on premise ${pi}`);

        premise = api.applyAction(premise, loliR);
        const innerPremise = premise.premisses[0];

        // After loli_r: context has loli + P, succedent is Q or R
        // Inversion exhausted → Focus_L on loli
        actions = api.getApplicableActions(innerPremise, { mode: 'focused' });
        assert.strictEqual(findRule(actions, 'with_r'), undefined, 'no with_r here');

        const focusL = findFocus(actions, 'L');
        assert.ok(focusL, `Focus_L on loli in premise ${pi}`);
        assert.strictEqual(focusL.name, 'Focus_L');

        // Apply Focus_L
        const afterFocus = api.applyAction(innerPremise, focusL);
        const focusedChild = afterFocus.premisses[0];

        // After focus: loli_l
        actions = api.getApplicableActions(focusedChild, { mode: 'focused' });
        const loliL = findRule(actions, 'loli_l');
        assert.ok(loliL, `loli_l after Focus_L in premise ${pi}`);
      }
    });

    it('with_l1/with_l2 after Focus_L on with', () => {
      let state = startProof('A & B |- A');

      // Inversion: no invertible rules (with is negative, with_l1/l2 not invertible)
      let actions = api.getApplicableActions(state, { mode: 'focused' });
      assert.strictEqual(actions.filter(a => a.type === 'rule').length, 0, 'no rules in inversion');

      // Focus_L on & (negative, focusable on left)
      const focusL = findFocus(actions, 'L');
      assert.ok(focusL, 'Focus_L available');

      state = api.applyAction(state, focusL);
      const focused = state.premisses[0];

      // After focus: with_l1 and with_l2
      actions = api.getApplicableActions(focused, { mode: 'focused' });
      assert.ok(findRule(actions, 'with_l1'), 'with_l1');
      assert.ok(findRule(actions, 'with_l2'), 'with_l2');

      // Apply with_l1
      const withL1 = findRule(actions, 'with_l1');
      const result = api.applyAction(focused, withL1);
      assert.strictEqual(result.premisses.length, 1);

      // Premise: A |- A → Focus_R → id
      const p = result.premisses[0];
      actions = api.getApplicableActions(p, { mode: 'focused' });
      const focusR = findFocus(actions, 'R');
      assert.ok(focusR, 'Focus_R on A');
    });

    it('tensor_r after Focus_R on tensor: A, B |- A * B', () => {
      let state = startProof('A, B |- A * B');

      // Inversion: no invertible rules
      let actions = api.getApplicableActions(state, { mode: 'focused' });
      assert.strictEqual(actions.filter(a => a.type === 'rule').length, 0);

      // Focus_R on tensor (positive, focusable on right)
      const focusR = findFocus(actions, 'R');
      assert.ok(focusR, 'Focus_R on A * B');

      state = api.applyAction(state, focusR);
      const focused = state.premisses[0];

      actions = api.getApplicableActions(focused, { mode: 'focused' });
      const tensorR = findRule(actions, 'tensor_r');
      assert.ok(tensorR, 'tensor_r after Focus_R');
      assert.strictEqual(tensorR.needsContextSplit, true, 'A,B need splitting');
    });
  });

  // =========================================================================
  // Edge cases
  // =========================================================================
  describe('edge cases', () => {
    it('empty context with one_r', () => {
      const state = startProof('|- I');
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const oneR = findRule(actions, 'one_r');
      assert.ok(oneR, 'one_r available');
      assert.strictEqual(oneR.closesGoal, true);
    });

    it('bang dereliction: !A |- A', () => {
      let state = startProof('!A |- A');
      let actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const bangL = findRule(actions, 'bang_l');
      assert.ok(bangL, 'bang_l available');

      state = api.applyAction(state, bangL);
      // After dereliction: A |- A
      const p = state.premisses[0];
      actions = api.getApplicableActions(p, { mode: 'unfocused' });
      assert.ok(findRule(actions, 'id'), 'id after dereliction');
    });

    it('unfocused mode matches auto-prover: distribution is provable', async () => {
      // Verify the auto-prover can prove it (sanity check)
      const result = await browser.proveString('P -o (R & Q) |- (P -o Q) & (P -o R)');
      assert.strictEqual(result.success, true, 'Auto-prover can prove distribution');
    });

    it('unfocused identity + rules: A, A -o B |- B', () => {
      // In unfocused mode, both loli_l and id should be available
      const state = startProof('A, A -o B |- B');
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });

      // id should NOT be available (A != B)
      assert.strictEqual(findRule(actions, 'id'), undefined, 'no id (A != B)');

      // loli_l should be available
      assert.ok(findRule(actions, 'loli_l'), 'loli_l available');
    });

    it('multiple left rules: A * B, C -o D |- E', () => {
      const state = startProof('A * B, C -o D |- E');
      const actions = api.getApplicableActions(state, { mode: 'unfocused' });
      const names = actions.map(a => a.name).sort();
      assert.deepStrictEqual(names, ['loli_l', 'tensor_l'], 'both left rules');
    });
  });
});
