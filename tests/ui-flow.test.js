/**
 * Test the UI flow using the refactored proofLogicV2 approach
 * This mimics what the browser does
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');

// Simulate browser module loading
const browser = require('../lib/v2/browser');
const illBundle = require('../out/ill-v2.json');
const Seq = require('../lib/v2/kernel/sequent');
const Store = require('../lib/v2/kernel/store');

describe('UI Flow (browser simulation)', () => {
  before(() => {
    browser.initFromBundle(illBundle);
  });

  describe('getManualProofAPI', () => {
    it('should expose ManualProofAPI', () => {
      const api = browser.getManualProofAPI();
      assert.ok(api, 'Should have ManualProofAPI');
      assert.ok(api.createProofState, 'Should have createProofState');
      assert.ok(api.getApplicableActions, 'Should have getApplicableActions');
      assert.ok(api.applyAction, 'Should have applyAction');
      assert.ok(api.renderSequent, 'Should have renderSequent');
    });
  });

  describe('full proof flow', () => {
    it('should handle focus -> loli_l -> context split flow', () => {
      const api = browser.getManualProofAPI();

      // Parse: P -o (R & Q) |- (P -o Q) & (P -o R)
      const seq = browser.parseSequent('P -o (R & Q) |- (P -o Q) & (P -o R)');
      console.log('Parsed sequent:', browser.render(seq, 'ascii'));

      // Step 1: Create proof state
      const state = api.createProofState(seq);
      assert.ok(state, 'Should create state');
      assert.strictEqual(state.focus, null, 'Initial state has no focus');

      // Step 2: Get applicable actions (no focus)
      let actions = api.getApplicableActions(state);
      console.log('Actions (no focus):', actions.map(a => `${a.name}@${a.position} (${a.type})`));

      // Should have Focus_L action for loli (negative, focusable on left)
      const focusActions = actions.filter(a => a.type === 'focus');
      console.log('Focus actions:', focusActions.length);
      assert.ok(focusActions.length > 0, 'Should have focus actions');

      const focusLoli = focusActions.find(a => a.position === 'L' && a.index === 0);
      assert.ok(focusLoli, 'Should be able to focus on loli (index 0)');

      // Step 3: Apply Focus
      const focusedState = api.applyAction(state, focusLoli);
      assert.ok(focusedState.premisses[0], 'Should have child state');
      assert.ok(focusedState.premisses[0].focus, 'Child should have focus');
      console.log('After focus, child focus:', focusedState.premisses[0].focus);

      // Step 4: Get actions with focus
      const childState = focusedState.premisses[0];
      actions = api.getApplicableActions(childState);
      console.log('Actions (with focus):', actions.map(a => `${a.name}@${a.position}${a.needsContextSplit ? ' [SPLIT]' : ''}`));

      // Should have loli_l (and NOT Focus actions!)
      const loliL = actions.find(a => a.name === 'loli_l');
      assert.ok(loliL, 'Should have loli_l');

      // CRITICAL: Should NOT have Focus actions when already focused
      const focusActionsAfter = actions.filter(a => a.type === 'focus');
      assert.strictEqual(focusActionsAfter.length, 0, 'Should NOT have Focus actions when already focused!');

      // Check barePremises
      assert.ok(loliL.barePremises, 'Should have barePremises');
      assert.strictEqual(loliL.barePremises.length, 2, 'loli_l has 2 premises');
      console.log('loli_l barePremises:', loliL.barePremises.map(p => browser.render(p, 'ascii')));

      // Step 5: Check rendering with focus
      const rendered = api.renderSequent(seq, 'latex', { position: 'L', index: 0 });
      console.log('Rendered with focus:', rendered);
      assert.ok(rendered.includes('['), 'Should have focus brackets');
    });

    it('should need context split when there is remaining context', () => {
      const api = browser.getManualProofAPI();

      // Parse: P -o Q, R |- S  (R is extra context that needs splitting)
      const seq = browser.parseSequent('P -o Q, R |- S');
      console.log('Parsed sequent:', browser.render(seq, 'ascii'));

      const state = api.createProofState(seq);

      // Set focus on loli (index 0)
      state.focus = { position: 'L', index: 0, hash: null };

      const actions = api.getApplicableActions(state);
      const loliL = actions.find(a => a.name === 'loli_l');

      assert.ok(loliL, 'Should have loli_l');
      console.log('loli_l needsContextSplit:', loliL.needsContextSplit);
      console.log('loli_l contextEntries:', loliL.contextEntries);

      assert.strictEqual(loliL.needsContextSplit, true, 'loli_l SHOULD need split (R in context)');
      assert.ok(loliL.contextEntries, 'Should have context entries');
      assert.strictEqual(loliL.contextEntries.length, 1, 'Should have 1 entry (R)');
    });
  });

  describe('Focus_L schema', () => {
    it('should have correct premise/conclusion orientation', () => {
      const api = browser.getManualProofAPI();
      const schema = api.getAbstractRule('Focus_L');

      console.log('Focus_L schema:', schema);

      // Conclusion is UNFOCUSED (what we start with)
      // Premise is FOCUSED (what we prove next)
      assert.ok(!schema.conclusion.includes('['), 'Conclusion should be unfocused (no brackets)');
      assert.ok(schema.premises[0].includes('['), 'Premise should be focused (has brackets)');
    });
  });

  describe('context split scenarios', () => {
    it('should NOT need split when only principal formula in context', () => {
      const api = browser.getManualProofAPI();

      // Only loli in context - nothing to split after removing principal
      const seq = browser.parseSequent('P -o (R & Q) |- (P -o Q) & (P -o R)');
      const state = api.createProofState(seq);
      state.focus = { position: 'L', index: 0, hash: null };

      const actions = api.getApplicableActions(state);
      const loliL = actions.find(a => a.name === 'loli_l');

      assert.ok(loliL, 'Should have loli_l');
      console.log('Only principal - needsContextSplit:', loliL.needsContextSplit);
      console.log('Only principal - contextEntries:', loliL.contextEntries?.length || 0);

      // No extra context, so no split needed
      assert.strictEqual(loliL.needsContextSplit, false, 'Should NOT need split (no extra context)');
    });

    it('should NEED split when extra context exists', () => {
      const api = browser.getManualProofAPI();

      // P -o Q plus R in context - R needs to be distributed
      const seq = browser.parseSequent('P -o Q, R |- S');
      const state = api.createProofState(seq);
      state.focus = { position: 'L', index: 0, hash: null };

      const actions = api.getApplicableActions(state);
      const loliL = actions.find(a => a.name === 'loli_l');

      assert.ok(loliL, 'Should have loli_l');
      console.log('Extra context - needsContextSplit:', loliL.needsContextSplit);
      console.log('Extra context - contextEntries:', loliL.contextEntries);

      // R is extra context that needs splitting
      assert.strictEqual(loliL.needsContextSplit, true, 'Should need split (R is extra context)');
      assert.strictEqual(loliL.contextEntries.length, 1, 'Should have 1 entry to split');
      assert.strictEqual(loliL.contextEntries[0].formula, 'R', 'Entry should be R');
    });

    it('should NEED split with multiple extra context formulas', () => {
      const api = browser.getManualProofAPI();

      // P -o Q plus R, S in context - both need distributing
      const seq = browser.parseSequent('P -o Q, R, S |- T');
      const state = api.createProofState(seq);
      state.focus = { position: 'L', index: 0, hash: null };

      const actions = api.getApplicableActions(state);
      const loliL = actions.find(a => a.name === 'loli_l');

      assert.ok(loliL, 'Should have loli_l');
      console.log('Multiple extra - needsContextSplit:', loliL.needsContextSplit);
      console.log('Multiple extra - contextEntries:', loliL.contextEntries);

      assert.strictEqual(loliL.needsContextSplit, true, 'Should need split');
      assert.strictEqual(loliL.contextEntries.length, 2, 'Should have 2 entries to split (R, S)');
    });
  });
});
