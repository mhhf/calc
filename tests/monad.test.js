/**
 * Tests for Lax Monad {A} — Phase 2 + Phase 3 (rightFocus)
 *
 * Covers: parser, polarity/invertibility, stickiness, mode switch,
 * committed choice, kernel verification, bridge, rightFocus, integration.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../lib/calculus');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const { createGenericProver } = require('../lib/prover/generic');
const { createKernel } = require('../lib/prover/kernel');
const { createProver } = require('../lib/prover/focused');
const { initRuleSpecs } = require('../lib/prover/rule-interpreter');
const { sequentToState, stateToContext, rightFocus, executeModeSwitch } = require('../lib/prover/bridge');
const { compileRule } = require('../lib/engine/compile');

let ill, AST, parse, render;

before(async () => {
  Store.clear();
  ill = await calculus.loadILL();
  AST = ill.AST;
  parse = ill.parse;
  render = ill.render;
});

// =========================================================================
// 1. Parser
// =========================================================================

describe('Monad parser', () => {
  it('parses standalone {A}', () => {
    const h = parse('{A}');
    const n = Store.get(h);
    assert.strictEqual(n.tag, 'monad');
    const inner = Store.get(n.children[0]);
    assert.strictEqual(inner.tag, 'freevar');
    assert.strictEqual(inner.children[0], 'A');
  });

  it('parses A -o {B} as loli(A, monad(B))', () => {
    const h = parse('A -o {B}');
    const n = Store.get(h);
    assert.strictEqual(n.tag, 'loli');
    const rhs = Store.get(n.children[1]);
    assert.strictEqual(rhs.tag, 'monad');
  });

  it('parses {A * B} as monad(tensor(A,B))', () => {
    const h = parse('{A * B}');
    const n = Store.get(h);
    assert.strictEqual(n.tag, 'monad');
    const inner = Store.get(n.children[0]);
    assert.strictEqual(inner.tag, 'tensor');
  });

  it('parses {{A}} as nested monad', () => {
    const h = parse('{{A}}');
    const n = Store.get(h);
    assert.strictEqual(n.tag, 'monad');
    const inner = Store.get(n.children[0]);
    assert.strictEqual(inner.tag, 'monad');
  });

  it('renders monad correctly', () => {
    const h = parse('{A}');
    assert.strictEqual(render(h), '{ A }');
  });

  it('renders A -o {B} correctly', () => {
    const h = parse('A -o {B}');
    assert.strictEqual(render(h), 'A -o { B }');
  });
});

// =========================================================================
// 2. Polarity & invertibility
// =========================================================================

describe('Monad polarity and invertibility', () => {
  it('monad has negative polarity', () => {
    assert.strictEqual(ill.polarity.monad, 'negative');
  });

  it('monad_r is invertible', () => {
    assert.strictEqual(ill.invertible.monad_r, true);
  });

  it('monad_l is not invertible', () => {
    assert.strictEqual(ill.invertible.monad_l, false);
  });

  it('monad_l is focusable on the left', () => {
    // Negative connective → focusable on left (not invertible on left)
    assert.strictEqual(ill.isNegative('monad'), true);
  });
});

// =========================================================================
// 3. Stickiness
// =========================================================================

describe('Monad stickiness', () => {
  it('monad_l spec has requiresSuccedentTag flag', () => {
    const { specs } = initRuleSpecs(ill);
    assert.strictEqual(specs.monad_l.requiresSuccedentTag, 'monad');
  });

  it('monad_l is blocked when succedent is non-monadic', () => {
    const generic = createGenericProver(ill);
    const { specs } = initRuleSpecs(ill);

    // Create sequent: {A} |- B (succedent is just freevar, not monadic)
    const monadA = AST.monad(AST.freevar('A'));
    const seq = Seq.fromArrays([monadA], [], AST.freevar('B'));

    const result = generic.applyRule(seq, 'L', 0, specs.monad_l);
    assert.strictEqual(result, null, 'monad_l should be blocked on non-monadic succedent');
  });

  it('monad_l succeeds when succedent is monadic', () => {
    const generic = createGenericProver(ill);
    const { specs } = initRuleSpecs(ill);

    // Create sequent: {A} |- {B} (succedent is monadic)
    const monadA = AST.monad(AST.freevar('A'));
    const monadB = AST.monad(AST.freevar('B'));
    const seq = Seq.fromArrays([monadA], [], monadB);

    const result = generic.applyRule(seq, 'L', 0, specs.monad_l);
    assert.ok(result?.success, 'monad_l should succeed when succedent is monadic');
  });

  it('monad_l produces correct premise', () => {
    const generic = createGenericProver(ill);
    const { specs } = initRuleSpecs(ill);

    // {A} |- {B} → A |- {B}
    const a = AST.freevar('A');
    const b = AST.freevar('B');
    const monadA = AST.monad(a);
    const monadB = AST.monad(b);
    const seq = Seq.fromArrays([monadA], [], monadB);

    const result = generic.applyRule(seq, 'L', 0, specs.monad_l);
    assert.ok(result?.success);
    assert.strictEqual(result.premises.length, 1);

    // Premise should have A in linear context (unwrapped from monad)
    const premLinear = Seq.getContext(result.premises[0], 'linear');
    assert.ok(premLinear.includes(a), 'premise should contain A (unwrapped)');
  });

  it('chooseFocus does not offer monad for right focus (negative connective)', () => {
    const focused = createProver(ill);

    // Create sequent: a |- {B} (monadic succedent)
    const monadB = AST.monad(AST.freevar('B'));
    const a = AST.atom('a');
    const seq = Seq.fromArrays([a], [], monadB);

    const choices = focused.chooseFocus(seq);
    // monad is negative → right focus should NOT be offered (it's invertible on right)
    const rightChoices = choices.filter(c => c.position === 'R');
    assert.strictEqual(rightChoices.length, 0,
      'monad (negative) should not be offered for right focus');
  });
});

// =========================================================================
// 4. Mode switch
// =========================================================================

describe('Monad mode switch', () => {
  it('monad_r spec has modeShift flag', () => {
    const { specs } = initRuleSpecs(ill);
    assert.strictEqual(specs.monad_r.modeShift, true);
  });

  it('findInvertible finds monad_r on monadic succedent', () => {
    const focused = createProver(ill);
    const monadA = AST.monad(AST.freevar('A'));
    const a = AST.atom('a');
    const seq = Seq.fromArrays([a], [], monadA);

    const inv = focused.findInvertible(seq);
    assert.ok(inv, 'should find invertible rule');
    assert.strictEqual(inv.position, 'R');
    assert.strictEqual(inv.formula, monadA);
  });

  it('executeModeSwitch returns null without forwardRules', () => {
    const a = AST.atom('a');
    const monadA = AST.monad(a);
    const seq = Seq.fromArrays([a], [], monadA);

    const result = executeModeSwitch(seq, null);
    assert.strictEqual(result, null);
  });

  it('executeModeSwitch returns null with empty forwardRules', () => {
    const a = AST.atom('a');
    const monadA = AST.monad(a);
    const seq = Seq.fromArrays([a], [], monadA);

    const result = executeModeSwitch(seq, { forwardRules: [] });
    assert.strictEqual(result, null);
  });

  it('executeModeSwitch with simple forward rule produces result', () => {
    // Build a simple forward rule: a -o {b}
    const a = AST.atom('a');
    const b = AST.atom('b');
    const ruleH = AST.loli(a, AST.monad(b));
    const compiled = compileRule({
      name: 'test_rule',
      hash: ruleH,
      antecedent: a,
      consequent: AST.monad(b)
    });

    const monadB = AST.monad(b);
    const seq = Seq.fromArrays([a], [], monadB);

    const result = executeModeSwitch(seq, { forwardRules: [compiled] });
    assert.ok(result, 'should produce a result');
    assert.ok(result.proofNode, 'should have proofNode');
    assert.strictEqual(result.proofNode.rule, 'monad_r');
    assert.strictEqual(result.proofNode.proven, true);
    assert.ok(result.proofNode.state.modeSwitch, 'should have modeSwitch state');
  });
});

// =========================================================================
// 5. Committed choice
// =========================================================================

describe('Monad committed choice', () => {
  it('monad_r returns empty delta (all resources consumed)', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const monadA = AST.monad(a);
    const compiled = compileRule({
      name: 'test_id',
      hash: AST.loli(a, AST.monad(a)),
      antecedent: a,
      consequent: AST.monad(a)
    });

    const seq = Seq.fromArrays([a], [], monadA);
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success, 'proof should succeed');
    assert.strictEqual(result.proofTree.rule, 'monad_r');
  });

  it('monad_r proofNode has zero premises', () => {
    const { specs, alternatives } = initRuleSpecs(ill);
    const a = AST.atom('a');
    const monadA = AST.monad(a);
    const compiled = compileRule({
      name: 'test_id2',
      hash: AST.loli(a, AST.monad(a)),
      antecedent: a,
      consequent: AST.monad(a)
    });

    const focused = createProver(ill);
    const seq = Seq.fromArrays([a], [], monadA);
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success);
    assert.strictEqual(result.proofTree.premises.length, 0,
      'monad_r should have zero premises (mode switch)');
  });
});

// =========================================================================
// 6. Kernel
// =========================================================================

describe('Monad kernel verification', () => {
  it('verifyStep accepts monad_r with monadic succedent', () => {
    const kernel = createKernel(ill);
    const monadA = AST.monad(AST.freevar('A'));
    const a = AST.atom('a');
    const seq = Seq.fromArrays([a], [], monadA);

    const result = kernel.verifyStep(seq, 'monad_r', []);
    assert.ok(result.valid, 'monad_r should be valid');
    assert.strictEqual(result.unverified, 'modeSwitch');
  });

  it('verifyStep rejects monad_r with non-monadic succedent', () => {
    const kernel = createKernel(ill);
    const a = AST.atom('a');
    const seq = Seq.fromArrays([a], [], a);

    const result = kernel.verifyStep(seq, 'monad_r', []);
    assert.strictEqual(result.valid, false);
    assert.ok(result.error.includes('not monadic'));
  });

  it('verifyStep returns evidence: null for monad_r', () => {
    const kernel = createKernel(ill);
    const monadA = AST.monad(AST.freevar('A'));
    const seq = Seq.fromArrays([], [], monadA);

    const result = kernel.verifyStep(seq, 'monad_r', []);
    assert.ok(result.valid);
    assert.strictEqual(result.evidence, null);
  });
});

// =========================================================================
// 7. Bridge
// =========================================================================

describe('Monad bridge', () => {
  it('sequentToState converts linear context to state.linear', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const seq = Seq.fromArrays([a, a, b], [], AST.freevar('X'));

    const state = sequentToState(seq);
    assert.strictEqual(state.linear[a], 2);
    assert.strictEqual(state.linear[b], 1);
  });

  it('sequentToState converts cartesian context to state.persistent', () => {
    const c = AST.atom('c');
    const seq = Seq.fromArrays([], [c], AST.freevar('X'));

    const state = sequentToState(seq);
    assert.strictEqual(state.persistent[c], 1);
  });

  it('stateToContext converts state back to formula array', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const ctx = stateToContext({ linear: { [a]: 2, [b]: 1 } });

    assert.strictEqual(ctx.length, 3);
    assert.strictEqual(ctx.filter(h => h === a).length, 2);
    assert.strictEqual(ctx.filter(h => h === b).length, 1);
  });

  it('stateToContext handles empty state', () => {
    const ctx = stateToContext({ linear: {} });
    assert.strictEqual(ctx.length, 0);
  });
});

// =========================================================================
// 8. Integration
// =========================================================================

describe('Monad integration', () => {
  it('prove succeeds with engineCalc and matching forward rule', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    const monadB = AST.monad(b);

    // Forward rule: a -o {b}
    const compiled = compileRule({
      name: 'a_to_b',
      hash: AST.loli(a, AST.monad(b)),
      antecedent: a,
      consequent: AST.monad(b)
    });

    const seq = Seq.fromArrays([a], [], monadB);
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success, 'should prove a |- {b} with forward rule a→b');
  });

  it('prove fails without engineCalc (no forward engine)', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const monadB = AST.monad(AST.atom('b'));

    const seq = Seq.fromArrays([a], [], monadB);
    const result = focused.prove(seq, {
      rules: specs,
      alternatives
      // no engineCalc
    });

    assert.strictEqual(result.success, false,
      'should fail without forward rules');
  });

  it('proof tree marks monad_r with modeSwitch state', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const monadA = AST.monad(a);
    const compiled = compileRule({
      name: 'test_pass',
      hash: AST.loli(a, AST.monad(a)),
      antecedent: a,
      consequent: AST.monad(a)
    });

    const seq = Seq.fromArrays([a], [], monadA);
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success);
    assert.ok(result.proofTree.state.modeSwitch, 'proofTree state should have modeSwitch');
    assert.ok(result.proofTree.state.quiescent !== undefined, 'should have quiescence info');
  });

  it('monad_r fires eagerly in inversion phase (negative polarity)', () => {
    const focused = createProver(ill);

    // monad is negative → monad_r is invertible → fires in inversion
    const monadA = AST.monad(AST.freevar('A'));
    const a = AST.atom('a');
    const seq = Seq.fromArrays([a], [], monadA);

    const inv = focused.findInvertible(seq);
    assert.ok(inv, 'findInvertible should find monad_r');
    assert.strictEqual(inv.position, 'R');

    const rName = focused.ruleName(inv.formula, 'r');
    assert.strictEqual(rName, 'monad_r');
  });

  it('forward engine quiescence is reported', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    // Rule: a -o {b}
    const compiled = compileRule({
      name: 'a_to_b_q',
      hash: AST.loli(a, AST.monad(b)),
      antecedent: a,
      consequent: AST.monad(b)
    });

    const seq = Seq.fromArrays([a], [], AST.monad(b));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success);
    assert.ok(result.proofTree.state.quiescent, 'forward engine should reach quiescence');
  });
});

// =========================================================================
// 9. rightFocus — succedent decomposition (Phase 3)
// =========================================================================

describe('rightFocus succedent decomposition', () => {
  it('atom: single atom in state matches', () => {
    const a = AST.atom('a');
    const remaining = rightFocus({ [a]: 1 }, {}, a);
    assert.ok(remaining !== null, 'should succeed');
    assert.strictEqual(Object.keys(remaining).length, 0, 'remaining should be empty');
  });

  it('atom: missing resource fails', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const remaining = rightFocus({ [b]: 1 }, {}, a);
    assert.strictEqual(remaining, null, 'should fail — a not in state');
  });

  it('tensor: two atoms split correctly', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const t = AST.tensor(a, b);
    const remaining = rightFocus({ [a]: 1, [b]: 1 }, {}, t);
    assert.ok(remaining !== null, 'should succeed');
    assert.strictEqual(Object.keys(remaining).length, 0, 'remaining should be empty');
  });

  it('tensor: nested tensor decomposes correctly', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const c = AST.atom('c');
    const t = AST.tensor(AST.tensor(a, b), c);
    const remaining = rightFocus({ [a]: 1, [b]: 1, [c]: 1 }, {}, t);
    assert.ok(remaining !== null);
    assert.strictEqual(Object.keys(remaining).length, 0);
  });

  it('tensor: duplicate atoms consumed multiplicatively', () => {
    const a = AST.atom('a');
    const t = AST.tensor(a, a);
    // Need exactly 2 copies
    const r1 = rightFocus({ [a]: 2 }, {}, t);
    assert.ok(r1 !== null, 'should succeed with 2 copies');
    assert.strictEqual(Object.keys(r1).length, 0);

    // Only 1 copy → fail
    const r2 = rightFocus({ [a]: 1 }, {}, t);
    assert.strictEqual(r2, null, 'should fail with only 1 copy');
  });

  it('one: empty state matches', () => {
    const one = AST.one();
    const remaining = rightFocus({}, {}, one);
    assert.ok(remaining !== null, 'should succeed on empty state');
  });

  it('one: non-empty state fails', () => {
    const a = AST.atom('a');
    const one = AST.one();
    const remaining = rightFocus({ [a]: 1 }, {}, one);
    assert.strictEqual(remaining, null, 'should fail — resources remain');
  });

  it('bang: atom in persistent state matches', () => {
    const a = AST.atom('a');
    const bangA = AST.bang(a);
    const remaining = rightFocus({}, { [a]: 1 }, bangA);
    assert.ok(remaining !== null, 'should succeed');
  });

  it('bang: missing from persistent fails', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const bangA = AST.bang(a);
    const remaining = rightFocus({}, { [b]: 1 }, bangA);
    assert.strictEqual(remaining, null, 'should fail — a not in persistent');
  });

  it('bang: does not consume linear resources', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const bangA = AST.bang(a);
    const remaining = rightFocus({ [b]: 1 }, { [a]: 1 }, bangA);
    assert.ok(remaining !== null);
    assert.strictEqual(remaining[b], 1, 'linear b should remain untouched');
  });

  it('tensor + bang: mixed decomposition', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    // a * !b
    const succ = AST.tensor(a, AST.bang(b));
    const remaining = rightFocus({ [a]: 1 }, { [b]: 1 }, succ);
    assert.ok(remaining !== null, 'should succeed');
    assert.strictEqual(Object.keys(remaining).length, 0);
  });

  it('failure: leftover resources after decomposition', () => {
    const a = AST.atom('a');
    const b = AST.atom('b');
    const c = AST.atom('c');
    // Succedent asks for a * b, but state has a, b, c
    const succ = AST.tensor(a, b);
    const remaining = rightFocus({ [a]: 1, [b]: 1, [c]: 1 }, {}, succ);
    // rightFocus itself succeeds (consumed a and b) but c remains
    assert.ok(remaining !== null, 'rightFocus succeeds (partial)');
    assert.strictEqual(remaining[c], 1, 'c should remain unconsumed');
    // executeModeSwitch would reject this (linearEmpty check)
  });

  it('freevar in succedent fails', () => {
    const fv = AST.freevar('X');
    const remaining = rightFocus({}, {}, fv);
    assert.strictEqual(remaining, null, 'freevar cannot be rightFocused');
  });

  it('predicate term consumes from linear', () => {
    // Compound term like pc(5) — treated as ground fact
    const pc5 = Store.put('pc', [Store.put('binlit', [5n])]);
    const remaining = rightFocus({ [pc5]: 1 }, {}, pc5);
    assert.ok(remaining !== null);
    assert.strictEqual(Object.keys(remaining).length, 0);
  });
});

// =========================================================================
// 10. rightFocus integration (Phase 3)
// =========================================================================

describe('rightFocus integration', () => {
  it('succedent match → proof succeeds', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    // Forward rule: a -o {b}
    const compiled = compileRule({
      name: 'rf_a_to_b',
      hash: AST.loli(a, AST.monad(b)),
      antecedent: a,
      consequent: AST.monad(b)
    });

    // Prove: a |- {b}
    const seq = Seq.fromArrays([a], [], AST.monad(b));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success, 'forward produces b, succedent is {b} → match');
  });

  it('succedent mismatch → proof fails (L3 backtracks)', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    const c = AST.atom('c');
    // Forward rule: a -o {b}
    const compiled = compileRule({
      name: 'rf_mismatch',
      hash: AST.loli(a, AST.monad(b)),
      antecedent: a,
      consequent: AST.monad(b)
    });

    // Prove: a |- {c} — forward produces b, but succedent wants c
    const seq = Seq.fromArrays([a], [], AST.monad(c));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.strictEqual(result.success, false,
      'forward produces b but succedent wants c → rightFocus fails');
  });

  it('leftover resources → proof fails', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    // Forward rule: a -o {a * b} (produces MORE than consumed)
    const compiled = compileRule({
      name: 'rf_extra',
      hash: AST.loli(a, AST.monad(AST.tensor(a, b))),
      antecedent: a,
      consequent: AST.monad(AST.tensor(a, b))
    });

    // Prove: a |- {a} — forward produces a and b, but succedent only wants a
    const seq = Seq.fromArrays([a], [], AST.monad(a));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.strictEqual(result.success, false,
      'forward produces {a, b} but succedent is {a} → leftover b → fail');
  });

  it('tensor succedent with multiple forward steps', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    const c = AST.atom('c');
    // Rule 1: a -o {b}
    const r1 = compileRule({
      name: 'rf_chain1',
      hash: AST.loli(a, AST.monad(b)),
      antecedent: a,
      consequent: AST.monad(b)
    });
    // Rule 2: b -o {c}
    const r2 = compileRule({
      name: 'rf_chain2',
      hash: AST.loli(b, AST.monad(c)),
      antecedent: b,
      consequent: AST.monad(c)
    });

    // Prove: a |- {c} — forward chains a→b→c
    const seq = Seq.fromArrays([a], [], AST.monad(c));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [r1, r2] }
    });

    assert.ok(result.success, 'forward chains a→b→c, succedent {c} matches');
  });

  it('tensor succedent decomposes against multi-fact state', () => {
    const focused = createProver(ill);
    const { specs, alternatives } = initRuleSpecs(ill);

    const a = AST.atom('a');
    const b = AST.atom('b');
    const c = AST.atom('c');
    // Rule: a -o {b * c} (one step producing two facts)
    const compiled = compileRule({
      name: 'rf_tensor_out',
      hash: AST.loli(a, AST.monad(AST.tensor(b, c))),
      antecedent: a,
      consequent: AST.monad(AST.tensor(b, c))
    });

    // Prove: a |- {b * c}
    const seq = Seq.fromArrays([a], [], AST.monad(AST.tensor(b, c)));
    const result = focused.prove(seq, {
      rules: specs,
      alternatives,
      engineCalc: { forwardRules: [compiled] }
    });

    assert.ok(result.success, 'forward produces {b, c}, rightFocus decomposes b * c');
  });
});
