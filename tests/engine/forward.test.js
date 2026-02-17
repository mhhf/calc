/**
 * Tests for Forward Chaining Engine
 */
const { describe, it } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const forward = require('../../lib/engine/forward');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const ffi = require('../../lib/engine/ffi');

describe('Forward Chaining', { timeout: 10000 }, () => {
  describe('flattenTensor', () => {
    it('flattens simple tensor', async () => {
      const h = await mde.parseExpr('A * B * C');
      const { linear, persistent } = forward.flattenTensor(h);

      assert.strictEqual(linear.length, 3, 'Should have 3 linear');
      assert.strictEqual(persistent.length, 0, 'Should have no persistent');
    });

    it('extracts bang as persistent', async () => {
      const h = await mde.parseExpr('A * !B * C');
      const { linear, persistent } = forward.flattenTensor(h);

      assert.strictEqual(linear.length, 2, 'Should have 2 linear');
      assert.strictEqual(persistent.length, 1, 'Should have 1 persistent');
    });
  });

  describe('compileRule', () => {
    it('compiles forward rule', async () => {
      const h = await mde.parseExpr('A * !B -o { C * D }');
      const rule = {
        name: 'test',
        hash: h,
        antecedent: Store.children(h)[0],
        consequent: Store.children(h)[1]
      };

      const compiled = forward.compileRule(rule);

      assert.strictEqual(compiled.antecedent.linear.length, 1, 'Should have 1 linear ante');
      assert.strictEqual(compiled.antecedent.persistent.length, 1, 'Should have 1 persistent ante');
      assert.strictEqual(compiled.consequent.linear.length, 2, 'Should have 2 linear conseq');
    });
  });

  describe('run', () => {
    it('runs single step rule', async () => {
      // Rule: foo -o { bar } (lowercase = atoms, not metavars)
      const ruleH = await mde.parseExpr('foo -o { bar }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'foo_to_bar',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      // State: foo
      const foo = await mde.parseExpr('foo');
      const bar = await mde.parseExpr('bar');
      const state = forward.createState({ [foo]: 1 }, {});

      const result = forward.run(state, [rule]);

      assert(result.quiescent, 'Should reach quiescence');
      assert.strictEqual(result.steps, 1, 'Should take 1 step');
      assert.strictEqual(result.state.linear[bar], 1, 'Should have bar');
      assert(!result.state.linear[foo], 'Should not have foo');
    });

    it('stops when no rules match', async () => {
      // Rule: foo -o { bar }
      const ruleH = await mde.parseExpr('foo -o { bar }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'foo_to_bar',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      // State: baz (not foo)
      const baz = await mde.parseExpr('baz');
      const state = forward.createState({ [baz]: 1 }, {});

      const result = forward.run(state, [rule]);

      assert(result.quiescent, 'Should reach quiescence');
      assert.strictEqual(result.steps, 0, 'Should take 0 steps');
      assert.strictEqual(result.state.linear[baz], 1, 'Should still have baz');
    });

    it('uses persistent facts without consuming', async () => {
      // Rule: foo * !guard -o { bar }
      const ruleH = await mde.parseExpr('foo * !guard -o { bar }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'test',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      const foo = await mde.parseExpr('foo');
      const guard = await mde.parseExpr('guard');
      const bar = await mde.parseExpr('bar');

      // State: foo, foo, !guard
      const state = forward.createState(
        { [foo]: 2 },
        { [guard]: true }
      );

      const result = forward.run(state, [rule]);

      assert(result.quiescent, 'Should reach quiescence');
      assert.strictEqual(result.steps, 2, 'Should take 2 steps (both foos)');
      assert.strictEqual(result.state.linear[bar], 2, 'Should have 2 bars');
      assert(result.state.persistent[guard], 'Should still have persistent guard');
    });

    it('limits steps with maxSteps', async () => {
      // Infinite loop rule: foo -o { foo * bar }
      const ruleH = await mde.parseExpr('foo -o { foo * bar }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'infinite',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      const foo = await mde.parseExpr('foo');
      const state = forward.createState({ [foo]: 1 }, {});

      const result = forward.run(state, [rule], { maxSteps: 5 });

      assert(!result.quiescent, 'Should not reach quiescence');
      assert.strictEqual(result.steps, 5, 'Should stop at 5 steps');
    });

    it('provides trace when requested', async () => {
      const ruleH = await mde.parseExpr('foo -o { bar }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'foo_to_bar',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      const foo = await mde.parseExpr('foo');
      const state = forward.createState({ [foo]: 1 }, {});

      const result = forward.run(state, [rule], { trace: true });

      assert(result.trace, 'Should have trace');
      assert.strictEqual(result.trace.length, 1, 'Should have 1 trace entry');
      assert(result.trace[0].includes('foo_to_bar'), 'Trace should include rule name');
    });
  });

  describe('tryFFIDirect definitive failure bug', () => {
    // Bug: forward.js:227 — when tryFFIDirect returns {success: false, reason: 'conversion_failed'}
    // for a non-multiModal predicate, tryMatch treats it as definitive failure (line 436: break).
    // This skips persistent state lookup and backward proving entirely.
    //
    // The issue: isGround() checks only for metavars, not "is numeric."
    // A ground atom like (atom 'sym') passes isGround but fails binToInt → conversion_failed.
    // For non-multiModal predicates (inc, to256, etc.), this non-definitive failure
    // is treated as definitive, blocking all fallback paths.

    it('isGround returns true for non-numeric ground terms', () => {
      // A symbolic expression term — ground (no metavars) but not a binlit
      const sym = Store.put('atom', ['sym']);
      assert.strictEqual(ffi.convert.isGround(sym), true,
        'atom is ground (no metavars)');

      const symExpr = Store.put('plus_expr', [
        Store.put('binlit', [3n]),
        Store.put('binlit', [5n])
      ]);
      assert.strictEqual(ffi.convert.isGround(symExpr), true,
        'plus_expr with binlit children is ground');
      assert.strictEqual(ffi.convert.binToInt(symExpr), null,
        'binToInt returns null for non-binlit tag');
    });

    it('non-multiModal FFI returns conversion_failed for ground non-numeric input', () => {
      // inc has mode '+ -' and is NOT multiModal
      const sym = Store.put('atom', ['sym']);
      const result = ffi.arithmetic.inc([sym, 0]);
      assert.strictEqual(result.success, false);
      assert.strictEqual(result.reason, 'conversion_failed',
        'inc returns conversion_failed, not mode_mismatch');
    });

    it('conversion_failed prevents persistent state fallback', async () => {
      // This test demonstrates the bug end-to-end:
      // A rule with !inc where the input is ground but non-numeric.
      // The FFI returns conversion_failed, tryMatch treats it as definitive → rule fails.
      // But if persistent state lookup were tried, it could find a match.

      // Rule: foo _X * !inc _X _Y -o { bar _Y }
      const ruleH = await mde.parseExpr('foo _X * !inc _X _Y -o { bar _Y }');
      const [ante, conseq] = Store.children(ruleH);
      const rule = forward.compileRule({
        name: 'test_inc',
        hash: ruleH,
        antecedent: ante,
        consequent: conseq
      });

      // Create a ground but non-numeric term as the value of foo
      const sym = Store.put('atom', ['sym']);
      const fooSym = Store.put('foo', [sym]);

      // Pre-compute what inc(sym) should be — put it in persistent state
      const incResult = Store.put('atom', ['sym_plus_1']);
      const incFact = Store.put('inc', [sym, incResult]);

      const state = forward.createState(
        { [fooSym]: 1 },
        { [incFact]: true }
      );

      // tryMatch should find inc(sym, sym_plus_1) in persistent state,
      // but the bug causes tryFFIDirect to return {success: false, reason: 'conversion_failed'}
      // which is treated as definitive failure (break on line 436).
      // The persistent state lookup (lines 439-460) is never reached.
      const result = forward.tryMatch(rule, state, null);

      // BUG: result is null because conversion_failed is treated as definitive.
      // EXPECTED: result should succeed, binding Y to sym_plus_1.
      // When the bug is fixed, change this assertion to: assert.notStrictEqual(result, null)
      assert.strictEqual(result, null,
        'BUG: tryMatch fails because conversion_failed is treated as definitive — ' +
        'persistent state lookup is skipped');
    });
  });

  describe('EVM multi-step execution', { timeout: 30000 }, () => {
    it('executes 5+ steps from multisig query', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig.ill')
      );

      const state = mde.decomposeQuery(calc.queries.get('symex'));

      const result = calc.exec(state, { maxSteps: 10, trace: true });

      assert(result.steps >= 5, `Expected >= 5 steps, got ${result.steps}. Trace: ${result.trace?.join(' → ')}`);
    });
  });
});
