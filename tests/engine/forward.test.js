/**
 * Tests for Forward Chaining Engine
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');
const forward = require('../../lib/prover/strategy/forward');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');

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

  describe('EVM multi-step execution', { timeout: 30000 }, () => {
    it('executes 5+ steps from JUMPDEST at PC=0x75', async () => {
      const programsDir = path.join(__dirname, '../../calculus/ill/programs');
      const calc = await mde.load([
        path.join(programsDir, 'bin.ill'),
        path.join(programsDir, 'evm.ill'),
        path.join(programsDir, 'multisig_code.ill'),
      ]);

      // Build initial state
      const state = { linear: {}, persistent: {} };
      const basicFacts = [
        'pc N_75',
        'sh ee',
        'gas N_ffff',
        'caller sender_addr',
        'sender member01',
      ];
      for (const f of basicFacts) {
        const h = await mde.parseExpr(f);
        state.linear[h] = 1;
      }

      // Load code facts from multisig_code.mde
      const codeFile = fs.readFileSync(path.join(programsDir, 'multisig_code.ill'), 'utf8');
      for (const line of codeFile.split('\n')) {
        const trimmed = line.split('%')[0].trim();
        if (!trimmed || !trimmed.startsWith('code')) continue;
        const parts = trimmed.replace(/\*.*$/, '').trim();
        if (parts) {
          const h = await mde.parseExpr(parts);
          state.linear[h] = 1;
        }
      }

      const result = calc.exec(state, { maxSteps: 10, trace: true });

      assert(result.steps >= 5, `Expected >= 5 steps, got ${result.steps}. Trace: ${result.trace?.join(' → ')}`);
    });
  });
});
