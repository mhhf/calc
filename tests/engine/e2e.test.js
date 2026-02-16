/**
 * End-to-end tests for MDE loading and execution
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const Store = mde.Store;

describe('MDE End-to-End', { timeout: 10000 }, () => {
  describe('bin.mde', () => {
    let calc;

    before(async () => {
      calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/bin.ill'));
    });

    it('loads types', () => {
      assert(calc.types.has('bin'), 'Should have bin type');
      assert(calc.types.has('nat'), 'Should have nat type');
    });

    it('loads clauses', () => {
      // plus/z1 has no premises, so it's a type/axiom
      // plus/s1 has premises, so it's a clause
      assert(calc.clauses.has('plus/s1'), 'Should have plus/s1');
      assert(calc.types.has('plus/z1'), 'plus/z1 is an axiom (no premises)');
    });

    it('has no forward rules', () => {
      assert.strictEqual(calc.forwardRules.length, 0, 'bin.mde has no forward rules');
    });
  });

  describe('evm.mde', () => {
    let calc;

    before(async () => {
      calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
    });

    it('loads types', () => {
      assert(calc.types.has('pc'), 'Should have pc type');
      assert(calc.types.has('stack'), 'Should have stack type');
      assert(calc.types.has('code'), 'Should have code type');
    });

    it('loads forward rules', () => {
      assert(calc.forwardRules.length > 0, 'Should have forward rules');

      // Check specific rules
      const ruleNames = calc.forwardRules.map(r => r.name);
      assert(ruleNames.includes('evm/stop'), 'Should have evm/stop rule');
      assert(ruleNames.includes('evm/add'), 'Should have evm/add rule');
    });

    it('executes STOP instruction', async () => {
      // Initial state: pc at 0, code[0] = STOP (0x00)
      const pc = await mde.parseExpr('pc 0');
      const code = await mde.parseExpr('code 0 0x00');
      const inc = await mde.parseExpr('inc 0 1');

      const state = mde.createState(
        { [pc]: 1, [code]: 1 },
        { [inc]: true }
      );

      const result = calc.exec(state, { trace: true });

      assert(result.quiescent, 'Should reach quiescence');
      assert.strictEqual(result.steps, 1, 'Should take 1 step');
      assert(result.trace[0].includes('evm/stop'), 'Should fire evm/stop rule');
      assert(result.state.linear[code], 'Should still have code');
    });
  });

  describe('Multi-file loading', () => {
    it('can load multiple files', async () => {
      const bin = await mde.load(path.join(__dirname, '../../calculus/ill/programs/bin.ill'));
      const evm = await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      // Store is shared - interning works across files
      const binType = bin.types.get('bin');
      const binFromEvm = await mde.parseExpr('bin');

      assert(Store.get(binType), 'bin from bin.mde should be in store');
      assert(Store.get(binFromEvm), 'bin from parse should be in store');
    });
  });

  describe('Performance', () => {
    it('loads evm.mde in < 100ms', async () => {
      const start = Date.now();
      await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const elapsed = Date.now() - start;

      console.log(`  Load time: ${elapsed}ms`);
      assert(elapsed < 100, `Load time ${elapsed}ms exceeds 100ms target`);
    });

    it('forward step is fast', async () => {
      const calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      const pc = await mde.parseExpr('pc 0');
      const code = await mde.parseExpr('code 0 0x00');
      const inc = await mde.parseExpr('inc 0 1');

      const state = mde.createState(
        { [pc]: 1, [code]: 1 },
        { [inc]: true }
      );

      const start = Date.now();
      for (let i = 0; i < 100; i++) {
        calc.exec(state);
      }
      const elapsed = Date.now() - start;

      console.log(`  100 executions: ${elapsed}ms (${elapsed/100}ms per exec)`);
      assert(elapsed < 500, `100 executions took ${elapsed}ms, too slow`);
    });
  });
});
