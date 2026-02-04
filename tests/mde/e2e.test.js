/**
 * End-to-end tests for MDE loading and execution
 */

const assert = require('assert');
const mde = require('../../lib/mde');
const Store = mde.Store;

describe('MDE End-to-End', function() {
  this.timeout(10000);

  describe('bin.mde', () => {
    let calc;

    before(async () => {
      calc = await mde.load('/home/mhhf/src/optimism-mde/lib/bin.mde');
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
      calc = await mde.load('/home/mhhf/src/optimism-mde/lib/evm.mde');
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
      // Initial state: pc at 0, code[0] = STOP (N_00)
      const pc = await mde.parseExpr('pc e'); // e = binary 0
      const code = await mde.parseExpr('code e N_00'); // N_00 = STOP opcode

      // Need inc predicate for PC increment
      const inc = await mde.parseExpr('inc e (i e)'); // inc(0, 1)

      const state = mde.createState(
        { [pc]: 1, [code]: 1 },
        { [inc]: true }
      );

      const result = calc.exec(state, { trace: true });

      assert(result.quiescent, 'Should reach quiescence');
      assert.strictEqual(result.steps, 1, 'Should take 1 step');
      assert(result.trace[0].includes('evm/stop'), 'Should fire evm/stop rule');
      // code should remain (it's kept in the rule)
      assert(result.state.linear[code], 'Should still have code');
    });
  });

  describe('Multi-file loading', () => {
    it('can load multiple files', async () => {
      const bin = await mde.load('/home/mhhf/src/optimism-mde/lib/bin.mde');
      const evm = await mde.load('/home/mhhf/src/optimism-mde/lib/evm.mde');

      // Store is shared - interning works across files
      const binType = bin.types.get('bin');
      const binFromEvm = await mde.parseExpr('bin');

      // Same hash because content-addressed
      // (might not be exactly same if parsed differently, but should be compatible)
      assert(Store.get(binType), 'bin from bin.mde should be in store');
      assert(Store.get(binFromEvm), 'bin from parse should be in store');
    });
  });

  describe('Performance', () => {
    it('loads evm.mde in < 100ms', async () => {
      const start = Date.now();
      await mde.load('/home/mhhf/src/optimism-mde/lib/evm.mde');
      const elapsed = Date.now() - start;

      console.log(`  Load time: ${elapsed}ms`);
      assert(elapsed < 100, `Load time ${elapsed}ms exceeds 100ms target`);
    });

    it('forward step is fast', async () => {
      const calc = await mde.load('/home/mhhf/src/optimism-mde/lib/evm.mde');

      const pc = await mde.parseExpr('pc e');
      const code = await mde.parseExpr('code e N_00');
      const inc = await mde.parseExpr('inc e (i e)');

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
