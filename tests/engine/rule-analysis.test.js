/**
 * Tests for Rule Analysis — Stage 2: Preserved/Delta Detection
 *
 * Phase 1: Inspect real EVM rules and synthetic rules to understand
 * the flattened structure before building the analysis function.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const forward = require('../../lib/prover/strategy/forward');
const { analyzeRule, analyzeDeltas } = require('../../lib/prover/strategy/rule-analysis');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');

// Helper: parse a lollipop rule string and compile it
async function makeRule(name, expr) {
  const h = await mde.parseExpr(expr);
  const [ante, conseq] = Store.children(h);
  return forward.compileRule({ name, hash: h, antecedent: ante, consequent: conseq });
}

// Helper: dump a compiled rule's structure for inspection
function dumpRule(rule) {
  const anteLinear = (rule.antecedent.linear || []).map(h => ({
    pred: forward.getPredicateHead(h),
    tag: Store.tag(h),
    arity: Store.arity(h),
    hash: h,
    children: Store.children(h)
  }));
  const antePersistent = (rule.antecedent.persistent || []).map(h => ({
    pred: forward.getPredicateHead(h),
    tag: Store.tag(h),
    arity: Store.arity(h),
    hash: h,
    children: Store.children(h)
  }));
  const conseqLinear = (rule.consequent.linear || []).map(h => ({
    pred: forward.getPredicateHead(h),
    tag: Store.tag(h),
    arity: Store.arity(h),
    hash: h,
    children: Store.children(h)
  }));
  return { anteLinear, antePersistent, conseqLinear };
}

// ============================================================================
// PART 1: Inspect real EVM rule structure
// ============================================================================

describe('Rule Analysis', { timeout: 10000 }, () => {
  describe('EVM rule structure inspection', () => {
    let calc;

    before(async () => {
      calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
    });

    it('evm/stop has expected antecedent and consequent predicates', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/stop');
      assert(rule, 'evm/stop rule should exist');

      const dump = dumpRule(rule);

      // Antecedent linear should have: pc, code, gas (at minimum)
      const antePreds = dump.anteLinear.map(p => p.pred);
      assert(antePreds.includes('pc'), `ante should have pc, got: ${antePreds}`);
      assert(antePreds.includes('code'), `ante should have code, got: ${antePreds}`);

      // Consequent linear should have: done (or similar terminal)
      assert(dump.conseqLinear.length > 0, 'Should have consequent patterns');
    });

    it('evm/add has preserved, delta, and consumed predicates', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      assert(rule, 'evm/add rule should exist');

      const dump = dumpRule(rule);
      const antePreds = dump.anteLinear.map(p => p.pred);
      const conseqPreds = dump.conseqLinear.map(p => p.pred);

      // code should appear on both sides (preserved)
      assert(antePreds.includes('code'), 'ante should have code');
      assert(conseqPreds.includes('code'), 'conseq should have code');

      // pc should appear on both sides (delta — arg changes via !inc)
      assert(antePreds.includes('pc'), 'ante should have pc');
      assert(conseqPreds.includes('pc'), 'conseq should have pc');

      // sh should appear on both sides (preserved — same args)
      assert(antePreds.includes('sh'), 'ante should have sh');
      assert(conseqPreds.includes('sh'), 'conseq should have sh');

      // stack should appear on both sides (delta — args change)
      assert(antePreds.includes('stack'), 'ante should have stack');
      assert(conseqPreds.includes('stack'), 'conseq should have stack');

      // persistent antecedents should include inc and plus
      const persistPreds = dump.antePersistent.map(p => p.pred);
      assert(persistPreds.includes('inc'), `persistent should have inc, got: ${persistPreds}`);
      assert(persistPreds.includes('plus'), `persistent should have plus, got: ${persistPreds}`);
    });

    it('preserved predicates have identical hashes on both sides', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const dump = dumpRule(rule);

      // code appears on both sides — if preserved, hashes should be identical
      const anteCode = dump.anteLinear.find(p => p.pred === 'code');
      const conseqCode = dump.conseqLinear.find(p => p.pred === 'code');

      assert(anteCode, 'ante should have code');
      assert(conseqCode, 'conseq should have code');

      // Same hash means identical pattern (content-addressed)
      assert.strictEqual(anteCode.hash, conseqCode.hash,
        'preserved predicate code should have same hash on both sides');
    });

    it('delta predicates have different hashes but same predicate head', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const dump = dumpRule(rule);

      // pc appears on both sides — delta (arg changes)
      const antePc = dump.anteLinear.find(p => p.pred === 'pc');
      const conseqPc = dump.conseqLinear.find(p => p.pred === 'pc');

      assert(antePc, 'ante should have pc');
      assert(conseqPc, 'conseq should have pc');

      // Same predicate head, different hash (arg differs)
      assert.notStrictEqual(antePc.hash, conseqPc.hash,
        'delta predicate pc should have different hashes on both sides');
      assert.strictEqual(antePc.pred, conseqPc.pred,
        'delta predicate should have same pred head');
    });

    it('22 of 44 EVM rules have multi-match predicates', () => {
      // Multi-match is the NORM, not an edge case.
      // stack: pop N values → push result (add, sub, mul, swap, dup, log4, call...)
      // code: push1/push20 read opcode + operand (2 code facts)
      let multiCount = 0;
      for (const rule of calc.forwardRules) {
        const dump = dumpRule(rule);
        const antePreds = dump.anteLinear.map(p => p.pred);
        const conseqPreds = dump.conseqLinear.map(p => p.pred);
        const anteDups = antePreds.filter((p, i) => antePreds.indexOf(p) !== i);
        const conseqDups = conseqPreds.filter((p, i) => conseqPreds.indexOf(p) !== i);
        if (anteDups.length > 0 || conseqDups.length > 0) multiCount++;
      }
      assert(multiCount >= 20, `expected >=20 multi-match rules, got ${multiCount}`);
    });

    it('evm/swap1 has 2 stacks on both sides (true N:M multi-match)', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/swap1');
      assert(rule, 'evm/swap1 should exist');

      const dump = dumpRule(rule);
      const anteStacks = dump.anteLinear.filter(p => p.pred === 'stack');
      const conseqStacks = dump.conseqLinear.filter(p => p.pred === 'stack');

      assert.strictEqual(anteStacks.length, 2, '2 stacks consumed');
      assert.strictEqual(conseqStacks.length, 2, '2 stacks produced');

      // The stacks should have different hashes (different metavar args)
      assert.notStrictEqual(anteStacks[0].hash, anteStacks[1].hash,
        'ante stacks should differ (different stack heights/values)');
    });

    it('evm/dup1 has 1 stack in, 2 stacks out (split-like)', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/dup1');
      assert(rule, 'evm/dup1 should exist');

      const dump = dumpRule(rule);
      const anteStacks = dump.anteLinear.filter(p => p.pred === 'stack');
      const conseqStacks = dump.conseqLinear.filter(p => p.pred === 'stack');

      assert.strictEqual(anteStacks.length, 1, '1 stack consumed');
      assert.strictEqual(conseqStacks.length, 2, '2 stacks produced');
    });

    it('delta predicates share a metavar with persistent antecedents', () => {
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const dump = dumpRule(rule);

      // pc ante pattern: pc(_PC) — child 0 is a metavar
      const antePc = dump.anteLinear.find(p => p.pred === 'pc');
      const conseqPc = dump.conseqLinear.find(p => p.pred === 'pc');

      // The antecedent pc's arg and consequent pc's arg should be different metavars
      const anteArg = Store.child(antePc.hash, 0);
      const conseqArg = Store.child(conseqPc.hash, 0);
      assert.notStrictEqual(anteArg, conseqArg, 'pc args should be different metavars');

      // Both should be freevars (metavars)
      assert.strictEqual(Store.tag(anteArg), 'freevar', 'ante pc arg should be freevar');
      assert.strictEqual(Store.tag(conseqArg), 'freevar', 'conseq pc arg should be freevar');

      // There should be a persistent inc(_PC, _PC') linking them
      const incPat = dump.antePersistent.find(p => p.pred === 'inc');
      assert(incPat, 'should have persistent inc');

      // inc's children should be [anteArg, conseqArg]
      const incArg0 = Store.child(incPat.hash, 0);
      const incArg1 = Store.child(incPat.hash, 1);
      assert.strictEqual(incArg0, anteArg,
        'inc first arg should be ante pc arg (shared metavar)');
      assert.strictEqual(incArg1, conseqArg,
        'inc second arg should be conseq pc arg (shared metavar)');
    });
  });

  // ============================================================================
  // PART 2: Synthetic rules — single-match cases
  // ============================================================================

  describe('Single-match classification', () => {
    it('pure consumed/produced: foo -o bar', async () => {
      const rule = await makeRule('consume', 'foo -o { bar }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 1);
      assert.strictEqual(dump.conseqLinear.length, 1);
      assert.strictEqual(dump.anteLinear[0].pred, 'foo');
      assert.strictEqual(dump.conseqLinear[0].pred, 'bar');

      // Different predicates — no preserved, no delta
      assert.notStrictEqual(dump.anteLinear[0].pred, dump.conseqLinear[0].pred);
    });

    it('preserved: foo * bar -o foo * baz', async () => {
      const rule = await makeRule('preserve', 'foo * bar -o { foo * baz }');
      const dump = dumpRule(rule);

      const anteFoo = dump.anteLinear.find(p => p.pred === 'foo');
      const conseqFoo = dump.conseqLinear.find(p => p.pred === 'foo');

      // foo appears on both sides with identical hash (no args, atom)
      assert(anteFoo, 'ante should have foo');
      assert(conseqFoo, 'conseq should have foo');
      assert.strictEqual(anteFoo.hash, conseqFoo.hash,
        'preserved atom should have same hash on both sides');
    });

    it('preserved with args: p _X * bar -o p _X * baz', async () => {
      const rule = await makeRule('preserve_args', 'p _X * bar -o { p _X * baz }');
      const dump = dumpRule(rule);

      const anteP = dump.anteLinear.find(p => p.pred === 'p');
      const conseqP = dump.conseqLinear.find(p => p.pred === 'p');

      assert(anteP, 'ante should have p');
      assert(conseqP, 'conseq should have p');
      // Same metavar _X on both sides → same hash (content-addressed)
      assert.strictEqual(anteP.hash, conseqP.hash,
        'p(_X) should have same hash on both sides');
    });

    it('delta: p _X * !inc _X _Y -o p _Y', async () => {
      const rule = await makeRule('delta', 'p _X * !inc _X _Y -o { p _Y }');
      const dump = dumpRule(rule);

      const anteP = dump.anteLinear.find(p => p.pred === 'p');
      const conseqP = dump.conseqLinear.find(p => p.pred === 'p');

      assert(anteP, 'ante should have p');
      assert(conseqP, 'conseq should have p');
      // Same pred, different args → delta
      assert.strictEqual(anteP.pred, conseqP.pred);
      assert.notStrictEqual(anteP.hash, conseqP.hash,
        'delta predicate should have different hashes');

      // Persistent inc links the metavars
      assert.strictEqual(dump.antePersistent.length, 1);
      assert.strictEqual(dump.antePersistent[0].pred, 'inc');
    });

    it('mixed: preserved + delta + consumed + produced', async () => {
      const rule = await makeRule('mixed',
        'keep * p _X * gone * !inc _X _Y -o { keep * p _Y * born }');
      const dump = dumpRule(rule);

      const antePreds = dump.anteLinear.map(p => p.pred);
      const conseqPreds = dump.conseqLinear.map(p => p.pred);

      // keep: preserved (same hash both sides)
      const anteKeep = dump.anteLinear.find(p => p.pred === 'keep');
      const conseqKeep = dump.conseqLinear.find(p => p.pred === 'keep');
      assert.strictEqual(anteKeep.hash, conseqKeep.hash, 'keep is preserved');

      // p: delta (different hash, same pred)
      const anteP = dump.anteLinear.find(p => p.pred === 'p');
      const conseqP = dump.conseqLinear.find(p => p.pred === 'p');
      assert.notStrictEqual(anteP.hash, conseqP.hash, 'p is delta');

      // gone: consumed only (no match in conseq)
      assert(antePreds.includes('gone'), 'ante has gone');
      assert(!conseqPreds.includes('gone'), 'conseq does not have gone');

      // born: produced only (no match in ante)
      assert(!antePreds.includes('born'), 'ante does not have born');
      assert(conseqPreds.includes('born'), 'conseq has born');
    });
  });

  // ============================================================================
  // PART 3: Multi-match edge cases
  // ============================================================================

  describe('Multi-match: same predicate multiple times', () => {
    it('join: coin * coin -o coin (2 ante, 1 conseq)', async () => {
      const rule = await makeRule('join', 'coin * coin -o { coin }');
      const dump = dumpRule(rule);

      // 2 identical atoms on left, 1 on right
      assert.strictEqual(dump.anteLinear.length, 2, 'should have 2 ante linear');
      assert.strictEqual(dump.conseqLinear.length, 1, 'should have 1 conseq linear');

      // All coin hashes are the same (content-addressed, same atom)
      assert.strictEqual(dump.anteLinear[0].hash, dump.anteLinear[1].hash,
        'both ante coins are identical hashes');
      assert.strictEqual(dump.anteLinear[0].hash, dump.conseqLinear[0].hash,
        'ante and conseq coins are identical hashes');
    });

    it('split: coin -o coin * coin (1 ante, 2 conseq)', async () => {
      const rule = await makeRule('split', 'coin -o { coin * coin }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 1, 'should have 1 ante linear');
      assert.strictEqual(dump.conseqLinear.length, 2, 'should have 2 conseq linear');

      // All same hash
      assert.strictEqual(dump.anteLinear[0].hash, dump.conseqLinear[0].hash);
      assert.strictEqual(dump.conseqLinear[0].hash, dump.conseqLinear[1].hash);
    });

    it('triple join: coin * coin * coin -o coin (3 ante, 1 conseq)', async () => {
      const rule = await makeRule('triple_join', 'coin * coin * coin -o { coin }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 3);
      assert.strictEqual(dump.conseqLinear.length, 1);
    });

    it('many-to-many: coin * coin * coin -o coin * coin (3 ante, 2 conseq)', async () => {
      const rule = await makeRule('many_to_many', 'coin * coin * coin -o { coin * coin }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 3);
      assert.strictEqual(dump.conseqLinear.length, 2);
    });

    it('join with args: p _X * p _Y -o p _Z (different metavars)', async () => {
      const rule = await makeRule('join_args', 'p _X * p _Y * !merge _X _Y _Z -o { p _Z }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 2);
      assert.strictEqual(dump.conseqLinear.length, 1);

      // Both are p but with different metavar args → different hashes
      assert.strictEqual(dump.anteLinear[0].pred, 'p');
      assert.strictEqual(dump.anteLinear[1].pred, 'p');
      assert.strictEqual(dump.conseqLinear[0].pred, 'p');
      assert.notStrictEqual(dump.anteLinear[0].hash, dump.anteLinear[1].hash,
        'p(_X) and p(_Y) have different hashes');
    });

    it('split with args: p _X * !split _X _Y _Z -o p _Y * p _Z', async () => {
      const rule = await makeRule('split_args',
        'p _X * !split _X _Y _Z -o { p _Y * p _Z }');
      const dump = dumpRule(rule);

      assert.strictEqual(dump.anteLinear.length, 1);
      assert.strictEqual(dump.conseqLinear.length, 2);
      assert.notStrictEqual(dump.conseqLinear[0].hash, dump.conseqLinear[1].hash,
        'p(_Y) and p(_Z) have different hashes');
    });

    it('swap: a * b -o b * a (preserved, different predicates)', async () => {
      const rule = await makeRule('swap', 'a * b -o { b * a }');
      const dump = dumpRule(rule);

      // Both predicates appear on both sides
      const anteA = dump.anteLinear.find(p => p.pred === 'a');
      const conseqA = dump.conseqLinear.find(p => p.pred === 'a');
      const anteB = dump.anteLinear.find(p => p.pred === 'b');
      const conseqB = dump.conseqLinear.find(p => p.pred === 'b');

      assert(anteA && conseqA, 'a on both sides');
      assert(anteB && conseqB, 'b on both sides');
      assert.strictEqual(anteA.hash, conseqA.hash, 'a is preserved');
      assert.strictEqual(anteB.hash, conseqB.hash, 'b is preserved');
    });
  });

  // ============================================================================
  // PART 4: Nested predicate patterns
  // ============================================================================

  describe('Nested predicate patterns', () => {
    it('preserved with nested args: f (g _X) * bar -o f (g _X) * baz', async () => {
      const rule = await makeRule('nested_preserved',
        'f (g _X) * bar -o { f (g _X) * baz }');
      const dump = dumpRule(rule);

      const anteF = dump.anteLinear.find(p => p.pred === 'f');
      const conseqF = dump.conseqLinear.find(p => p.pred === 'f');

      assert(anteF && conseqF, 'f on both sides');
      assert.strictEqual(anteF.hash, conseqF.hash,
        'f(g(_X)) preserved — same hash due to shared metavar');
    });

    it('delta with nested args: f (g _X) * !inc _X _Y -o f (g _Y)', async () => {
      const rule = await makeRule('nested_delta',
        'f (g _X) * !inc _X _Y -o { f (g _Y) }');
      const dump = dumpRule(rule);

      const anteF = dump.anteLinear.find(p => p.pred === 'f');
      const conseqF = dump.conseqLinear.find(p => p.pred === 'f');

      assert(anteF && conseqF, 'f on both sides');
      assert.notStrictEqual(anteF.hash, conseqF.hash,
        'f(g(_X)) vs f(g(_Y)) — delta, different hashes');
      assert.strictEqual(anteF.pred, conseqF.pred, 'same pred head');
    });

    it('partially preserved nested: f _X (g _Y) * !inc _X _Z -o f _Z (g _Y)', async () => {
      const rule = await makeRule('partial_nested',
        'f _X (g _Y) * !inc _X _Z -o { f _Z (g _Y) }');
      const dump = dumpRule(rule);

      const anteF = dump.anteLinear.find(p => p.pred === 'f');
      const conseqF = dump.conseqLinear.find(p => p.pred === 'f');

      assert(anteF && conseqF, 'f on both sides');
      assert.notStrictEqual(anteF.hash, conseqF.hash, 'different hashes — first arg changes');

      // Second arg (g _Y) should be the same on both sides
      const anteArg1 = Store.child(anteF.hash, 1);
      const conseqArg1 = Store.child(conseqF.hash, 1);
      assert.strictEqual(anteArg1, conseqArg1,
        'second arg (g _Y) should be identical — preserved sub-term');
    });
  });

  // ============================================================================
  // PART 5: Availability / resource counting
  // ============================================================================

  describe('Resource counting correctness', () => {
    it('coin * coin -o coin: requires 2 coins, not 1', async () => {
      const rule = await makeRule('join', 'coin * coin -o { coin }');
      const coin = await mde.parseExpr('coin');

      // With 2 coins: rule should fire, leaving 1
      const state2 = forward.createState({ [coin]: 2 }, {});
      const result2 = forward.run(state2, [rule], { maxSteps: 1 });
      assert.strictEqual(result2.steps, 1, 'should fire with 2 coins');
      assert.strictEqual(result2.state.linear[coin], 1, 'should have 1 coin after join');

      // With 1 coin: rule should NOT fire
      const state1 = forward.createState({ [coin]: 1 }, {});
      const result1 = forward.run(state1, [rule], { maxSteps: 1 });
      assert.strictEqual(result1.steps, 0, 'should NOT fire with only 1 coin');
      assert.strictEqual(result1.state.linear[coin], 1, 'should still have 1 coin');
    });

    it('coin -o coin * coin: produces extra coin', async () => {
      const rule = await makeRule('split', 'coin -o { coin * coin }');
      const coin = await mde.parseExpr('coin');

      const state = forward.createState({ [coin]: 1 }, {});
      const result = forward.run(state, [rule], { maxSteps: 1 });
      assert.strictEqual(result.steps, 1, 'should fire with 1 coin');
      assert.strictEqual(result.state.linear[coin], 2, 'should have 2 coins after split');
    });

    it('coin * coin * coin -o coin * coin: net -1', async () => {
      const rule = await makeRule('join3to2', 'coin * coin * coin -o { coin * coin }');
      const coin = await mde.parseExpr('coin');

      // With 3 coins: should fire, leaving 2
      const state3 = forward.createState({ [coin]: 3 }, {});
      const result3 = forward.run(state3, [rule], { maxSteps: 1 });
      assert.strictEqual(result3.steps, 1, 'should fire with 3 coins');
      assert.strictEqual(result3.state.linear[coin], 2, 'should have 2 coins');

      // With 2 coins: should NOT fire (need 3)
      const state2 = forward.createState({ [coin]: 2 }, {});
      const result2 = forward.run(state2, [rule], { maxSteps: 1 });
      assert.strictEqual(result2.steps, 0, 'should NOT fire with only 2 coins');
    });

    it('a * a -o a * b: one a consumed, one preserved, b produced', async () => {
      const rule = await makeRule('partial', 'a * a -o { a * b }');
      const a = await mde.parseExpr('a');
      const b = await mde.parseExpr('b');

      // With 2 a's: should fire
      const state2 = forward.createState({ [a]: 2 }, {});
      const result2 = forward.run(state2, [rule], { maxSteps: 1 });
      assert.strictEqual(result2.steps, 1, 'should fire with 2 a');
      assert.strictEqual(result2.state.linear[a], 1, 'should have 1 a');
      assert.strictEqual(result2.state.linear[b], 1, 'should have 1 b');

      // With 1 a: should NOT fire (need 2)
      const state1 = forward.createState({ [a]: 1 }, {});
      const result1 = forward.run(state1, [rule], { maxSteps: 1 });
      assert.strictEqual(result1.steps, 0, 'should NOT fire with only 1 a');
    });

    it('a * b * a -o a * b: mixed predicates, a appears 2x on left', async () => {
      const rule = await makeRule('mixed_multi', 'a * b * a -o { a * b }');
      const a = await mde.parseExpr('a');
      const b = await mde.parseExpr('b');

      // Need 2 a and 1 b
      const state = forward.createState({ [a]: 2, [b]: 1 }, {});
      const result = forward.run(state, [rule], { maxSteps: 1 });
      assert.strictEqual(result.steps, 1, 'should fire');
      assert.strictEqual(result.state.linear[a], 1, '1 a remaining');
      assert.strictEqual(result.state.linear[b], 1, '1 b remaining (preserved)');

      // Need 2 a but only have 1
      const state1a = forward.createState({ [a]: 1, [b]: 1 }, {});
      const result1a = forward.run(state1a, [rule], { maxSteps: 1 });
      assert.strictEqual(result1a.steps, 0, 'should NOT fire with only 1 a');
    });

    it('p _X * p _X -o p _X: two identical predicate patterns', async () => {
      const rule = await makeRule('join_same', 'p _X * p _X -o { p _X }');
      const dump = dumpRule(rule);

      // Both ante patterns should be identical (same hash — same metavar)
      assert.strictEqual(dump.anteLinear.length, 2);
      assert.strictEqual(dump.anteLinear[0].hash, dump.anteLinear[1].hash,
        'p(_X) * p(_X) gives identical pattern hashes');
    });
  });

  // ============================================================================
  // PART 6: analyzeRule — preserved/consumed/produced classification
  // ============================================================================

  describe('analyzeRule v1: preserved detection', () => {

    // Helper: compare multisets (sorted arrays)
    function sortedHashes(arr) { return [...arr].sort((a, b) => a - b); }
    function assertMultisetEqual(actual, expected, msg) {
      assert.deepStrictEqual(sortedHashes(actual), sortedHashes(expected), msg);
    }

    it('foo -o bar: pure consumed + produced', async () => {
      const rule = await makeRule('c', 'foo -o { bar }');
      const result = analyzeRule(rule);

      const foo = rule.antecedent.linear[0];
      const bar = rule.consequent.linear[0];

      assertMultisetEqual(result.preserved, [], 'no preserved');
      assertMultisetEqual(result.consumed, [foo], 'foo consumed');
      assertMultisetEqual(result.produced, [bar], 'bar produced');
    });

    it('foo * bar -o foo * baz: foo preserved', async () => {
      const rule = await makeRule('p', 'foo * bar -o { foo * baz }');
      const result = analyzeRule(rule);

      const foo = await mde.parseExpr('foo');
      const bar = await mde.parseExpr('bar');
      const baz = await mde.parseExpr('baz');

      assertMultisetEqual(result.preserved, [foo], 'foo preserved');
      assertMultisetEqual(result.consumed, [bar], 'bar consumed');
      assertMultisetEqual(result.produced, [baz], 'baz produced');
    });

    it('p _X * bar -o p _X * baz: p(_X) preserved (shared metavar)', async () => {
      const rule = await makeRule('pa', 'p _X * bar -o { p _X * baz }');
      const result = analyzeRule(rule);

      // p(_X) has the same hash on both sides (content-addressed, same metavar)
      const pHash = rule.antecedent.linear.find(
        h => forward.getPredicateHead(h) === 'p');

      assert(result.preserved.includes(pHash), 'p(_X) should be preserved');
      assert.strictEqual(result.preserved.length, 1);
      assert.strictEqual(result.consumed.length, 1, '1 consumed (bar)');
      assert.strictEqual(result.produced.length, 1, '1 produced (baz)');
    });

    it('a * b -o b * a: both preserved (swap)', async () => {
      const rule = await makeRule('swap', 'a * b -o { b * a }');
      const result = analyzeRule(rule);

      assert.strictEqual(result.preserved.length, 2, 'both preserved');
      assert.strictEqual(result.consumed.length, 0, 'none consumed');
      assert.strictEqual(result.produced.length, 0, 'none produced');
    });

    it('coin * coin -o coin: 1 preserved, 1 consumed', async () => {
      const rule = await makeRule('join', 'coin * coin -o { coin }');
      const result = analyzeRule(rule);
      const coin = await mde.parseExpr('coin');

      assertMultisetEqual(result.preserved, [coin], '1 preserved');
      assertMultisetEqual(result.consumed, [coin], '1 consumed');
      assertMultisetEqual(result.produced, [], 'none produced');
    });

    it('coin -o coin * coin: 1 preserved, 1 produced', async () => {
      const rule = await makeRule('split', 'coin -o { coin * coin }');
      const result = analyzeRule(rule);
      const coin = await mde.parseExpr('coin');

      assertMultisetEqual(result.preserved, [coin], '1 preserved');
      assertMultisetEqual(result.consumed, [], 'none consumed');
      assertMultisetEqual(result.produced, [coin], '1 produced');
    });

    it('coin * coin * coin -o coin * coin: 2 preserved, 1 consumed', async () => {
      const rule = await makeRule('3to2', 'coin * coin * coin -o { coin * coin }');
      const result = analyzeRule(rule);
      const coin = await mde.parseExpr('coin');

      assertMultisetEqual(result.preserved, [coin, coin], '2 preserved');
      assertMultisetEqual(result.consumed, [coin], '1 consumed');
      assertMultisetEqual(result.produced, [], 'none produced');
    });

    it('a * a -o a * b: 1 a preserved, 1 a consumed, b produced', async () => {
      const rule = await makeRule('partial', 'a * a -o { a * b }');
      const result = analyzeRule(rule);
      const a = await mde.parseExpr('a');
      const b = await mde.parseExpr('b');

      assertMultisetEqual(result.preserved, [a], '1 a preserved');
      assertMultisetEqual(result.consumed, [a], '1 a consumed');
      assertMultisetEqual(result.produced, [b], 'b produced');
    });

    it('p _X * p _Y -o p _Z: no preserved (different hashes)', async () => {
      const rule = await makeRule('join_args',
        'p _X * p _Y * !merge _X _Y _Z -o { p _Z }');
      const result = analyzeRule(rule);

      // All p(...) have different metavar args → different hashes → no preserved
      assert.strictEqual(result.preserved.length, 0, 'no preserved');
      assert.strictEqual(result.consumed.length, 2, '2 consumed');
      assert.strictEqual(result.produced.length, 1, '1 produced');
    });

    it('p _X * p _X -o p _X: 1 preserved, 1 consumed (identical patterns)', async () => {
      const rule = await makeRule('join_same', 'p _X * p _X -o { p _X }');
      const result = analyzeRule(rule);
      const pHash = rule.antecedent.linear[0]; // both are same hash

      assertMultisetEqual(result.preserved, [pHash], '1 preserved');
      assertMultisetEqual(result.consumed, [pHash], '1 consumed');
      assertMultisetEqual(result.produced, [], 'none produced');
    });

    it('multiset invariant: preserved + consumed = antecedent', async () => {
      const rule = await makeRule('inv', 'a * b * a * c -o { a * d * b }');
      const result = analyzeRule(rule);

      const anteHashes = sortedHashes(rule.antecedent.linear);
      const reconstituted = sortedHashes([...result.preserved, ...result.consumed]);
      assert.deepStrictEqual(reconstituted, anteHashes,
        'preserved + consumed should equal antecedent (as multiset)');
    });

    it('multiset invariant: preserved + produced = consequent', async () => {
      const rule = await makeRule('inv2', 'a * b * a * c -o { a * d * b }');
      const result = analyzeRule(rule);

      const conseqHashes = sortedHashes(rule.consequent.linear);
      const reconstituted = sortedHashes([...result.preserved, ...result.produced]);
      assert.deepStrictEqual(reconstituted, conseqHashes,
        'preserved + produced should equal consequent (as multiset)');
    });

    it('evm/add: only code is preserved (v1, no delta detection)', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const result = analyzeRule(rule);

      // code has identical hash on both sides → preserved
      const codeHash = rule.antecedent.linear.find(
        h => forward.getPredicateHead(h) === 'code');
      assert(result.preserved.includes(codeHash), 'code should be preserved');

      // pc, sh, stack have different hashes → consumed/produced
      assert.strictEqual(result.preserved.length, 1, 'only code is preserved in v1');

      // 4 consumed (pc, sh, stack, stack), 3 produced (pc', sh', stack')
      assert.strictEqual(result.consumed.length, 4, '4 consumed');
      assert.strictEqual(result.produced.length, 3, '3 produced');

      // Verify multiset invariant
      const anteHashes = sortedHashes(rule.antecedent.linear);
      const reconstituted = sortedHashes([...result.preserved, ...result.consumed]);
      assert.deepStrictEqual(reconstituted, anteHashes, 'multiset invariant');
    });

    it('evm/swap1: all different hashes — nothing preserved in v1', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const rule = calc.forwardRules.find(r => r.name === 'evm/swap1');
      const result = analyzeRule(rule);

      // Check if code is preserved (should be if same hash)
      const anteCode = rule.antecedent.linear.find(
        h => forward.getPredicateHead(h) === 'code');
      const conseqCode = rule.consequent.linear.find(
        h => forward.getPredicateHead(h) === 'code');

      if (anteCode === conseqCode) {
        assert(result.preserved.includes(anteCode), 'code preserved if same hash');
      }

      // Multiset invariant always holds
      const anteHashes = sortedHashes(rule.antecedent.linear);
      const reconstituted = sortedHashes([...result.preserved, ...result.consumed]);
      assert.deepStrictEqual(reconstituted, anteHashes, 'multiset invariant');
    });

    it('multiset invariants hold for ALL EVM rules', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      for (const rule of calc.forwardRules) {
        const result = analyzeRule(rule);

        // preserved + consumed = antecedent
        const anteHashes = sortedHashes(rule.antecedent.linear);
        const anteRecon = sortedHashes([...result.preserved, ...result.consumed]);
        assert.deepStrictEqual(anteRecon, anteHashes,
          `${rule.name}: preserved + consumed should equal antecedent`);

        // preserved + produced = consequent
        const conseqHashes = sortedHashes(rule.consequent.linear);
        const conseqRecon = sortedHashes([...result.preserved, ...result.produced]);
        assert.deepStrictEqual(conseqRecon, conseqHashes,
          `${rule.name}: preserved + produced should equal consequent`);
      }
    });
  });

  // ============================================================================
  // PART 7: analyzeDeltas — delta detection (same pred, different args)
  // ============================================================================

  describe('analyzeDeltas: delta detection', () => {

    function sortedHashes(arr) { return [...arr].sort((a, b) => a - b); }
    function assertMultisetEqual(actual, expected, msg) {
      assert.deepStrictEqual(sortedHashes(actual), sortedHashes(expected), msg);
    }

    // --- Single-pred deltas ---

    it('p _X -o p _Y: one delta (position 0 changed)', async () => {
      const rule = await makeRule('d1', 'p _X * !inc _X _Y -o { p _Y }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1, 'one delta');
      assert.strictEqual(result.deltas[0].pred, 'p');
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0],
        'position 0 changed');

      // consumed/produced should now exclude the delta pair
      assert.strictEqual(result.consumed.length, 0, 'no remaining consumed');
      assert.strictEqual(result.produced.length, 0, 'no remaining produced');
    });

    it('foo -o bar: no deltas (different preds)', async () => {
      const rule = await makeRule('d2', 'foo -o { bar }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 0, 'no deltas');
      assert.strictEqual(result.consumed.length, 1, 'foo consumed');
      assert.strictEqual(result.produced.length, 1, 'bar produced');
    });

    it('preserved: foo * bar -o foo * baz has no deltas (foo preserved)', async () => {
      const rule = await makeRule('d3', 'foo * bar -o { foo * baz }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 0, 'no deltas');
      assert.strictEqual(result.preserved.length, 1, 'foo preserved');
      assert.strictEqual(result.consumed.length, 1, 'bar consumed');
      assert.strictEqual(result.produced.length, 1, 'baz produced');
    });

    it('mixed: keep * p _X * gone * !inc _X _Y -o keep * p _Y * born', async () => {
      const rule = await makeRule('d4',
        'keep * p _X * gone * !inc _X _Y -o { keep * p _Y * born }');
      const result = analyzeDeltas(rule);

      // keep is preserved (identical hash)
      assert.strictEqual(result.preserved.length, 1, '1 preserved (keep)');

      // p is a delta (same pred, arg 0 changed)
      assert.strictEqual(result.deltas.length, 1, '1 delta (p)');
      assert.strictEqual(result.deltas[0].pred, 'p');
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0]);

      // gone consumed, born produced
      assert.strictEqual(result.consumed.length, 1, '1 consumed (gone)');
      assert.strictEqual(result.produced.length, 1, '1 produced (born)');
    });

    // --- Multi-position deltas ---

    it('f _X _Y * !inc _X _X2 * !inc _Y _Y2 -o f _X2 _Y2: both positions changed', async () => {
      const rule = await makeRule('d5',
        'f _X _Y * !inc _X _X2 * !inc _Y _Y2 -o { f _X2 _Y2 }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1, '1 delta');
      assert.strictEqual(result.deltas[0].pred, 'f');
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0, 1],
        'both positions changed');
    });

    it('f _X _Y * !inc _X _Z -o f _Z _Y: only position 0 changed', async () => {
      const rule = await makeRule('d6',
        'f _X _Y * !inc _X _Z -o { f _Z _Y }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1, '1 delta');
      assert.strictEqual(result.deltas[0].pred, 'f');
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0],
        'only position 0 changed');

      // Verify unchanged position has same child hash
      const anteF = result.deltas[0].anteHash;
      const conseqF = result.deltas[0].conseqHash;
      assert.strictEqual(Store.child(anteF, 1), Store.child(conseqF, 1),
        'position 1 is unchanged');
      assert.notStrictEqual(Store.child(anteF, 0), Store.child(conseqF, 0),
        'position 0 is changed');
    });

    // --- Nested structure deltas ---

    it('f (g _X) * !inc _X _Y -o f (g _Y): nested delta', async () => {
      const rule = await makeRule('d7',
        'f (g _X) * !inc _X _Y -o { f (g _Y) }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1);
      assert.strictEqual(result.deltas[0].pred, 'f');
      // Position 0 changes (g(_X) → g(_Y))
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0]);
    });

    it('f _X (g _Y) * !inc _X _Z -o f _Z (g _Y): partial nested delta', async () => {
      const rule = await makeRule('d8',
        'f _X (g _Y) * !inc _X _Z -o { f _Z (g _Y) }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1);
      assert.strictEqual(result.deltas[0].pred, 'f');
      assert.deepStrictEqual(result.deltas[0].changedPositions, [0],
        'only position 0 changed, position 1 (g _Y) preserved');
    });

    // --- N:M multi-match with deltas ---

    it('coin * coin -o coin: no deltas (identical hashes, not different-arg)', async () => {
      // All coins have identical hash → all go to preserved/consumed, no deltas
      const rule = await makeRule('d9', 'coin * coin -o { coin }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 0, 'no deltas');
      assert.strictEqual(result.preserved.length, 1, '1 preserved');
      assert.strictEqual(result.consumed.length, 1, '1 consumed');
    });

    it('p _X * p _Y -o p _Z: 1 delta, 1 consumed (2 consumed, 1 produced)', async () => {
      // Two consumed p with different args, one produced p with different arg
      // Should pair one consumed with the produced → 1 delta + 1 remaining consumed
      const rule = await makeRule('d10',
        'p _X * p _Y * !merge _X _Y _Z -o { p _Z }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1, '1 delta');
      assert.strictEqual(result.deltas[0].pred, 'p');
      assert.strictEqual(result.consumed.length, 1, '1 remaining consumed');
      assert.strictEqual(result.produced.length, 0, 'no remaining produced');
    });

    it('p _X -o p _Y * p _Z: 1 delta, 1 produced (1 consumed, 2 produced)', async () => {
      const rule = await makeRule('d11',
        'p _X * !split _X _Y _Z -o { p _Y * p _Z }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 1, '1 delta');
      assert.strictEqual(result.deltas[0].pred, 'p');
      assert.strictEqual(result.consumed.length, 0, 'no remaining consumed');
      assert.strictEqual(result.produced.length, 1, '1 remaining produced');
    });

    it('p _X * p _Y -o p _Y * p _X: all preserved (hash matching)', async () => {
      // p(_X) appears on both sides → preserved. p(_Y) appears on both sides → preserved.
      // Content-addressing: p(_X) ante hash = p(_X) conseq hash, same for p(_Y).
      // So v1 sees both as preserved. 0 deltas.
      const rule = await makeRule('d12', 'p _X * p _Y -o { p _Y * p _X }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.preserved.length, 2, '2 preserved');
      assert.strictEqual(result.deltas.length, 0, '0 deltas');
      assert.strictEqual(result.consumed.length, 0, 'no consumed');
      assert.strictEqual(result.produced.length, 0, 'no produced');
    });

    // --- Zero-arg (atom) deltas impossible ---

    it('atoms have no deltas (different pred = different consumed/produced)', async () => {
      const rule = await makeRule('d13', 'a * b -o { c * d }');
      const result = analyzeDeltas(rule);

      assert.strictEqual(result.deltas.length, 0);
      assert.strictEqual(result.consumed.length, 2);
      assert.strictEqual(result.produced.length, 2);
    });

    // --- Multiset invariants for deltas ---

    it('multiset invariant: preserved + consumed + delta.ante = antecedent', async () => {
      const rule = await makeRule('dinv',
        'keep * p _X * q _A _B * gone * !inc _X _Y * !inc _A _A2 -o { keep * p _Y * q _A2 _B * born }');
      const result = analyzeDeltas(rule);

      const deltaAnteHashes = result.deltas.map(d => d.anteHash);
      const anteHashes = sortedHashes(rule.antecedent.linear);
      const reconstituted = sortedHashes([
        ...result.preserved,
        ...result.consumed,
        ...deltaAnteHashes
      ]);
      assert.deepStrictEqual(reconstituted, anteHashes,
        'preserved + consumed + delta.ante = antecedent');
    });

    it('multiset invariant: preserved + produced + delta.conseq = consequent', async () => {
      const rule = await makeRule('dinv2',
        'keep * p _X * q _A _B * gone * !inc _X _Y * !inc _A _A2 -o { keep * p _Y * q _A2 _B * born }');
      const result = analyzeDeltas(rule);

      const deltaConseqHashes = result.deltas.map(d => d.conseqHash);
      const conseqHashes = sortedHashes(rule.consequent.linear);
      const reconstituted = sortedHashes([
        ...result.preserved,
        ...result.produced,
        ...deltaConseqHashes
      ]);
      assert.deepStrictEqual(reconstituted, conseqHashes,
        'preserved + produced + delta.conseq = consequent');
    });

    // --- EVM rules ---

    it('evm/add: pc, sh are deltas; stack has 2 consumed, 1 produced delta', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const result = analyzeDeltas(rule);

      // code is preserved (identical hash)
      const codeHash = rule.antecedent.linear.find(
        h => forward.getPredicateHead(h) === 'code');
      assert(result.preserved.includes(codeHash), 'code preserved');

      // Check delta predicates
      const deltaPreds = result.deltas.map(d => d.pred);

      // pc should be a delta (PC → PC' via !inc)
      assert(deltaPreds.includes('pc'), `pc should be delta, got: ${deltaPreds}`);
      const pcDelta = result.deltas.find(d => d.pred === 'pc');
      assert.deepStrictEqual(pcDelta.changedPositions, [0], 'pc: position 0 changes');

      // sh should be a delta (SH → SH' — unwrap s() constructor)
      assert(deltaPreds.includes('sh'), `sh should be delta, got: ${deltaPreds}`);

      // evm/add does NOT have gas as a linear pattern (only eq, sload, etc. do)
      assert(!deltaPreds.includes('gas'), 'no gas in evm/add');
    });

    it('evm/add: stack has delta and extra consumed (2 ante, 1 conseq)', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const result = analyzeDeltas(rule);

      // stack: 2 consumed (pop X, Y), 1 produced (push X+Y)
      // → 1 delta pair + 1 remaining consumed
      const stackDeltas = result.deltas.filter(d => d.pred === 'stack');
      assert.strictEqual(stackDeltas.length, 1, '1 stack delta pair');

      const remainingConsumedStacks = result.consumed.filter(
        h => forward.getPredicateHead(h) === 'stack');
      assert.strictEqual(remainingConsumedStacks.length, 1, '1 stack remaining consumed');
    });

    it('multiset invariants hold for ALL EVM rules with deltas', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      for (const rule of calc.forwardRules) {
        const result = analyzeDeltas(rule);
        const deltaAnteHashes = result.deltas.map(d => d.anteHash);
        const deltaConseqHashes = result.deltas.map(d => d.conseqHash);

        // preserved + consumed + delta.ante = antecedent
        const anteHashes = sortedHashes(rule.antecedent.linear);
        const anteRecon = sortedHashes([
          ...result.preserved,
          ...result.consumed,
          ...deltaAnteHashes
        ]);
        assert.deepStrictEqual(anteRecon, anteHashes,
          `${rule.name}: preserved + consumed + delta.ante = antecedent`);

        // preserved + produced + delta.conseq = consequent
        const conseqHashes = sortedHashes(rule.consequent.linear);
        const conseqRecon = sortedHashes([
          ...result.preserved,
          ...result.produced,
          ...deltaConseqHashes
        ]);
        assert.deepStrictEqual(conseqRecon, conseqHashes,
          `${rule.name}: preserved + produced + delta.conseq = consequent`);
      }
    });

    it('all EVM deltas have valid changedPositions', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      for (const rule of calc.forwardRules) {
        const result = analyzeDeltas(rule);
        for (const delta of result.deltas) {
          // changedPositions should be non-empty (otherwise it would be preserved)
          assert(delta.changedPositions.length > 0,
            `${rule.name}: delta ${delta.pred} should have at least one changed position`);

          // changedPositions should be within arity bounds
          const arity = Store.arity(delta.anteHash);
          for (const pos of delta.changedPositions) {
            assert(pos >= 0 && pos < arity,
              `${rule.name}: delta ${delta.pred} position ${pos} out of bounds (arity ${arity})`);
          }

          // Ante and conseq should have same pred head
          assert.strictEqual(
            forward.getPredicateHead(delta.anteHash),
            forward.getPredicateHead(delta.conseqHash),
            `${rule.name}: delta ante/conseq should have same pred head`);

          // Unchanged positions should have identical children
          const a = Store.arity(delta.anteHash);
          const changedSet = new Set(delta.changedPositions);
          for (let i = 0; i < a; i++) {
            if (!changedSet.has(i)) {
              assert.strictEqual(
                Store.child(delta.anteHash, i),
                Store.child(delta.conseqHash, i),
                `${rule.name}: delta ${delta.pred} position ${i} should be unchanged`);
            }
          }
        }
      }
    });
  });

  // ============================================================================
  // PART 8: compileRule integration — analysis metadata on compiled rules
  // ============================================================================

  describe('compileRule integration: analysis metadata', () => {

    it('compiled rule has analysis field', async () => {
      const rule = await makeRule('int1', 'foo * bar -o { foo * baz }');
      assert(rule.analysis, 'compiled rule should have analysis field');
      assert(Array.isArray(rule.analysis.preserved), 'analysis.preserved is array');
      assert(Array.isArray(rule.analysis.consumed), 'analysis.consumed is array');
      assert(Array.isArray(rule.analysis.produced), 'analysis.produced is array');
      assert(Array.isArray(rule.analysis.deltas), 'analysis.deltas is array');
    });

    it('analysis matches standalone analyzeDeltas call', async () => {
      const rule = await makeRule('int2',
        'keep * p _X * gone * !inc _X _Y -o { keep * p _Y * born }');

      // Analysis from compileRule should match standalone call
      const standalone = analyzeDeltas(rule);
      assert.deepStrictEqual(rule.analysis, standalone,
        'embedded analysis should equal standalone call');
    });

    it('EVM rules have analysis metadata via mde.load()', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      for (const rule of calc.forwardRules) {
        assert(rule.analysis, `${rule.name} should have analysis`);
        assert(Array.isArray(rule.analysis.preserved),
          `${rule.name} should have preserved array`);
        assert(Array.isArray(rule.analysis.deltas),
          `${rule.name} should have deltas array`);
      }
    });

    it('evm/add analysis matches expectations', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
      const rule = calc.forwardRules.find(r => r.name === 'evm/add');
      const a = rule.analysis;

      // code is preserved
      assert.strictEqual(a.preserved.length, 1, '1 preserved');
      assert.strictEqual(forward.getPredicateHead(a.preserved[0]), 'code');

      // pc, sh, stack are deltas (3 total: pc, sh, 1 of 2 stacks)
      const deltaPreds = a.deltas.map(d => d.pred).sort();
      assert.deepStrictEqual(deltaPreds, ['pc', 'sh', 'stack'],
        'deltas: pc, sh, stack');

      // 1 remaining consumed (extra stack)
      assert.strictEqual(a.consumed.length, 1, '1 remaining consumed');
      assert.strictEqual(forward.getPredicateHead(a.consumed[0]), 'stack');

      // 0 remaining produced
      assert.strictEqual(a.produced.length, 0, 'no remaining produced');
    });
  });

  // ============================================================================
  // PART 9: Stage 3 — preserved optimization cross-check
  // ============================================================================

  describe('Preserved optimization cross-check', () => {

    // Helper: compare two states for equality
    function statesEqual(s1, s2) {
      const l1 = Object.entries(s1.linear).filter(([, v]) => v > 0).sort(([a], [b]) => a - b);
      const l2 = Object.entries(s2.linear).filter(([, v]) => v > 0).sort(([a], [b]) => a - b);
      if (l1.length !== l2.length) return false;
      for (let i = 0; i < l1.length; i++) {
        if (l1[i][0] !== l2[i][0] || l1[i][1] !== l2[i][1]) return false;
      }
      const p1 = Object.keys(s1.persistent).sort();
      const p2 = Object.keys(s2.persistent).sort();
      if (p1.length !== p2.length) return false;
      for (let i = 0; i < p1.length; i++) {
        if (p1[i] !== p2[i]) return false;
      }
      return true;
    }

    function assertStatesEqual(s1, s2, msg) {
      if (!statesEqual(s1, s2)) {
        const fmt = s => JSON.stringify({
          linear: Object.entries(s.linear).filter(([,v]) => v > 0),
          persistent: Object.keys(s.persistent)
        });
        assert.fail(`${msg}\n  got:      ${fmt(s1)}\n  expected: ${fmt(s2)}`);
      }
    }

    // Cross-check helper: run same scenario with opt ON and OFF, compare
    function crossCheck(state, rules, opts, msg) {
      const r1 = forward.run(
        { linear: { ...state.linear }, persistent: { ...state.persistent } },
        rules, { ...opts, optimizePreserved: false });
      const r2 = forward.run(
        { linear: { ...state.linear }, persistent: { ...state.persistent } },
        rules, { ...opts, optimizePreserved: true });

      assertStatesEqual(r1.state, r2.state,
        `${msg}: final states should match`);
      assert.strictEqual(r1.steps, r2.steps,
        `${msg}: step count should match`);
      assert.strictEqual(r1.quiescent, r2.quiescent,
        `${msg}: quiescence should match`);
      return { unopt: r1, opt: r2 };
    }

    it('foo -o bar: no preserved, same behavior', async () => {
      const rule = await makeRule('xc1', 'foo -o { bar }');
      const foo = await mde.parseExpr('foo');
      const state = forward.createState({ [foo]: 1 }, {});
      crossCheck(state, [rule], { maxSteps: 10 }, 'foo→bar');
    });

    it('foo * bar -o foo * baz: foo preserved', async () => {
      const rule = await makeRule('xc2', 'foo * bar -o { foo * baz }');
      const foo = await mde.parseExpr('foo');
      const bar = await mde.parseExpr('bar');
      const state = forward.createState({ [foo]: 1, [bar]: 1 }, {});
      crossCheck(state, [rule], { maxSteps: 10 }, 'preserve foo');
    });

    it('coin * coin -o coin: resource counting with preserved', async () => {
      const rule = await makeRule('xc3', 'coin * coin -o { coin }');
      const coin = await mde.parseExpr('coin');

      // With 3 coins: should fire once (consume 2, produce 1 → net 2)
      // then fire again (consume 2, produce 1 → net 1), then stop
      // Wait — coin*coin→coin consumes 2 produces 1 → net -1 each step
      // 3 coins → step 1 → 2 coins → step 2 → 1 coin → stop
      crossCheck(
        forward.createState({ [coin]: 3 }, {}),
        [rule], { maxSteps: 10 }, 'coin×3 join'
      );
    });

    it('coin * coin -o coin: with exactly 2 coins', async () => {
      const rule = await makeRule('xc3b', 'coin * coin -o { coin }');
      const coin = await mde.parseExpr('coin');
      crossCheck(
        forward.createState({ [coin]: 2 }, {}),
        [rule], { maxSteps: 10 }, 'coin×2 join'
      );
    });

    it('coin * coin -o coin: with 1 coin (should not fire)', async () => {
      const rule = await makeRule('xc3c', 'coin * coin -o { coin }');
      const coin = await mde.parseExpr('coin');
      crossCheck(
        forward.createState({ [coin]: 1 }, {}),
        [rule], { maxSteps: 10 }, 'coin×1 join'
      );
    });

    it('a * b -o b * a: swap (both preserved, no-op)', async () => {
      const rule = await makeRule('xc4', 'a * b -o { b * a }');
      const a = await mde.parseExpr('a');
      const b = await mde.parseExpr('b');
      const state = forward.createState({ [a]: 1, [b]: 1 }, {});
      // This rule is a no-op (swap identity). But does it loop?
      // It fires once (consuming a,b → producing b,a → same state) then fires again...
      // Actually: antecedent matches, so it fires → produces same state → matches again → infinite loop
      // Limit steps to check both modes agree
      crossCheck(state, [rule], { maxSteps: 5 }, 'swap a,b');
    });

    it('a * a -o a * b: partial preserve', async () => {
      const rule = await makeRule('xc5', 'a * a -o { a * b }');
      const a = await mde.parseExpr('a');
      const state = forward.createState({ [a]: 2 }, {});
      crossCheck(state, [rule], { maxSteps: 10 }, 'partial preserve a');
    });

    it('foo -o foo * bar: infinite producer (limited)', async () => {
      const rule = await makeRule('xc6', 'foo -o { foo * bar }');
      const foo = await mde.parseExpr('foo');
      const state = forward.createState({ [foo]: 1 }, {});
      crossCheck(state, [rule], { maxSteps: 10 }, 'infinite producer');
    });

    it('multi-rule: r1 produces what r2 consumes', async () => {
      const r1 = await makeRule('xc7a', 'a -o { b }');
      const r2 = await makeRule('xc7b', 'b -o { c }');
      const a = await mde.parseExpr('a');
      const state = forward.createState({ [a]: 1 }, {});
      crossCheck(state, [r1, r2], { maxSteps: 10 }, 'chain a→b→c');
    });

    it('preserved with metavars: p _X * bar -o p _X * baz', async () => {
      const rule = await makeRule('xc8', 'p _X * bar -o { p _X * baz }');
      const pFoo = Store.put('p', [await mde.parseExpr('foo')]);
      const bar = await mde.parseExpr('bar');
      const state = forward.createState({ [pFoo]: 1, [bar]: 1 }, {});
      crossCheck(state, [rule], { maxSteps: 10 }, 'metavar preserve');
    });

    it('EVM multisig: full execution cross-check', async () => {
      const programsDir = path.join(__dirname, '../../calculus/ill/programs');
      const fs = require('fs');
      const calc = await mde.load([
        path.join(programsDir, 'bin.ill'),
        path.join(programsDir, 'evm.ill'),
        path.join(programsDir, 'multisig_code.ill')
      ]);

      // Build initial state (same as benchmark)
      const initState = { linear: {}, persistent: {} };
      for (const f of ['pc N_75', 'sh ee', 'gas N_ffff', 'caller sender_addr', 'sender member01']) {
        initState.linear[await mde.parseExpr(f)] = 1;
      }
      const codeFile = fs.readFileSync(path.join(programsDir, 'multisig_code.ill'), 'utf8');
      for (const line of codeFile.split('\n')) {
        const trimmed = line.split('%')[0].trim();
        if (!trimmed || !trimmed.startsWith('code')) continue;
        const parts = trimmed.replace(/\*.*$/, '').trim();
        if (parts) initState.linear[await mde.parseExpr(parts)] = 1;
      }

      const calcCtx = { types: calc.types, clauses: calc.clauses };

      const r1 = forward.run(
        { linear: { ...initState.linear }, persistent: { ...initState.persistent } },
        calc.forwardRules,
        { maxSteps: 200, calc: calcCtx, optimizePreserved: false });

      const r2 = forward.run(
        { linear: { ...initState.linear }, persistent: { ...initState.persistent } },
        calc.forwardRules,
        { maxSteps: 200, calc: calcCtx, optimizePreserved: true });

      assertStatesEqual(r1.state, r2.state,
        'EVM multisig: final states should match');
      assert.strictEqual(r1.steps, r2.steps,
        'EVM multisig: step count should match');
      assert.strictEqual(r1.quiescent, r2.quiescent,
        'EVM multisig: quiescence should match');
    });
  });
});
