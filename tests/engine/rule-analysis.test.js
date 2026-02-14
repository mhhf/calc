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
});
