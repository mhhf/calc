/**
 * Tests for bytecode loader + extraGrade0Facts compose integration (Phase C+D of TODO_0160).
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { loadBytecode, bytecodeArrGetGuard } = require('../../lib/engine/ill/bytecode-loader');
const { intToBin, binToInt } = require('../../lib/engine/ill/ffi/convert');
const { GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, compileRule, flattenAntecedent } = require('../../lib/engine/compile');
const { getPredicateHead } = require('../../lib/kernel/ast');
const { composeGrade0 } = require('../../lib/engine/compose');
const { getModes } = require('../../lib/engine/opt/ffi');

const COMPILE_OPTS = { connectives: ILL_CONNECTIVES, getModes };

function makeRule(name, anteHash, conseqBodyHash) {
  const conseqHash = Store.put('monad', [conseqBodyHash]);
  const hash = Store.put('loli', [anteHash, conseqHash]);
  return compileRule(
    { name, hash, antecedent: anteHash, consequent: conseqHash },
    COMPILE_OPTS
  );
}

function tensor(...hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

// ─── Bytecode loader unit tests ─────────────────────────────────────────────

describe('bytecode-loader: loadBytecode', () => {
  beforeEach(() => Store.clear());

  it('loads simple bytecode: PUSH1 0x40 PUSH1 0x00', () => {
    // 6040 6000 = PUSH1 0x40, PUSH1 0x00
    const result = loadBytecode('60406000');
    assert.ok(result.arrayHash, 'should have arrayHash');
    assert.ok(result.facts instanceof Map);
    assert.ok(result.entryPoints instanceof Set);

    const arrGetFacts = result.facts.get('arr_get');
    assert.ok(arrGetFacts, 'should have arr_get facts');

    // Semantic: PC0=PUSH1(0x60), PC1=filler, PC2=PUSH1(0x60), PC3=filler, PC4=0 (implicit STOP)
    // PUSH data positions (PC1, PC3) are fillers — skipped to prevent phantom rules.
    // Pre-scan extends array when PUSH data reaches end of bytecode.
    assert.equal(arrGetFacts.length, 3, '3 semantic positions (PUSH data fillers skipped)');

    // Check PC0 value = 0x60 (PUSH1 opcode)
    const pc0 = arrGetFacts[0].hash;
    assert.equal(Store.tag(pc0), 'arr_get');
    const pc0val = Store.child(pc0, 2); // 3rd arg = value
    assert.equal(binToInt(pc0val), 0x60n, 'PC0 = PUSH1 opcode (0x60)');

    // PC1 is filler (skipped), next fact is PC2
    const pc2 = arrGetFacts[1].hash;
    const pc2val = Store.child(pc2, 2);
    assert.equal(binToInt(pc2val), 0x60n, 'PC2 = PUSH1 opcode (0x60)');
  });

  it('handles 0x prefix', () => {
    const r1 = loadBytecode('0x6040');
    const r2 = loadBytecode('6040');
    // Same bytecode → same semantic content
    assert.equal(r1.facts.get('arr_get').length, r2.facts.get('arr_get').length);
  });

  it('rejects odd-length hex', () => {
    assert.throws(() => loadBytecode('604'), /Odd-length/);
  });

  it('detects JUMPDEST entry points', () => {
    // 00 5b 00 5b = STOP, JUMPDEST, STOP, JUMPDEST
    const result = loadBytecode('005b005b');
    assert.ok(result.entryPoints.has(0), 'PC=0 always entry');
    assert.ok(result.entryPoints.has(1), 'PC=1 is JUMPDEST');
    assert.ok(result.entryPoints.has(3), 'PC=3 is JUMPDEST');
    assert.ok(!result.entryPoints.has(2), 'PC=2 is STOP, not entry');
  });

  it('JUMPDEST inside PUSH data is NOT an entry point', () => {
    // 61 5b 00 = PUSH2, data=[0x5b, 0x00] — the 0x5b is PUSH data, not JUMPDEST
    const result = loadBytecode('615b00');
    assert.ok(result.entryPoints.has(0), 'PC=0 always entry');
    assert.ok(!result.entryPoints.has(1), 'PC=1 is PUSH2 data, not JUMPDEST');
    assert.equal(result.entryPoints.size, 1, 'only PC=0 is entry');
  });

  it('uses custom array name in fact labels', () => {
    const result = loadBytecode('00', 'mycode');
    const facts = result.facts.get('arr_get');
    assert.ok(facts.length > 0);
    // First arg is raw arrlit (FFI-compatible), name is cosmetic
    const arg0 = Store.child(facts[0].hash, 0);
    assert.equal(Store.tag(arg0), 'arrlit');
    assert.ok(facts[0].name.includes('mycode'), 'label includes custom name');
  });

  it('semantic grouping: PUSH2 combines 2 data bytes', () => {
    // 61 AB CD = PUSH2 0xABCD
    const result = loadBytecode('61abcd');
    const facts = result.facts.get('arr_get');
    // Semantic: PC0=PUSH2(0x61), PC1=filler, PC2=filler, PC3=0 (implicit STOP)
    // All PUSH data positions (PC1, PC2) are fillers — skipped to prevent phantom rules.
    assert.equal(facts.length, 2, '2 semantic positions (PUSH data fillers skipped)');

    const pc0val = Store.child(facts[0].hash, 2);
    assert.equal(binToInt(pc0val), 0x61n, 'PC0 = PUSH2 opcode');

    // facts[1] is PC3 (implicit STOP), PC1 and PC2 are fillers
    const pc3val = Store.child(facts[1].hash, 2);
    assert.equal(binToInt(pc3val), 0n, 'PC3 = implicit STOP');
  });

  it('fact structure compatible with composeGrade0', () => {
    const result = loadBytecode('6040');
    const facts = result.facts.get('arr_get');
    for (const f of facts) {
      assert.ok(typeof f.name === 'string', 'has name');
      assert.ok(typeof f.hash === 'number', 'has hash');
      assert.equal(Store.tag(f.hash), 'arr_get', 'tag is arr_get');
      assert.equal(Store.arity(f.hash), 3, 'arity is 3');
    }
  });
});

// ─── extraGrade0Facts compose integration ───────────────────────────────────

describe('compose: extraGrade0Facts parameter', () => {
  beforeEach(() => Store.clear());

  it('specializes rules using extraGrade0Facts', () => {
    // Rule: !arr_get BC PC Val * foo PC -o { bar Val }
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const arr_get_BC_PC_Val = Store.put('arr_get', [BC, PC, Val]);
    const bang_arr_get = Store.put('bang', [GRADE_W, arr_get_BC_PC_Val]);
    const foo_PC = Store.put('foo', [PC]);
    const bar_Val = Store.put('bar', [Val]);
    const rule = makeRule('r', tensor(bang_arr_get, foo_PC), bar_Val);

    // External facts: arr_get(myArr, 0, 0x60) and arr_get(myArr, 1, 0x40)
    const myArr = Store.put('myarr', [Store.put('atom', ['hash1'])]);
    const pc0 = intToBin(0n);
    const pc1 = intToBin(1n);
    const v60 = intToBin(0x60n);
    const v40 = intToBin(0x40n);
    const extraFacts = new Map([
      ['arr_get', [
        { name: 'arr_get/myarr:0', hash: Store.put('arr_get', [myArr, pc0, v60]) },
        { name: 'arr_get/myarr:1', hash: Store.put('arr_get', [myArr, pc1, v40]) },
      ]],
    ]);

    const result = composeGrade0([rule], ILL_CONNECTIVES, null, null, null, extraFacts);
    assert.equal(result.diagnostics.errors.length, 0, 'no errors');
    assert.equal(result.composedRules.length, 2, '2 specialized rules');
    assert.equal(result.diagnostics.specializations, 2);
    assert.ok(result.removedNames.has('r'), 'original removed');

    // Verify arr_get goals resolved
    const rc = resolveConnectives(ILL_CONNECTIVES);
    for (const raw of result.composedRules) {
      const anteFlat = flattenAntecedent(raw.antecedent, rc);
      for (const p of anteFlat.persistent) {
        assert.notEqual(getPredicateHead(p), 'arr_get', 'no arr_get goals remain');
      }
    }
  });

  it('merges extraGrade0Facts with clause-derived facts', () => {
    // Rule: !is_push OP N * !arr_get BC PC Val * foo -o { bar N Val }
    const OP = Store.put('metavar', ['OP']);
    const N = Store.put('metavar', ['N']);
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const is_push = Store.put('is_push', [OP, N]);
    const arr_get = Store.put('arr_get', [BC, PC, Val]);
    const bang_is_push = Store.put('bang', [GRADE_W, is_push]);
    const bang_arr_get = Store.put('bang', [GRADE_W, arr_get]);
    const foo = Store.put('atom', ['foo']);
    const bar = Store.put('bar', [N, Val]);
    const rule = makeRule('r', tensor(bang_is_push, bang_arr_get, foo), bar);

    // Clause-derived: is_push facts
    const h60 = Store.put('atom', ['h60']);
    const v1 = Store.put('atom', ['v1']);
    const clauses = new Map([
      ['is_push/1', { hash: Store.put('is_push', [h60, v1]), premises: [], grade0: true }],
    ]);

    // External: arr_get facts
    const myArr = Store.put('myarr', [Store.put('atom', ['arr1'])]);
    const extraFacts = new Map([
      ['arr_get', [
        { name: 'ag/0', hash: Store.put('arr_get', [myArr, intToBin(0n), intToBin(0x60n)]) },
      ]],
    ]);

    const result = composeGrade0([rule], ILL_CONNECTIVES, null, clauses, null, extraFacts);
    assert.equal(result.diagnostics.errors.length, 0);
    // Stage 1: is_push → 1 specialized rule (OP=h60, N=v1)
    // Stage 2: arr_get → from that 1 rule, 1 specialization (arr_get matches)
    assert.equal(result.composedRules.length, 1, '1 fully specialized rule');
    assert.ok(result.diagnostics.specializations >= 2, 'at least 2 specialization steps');
  });

  it('implicit CWA: unmatched goals drop the rule', () => {
    // Rule: !lookup KEY Val * foo -o { bar Val }
    const KEY = Store.put('metavar', ['KEY']);
    const Val = Store.put('metavar', ['Val']);
    const lookup = Store.put('lookup', [KEY, Val]);
    const bang_lookup = Store.put('bang', [GRADE_W, lookup]);
    const foo = Store.put('atom', ['foo']);
    const bar = Store.put('bar', [Val]);
    const rule = makeRule('r', tensor(bang_lookup, foo), bar);

    // Provide a lookup fact for key 'k1' but not for any key that matches a second rule
    const k1 = Store.put('atom', ['k1']);
    const va = Store.put('atom', ['va']);

    // Rule 2: !lookup KEY2 Val2 * baz -o { done Val2 } — uses same predicate
    const KEY2 = Store.put('metavar', ['KEY2']);
    const Val2 = Store.put('metavar', ['Val2']);
    const lookup2 = Store.put('lookup', [KEY2, Val2]);
    const bang_lookup2 = Store.put('bang', [GRADE_W, lookup2]);
    const baz = Store.put('atom', ['baz']);
    const done = Store.put('done', [Val2]);
    const rule2 = makeRule('r2', tensor(bang_lookup2, baz), done);

    const extraFacts = new Map([
      ['lookup', [{ name: 'lk/k1', hash: Store.put('lookup', [k1, va]) }]],
    ]);

    const result = composeGrade0([rule, rule2], ILL_CONNECTIVES, null, null, null, extraFacts);
    // Both rules have lookup goals → both get specialized.
    // Both match the single fact → both produce 1 specialized rule.
    assert.equal(result.composedRules.length, 2, '2 specialized rules (one per original)');
    assert.equal(result.diagnostics.specializations, 2);
  });

  it('multi-stage: step → is_push → arr_get three-stage DAG', () => {
    // This tests the full three-stage composition pipeline:
    // Stage 1: step (opcode class) — from clauses
    // Stage 2: is_push (opcode decoder) — from clauses
    // Stage 3: arr_get (bytecode access) — from extraGrade0Facts

    // Rule: !step OP Type * !is_push OP N * !arr_get BC PC Val * resource PC -o { result N Val }
    const OP = Store.put('metavar', ['OP']);
    const Type = Store.put('metavar', ['Type']);
    const N = Store.put('metavar', ['N']);
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);

    const step_goal = Store.put('step', [OP, Type]);
    const is_push_goal = Store.put('is_push', [OP, N]);
    const arr_get_goal = Store.put('arr_get', [BC, PC, Val]);
    const resource = Store.put('resource', [PC]);
    const result_term = Store.put('result', [N, Val]);

    const rule = makeRule('r',
      tensor(
        Store.put('bang', [GRADE_W, step_goal]),
        Store.put('bang', [GRADE_W, is_push_goal]),
        Store.put('bang', [GRADE_W, arr_get_goal]),
        resource
      ),
      result_term
    );

    // Grade-0 clauses: step and is_push
    const h60 = Store.put('atom', ['h60']);
    const push_type = Store.put('atom', ['push_type']);
    const v1 = Store.put('atom', ['v1']);
    const clauses = new Map([
      ['step/push', { hash: Store.put('step', [h60, push_type]), premises: [], grade0: true }],
      ['is_push/1', { hash: Store.put('is_push', [h60, v1]), premises: [], grade0: true }],
    ]);

    // External: arr_get facts (from bytecode)
    const myArr = Store.put('myarr', [Store.put('atom', ['bc1'])]);
    const extraFacts = new Map([
      ['arr_get', [
        { name: 'ag/0', hash: Store.put('arr_get', [myArr, intToBin(0n), intToBin(0x60n)]) },
        { name: 'ag/2', hash: Store.put('arr_get', [myArr, intToBin(2n), intToBin(0x00n)]) },
      ]],
    ]);

    const res = composeGrade0([rule], ILL_CONNECTIVES, null, clauses, null, extraFacts);
    assert.equal(res.diagnostics.errors.length, 0, 'no errors');

    // After step specialization: OP=h60 (only 1 step fact matches)
    // After is_push: OP=h60 matches is_push/1 → N=v1
    // After arr_get: 2 facts → 2 specialized rules
    assert.equal(res.composedRules.length, 2, '2 fully specialized rules');
    assert.ok(res.removedNames.has('r'));

    // Verify all persistent goals are resolved
    const rc = resolveConnectives(ILL_CONNECTIVES);
    for (const raw of res.composedRules) {
      const anteFlat = flattenAntecedent(raw.antecedent, rc);
      assert.equal(anteFlat.persistent.length, 0, 'all persistent goals resolved');
    }
  });

  it('unification filters: bytecode arr_get does not over-specialize', () => {
    // Two rules: one uses arr_get with a ground first arg, the other with a different ground first arg.
    // Only the one matching the facts should produce specialized rules.

    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);

    // Rule 1: !arr_get(code_arr, PC, Val) * ... → matches bytecode facts
    const codeArr = Store.put('code_arr', [Store.put('atom', ['h1'])]);
    const arr_get1 = Store.put('arr_get', [codeArr, PC, Val]);
    const rule1 = makeRule('code_rule',
      tensor(Store.put('bang', [GRADE_W, arr_get1]), Store.put('atom', ['a'])),
      Store.put('atom', ['b'])
    );

    // Rule 2: !arr_get(stack_arr, PC, Val) * ... → different array, should NOT match
    const stackArr = Store.put('stack_arr', [Store.put('atom', ['h2'])]);
    const PC2 = Store.put('metavar', ['PC2']);
    const Val2 = Store.put('metavar', ['Val2']);
    const arr_get2 = Store.put('arr_get', [stackArr, PC2, Val2]);
    const rule2 = makeRule('stack_rule',
      tensor(Store.put('bang', [GRADE_W, arr_get2]), Store.put('atom', ['c'])),
      Store.put('atom', ['d'])
    );

    // Facts use code_arr
    const extraFacts = new Map([
      ['arr_get', [
        { name: 'ag/0', hash: Store.put('arr_get', [codeArr, intToBin(0n), intToBin(0x60n)]) },
      ]],
    ]);

    const result = composeGrade0([rule1, rule2], ILL_CONNECTIVES, null, null, null, extraFacts);
    assert.equal(result.diagnostics.errors.length, 0);

    // rule1's arr_get(code_arr, ...) unifies with fact → 1 specialized rule
    // rule2's arr_get(stack_arr, ...) does NOT unify with code_arr fact → 0 specialized rules
    // rule2 is dropped (implicit CWA — it had a matching pred but no unifying fact)
    assert.equal(result.composedRules.length, 1, 'only code_rule specialized');
    assert.ok(result.composedRules[0].name.includes('code_rule'));
  });

  it('bytecode loader → compose pipeline end-to-end', () => {
    // Load real-ish bytecode, feed facts into compose
    // Bytecode: PUSH1 0x40 PUSH1 0x00 JUMPDEST STOP = 6040 6000 5b 00
    const bc = loadBytecode('604060005b00');
    assert.ok(bc.entryPoints.has(0));
    assert.ok(bc.entryPoints.has(4), 'JUMPDEST at PC=4');
    assert.equal(bc.entryPoints.size, 2);

    // Rule that reads bytecode
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const arr_get_goal = Store.put('arr_get', [BC, PC, Val]);
    const resource = Store.put('resource', [PC]);
    const out = Store.put('out', [Val]);
    const rule = makeRule('read_bc',
      tensor(Store.put('bang', [GRADE_W, arr_get_goal]), resource),
      out
    );

    const result = composeGrade0([rule], ILL_CONNECTIVES, null, null, null, bc.facts);
    assert.equal(result.diagnostics.errors.length, 0);
    // 4 non-filler positions (PC0, PC2, PC4, PC5) → 4 specialized rules
    assert.equal(result.composedRules.length, 4, 'one rule per non-filler position');
    assert.ok(result.removedNames.has('read_bc'));
  });
});

// ─── Entry point filtering ──────────────────────────────────────────────────

describe('bytecode-loader: entry point pre-filter', () => {
  beforeEach(() => Store.clear());

  it('filter arr_get facts to entry points only', () => {
    // Load bytecode and manually filter to entry points
    // PUSH1 0x40 PUSH1 0x00 JUMPDEST STOP = 6040 6000 5b 00
    const bc = loadBytecode('604060005b00');
    const allFacts = bc.facts.get('arr_get');
    // Filter by actual PC value in fact, not array index
    const entryFacts = allFacts.filter(f => {
      const pc = Number(binToInt(Store.child(f.hash, 1)));
      return bc.entryPoints.has(pc);
    });

    // Only PC=0 (PUSH1) and PC=4 (JUMPDEST) are entry points
    assert.equal(entryFacts.length, 2, '2 entry point facts');

    // Verify PC values
    const pcs = entryFacts.map(f => Number(binToInt(Store.child(f.hash, 1))));
    assert.ok(pcs.includes(0), 'PC=0');
    assert.ok(pcs.includes(4), 'PC=4 (JUMPDEST)');
  });

  it('entry-filtered compose produces fewer rules', () => {
    const bc = loadBytecode('604060005b00');

    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const arr_get_goal = Store.put('arr_get', [BC, PC, Val]);
    const resource = Store.put('resource', [PC]);
    const out = Store.put('out', [Val]);
    const rule = makeRule('r',
      tensor(Store.put('bang', [GRADE_W, arr_get_goal]), resource),
      out
    );

    // All non-filler facts → 4 rules
    const res1 = composeGrade0([rule], ILL_CONNECTIVES, null, null, null, bc.facts);
    assert.equal(res1.composedRules.length, 4);

    Store.clear();
    // Rebuild after clear — filter by actual PC value
    const bc2 = loadBytecode('604060005b00');
    const entryFacts2 = bc2.facts.get('arr_get').filter(f => {
      const pc = Number(binToInt(Store.child(f.hash, 1)));
      return bc2.entryPoints.has(pc);
    });
    const filteredFacts = new Map([['arr_get', entryFacts2]]);

    const BC2 = Store.put('metavar', ['BC2']);
    const PC2 = Store.put('metavar', ['PC2']);
    const Val2 = Store.put('metavar', ['Val2']);
    const rule2 = makeRule('r2',
      tensor(
        Store.put('bang', [GRADE_W, Store.put('arr_get', [BC2, PC2, Val2])]),
        Store.put('resource', [PC2])
      ),
      Store.put('out', [Val2])
    );

    const res2 = composeGrade0([rule2], ILL_CONNECTIVES, null, null, null, filteredFacts);
    assert.equal(res2.composedRules.length, 2, 'only 2 rules (entry points only)');
  });
});

// ─── Scoping guard ──────────────────────────────────────────────────────────

describe('bytecode-loader: bytecodeArrGetGuard', () => {
  beforeEach(() => Store.clear());

  it('allows arr_get when arg₁ matches bytecode linear resource', () => {
    // Rule: !arr_get(BC, PC, Val) * bytecode BC -o { out Val }
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const arr_get_goal = Store.put('arr_get', [BC, PC, Val]);
    const bang_arr_get = Store.put('bang', [GRADE_W, arr_get_goal]);
    const bytecode_BC = Store.put('bytecode', [BC]);
    const out = Store.put('out', [Val]);
    const rule = makeRule('bc_rule', tensor(bang_arr_get, bytecode_BC), out);

    const rc = resolveConnectives(ILL_CONNECTIVES);
    const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
    const goalMatch = ante.persistent.find(g => getPredicateHead(g) === 'arr_get');

    assert.equal(
      bytecodeArrGetGuard(rule, 'arr_get', goalMatch, ante),
      true,
      'should allow — BC matches bytecode resource'
    );
  });

  it('rejects arr_get when arg₁ matches stack, not bytecode', () => {
    // Rule: !arr_get(S, I, Val) * stack S -o { peeked Val }
    const S = Store.put('metavar', ['S']);
    const I = Store.put('metavar', ['I']);
    const Val = Store.put('metavar', ['Val']);
    const arr_get_goal = Store.put('arr_get', [S, I, Val]);
    const bang_arr_get = Store.put('bang', [GRADE_W, arr_get_goal]);
    const stack_S = Store.put('stack', [S]);
    const peeked = Store.put('peeked', [Val]);
    const rule = makeRule('stack_rule', tensor(bang_arr_get, stack_S), peeked);

    const rc = resolveConnectives(ILL_CONNECTIVES);
    const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
    const goalMatch = ante.persistent.find(g => getPredicateHead(g) === 'arr_get');

    assert.equal(
      bytecodeArrGetGuard(rule, 'arr_get', goalMatch, ante),
      false,
      'should reject — S from stack, not bytecode'
    );
  });

  it('passes through non-arr_get predicates unconditionally', () => {
    assert.equal(bytecodeArrGetGuard({}, 'is_push', 0, { linear: [] }), true);
    assert.equal(bytecodeArrGetGuard({}, 'step', 0, { linear: [] }), true);
  });

  it('scopeGuard prevents stack arr_get specialization in compose', () => {
    // Two rules with free metavar arg₁:
    // Rule 1: !arr_get(BC, PC, Val) * bytecode BC -o { read Val }
    // Rule 2: !arr_get(S, I, Val) * stack S -o { peek Val }
    const BC = Store.put('metavar', ['BC']);
    const PC = Store.put('metavar', ['PC']);
    const Val = Store.put('metavar', ['Val']);
    const rule1 = makeRule('bc_read',
      tensor(
        Store.put('bang', [GRADE_W, Store.put('arr_get', [BC, PC, Val])]),
        Store.put('bytecode', [BC])
      ),
      Store.put('read', [Val])
    );

    const S = Store.put('metavar', ['S']);
    const I = Store.put('metavar', ['I']);
    const Val2 = Store.put('metavar', ['Val2']);
    const rule2 = makeRule('stack_peek',
      tensor(
        Store.put('bang', [GRADE_W, Store.put('arr_get', [S, I, Val2])]),
        Store.put('stack', [S])
      ),
      Store.put('peek', [Val2])
    );

    const myArr = Store.put('myarr', [Store.put('atom', ['h1'])]);
    const extraFacts = new Map([
      ['arr_get', [
        { name: 'ag/0', hash: Store.put('arr_get', [myArr, intToBin(0n), intToBin(0x60n)]) },
        { name: 'ag/1', hash: Store.put('arr_get', [myArr, intToBin(1n), intToBin(0x40n)]) },
      ]],
    ]);

    // Without scoping guard: both rules get specialized (metavar arg₁ unifies with anything)
    const resNoGuard = composeGrade0([rule1, rule2], ILL_CONNECTIVES, null, null, null, extraFacts);
    assert.equal(resNoGuard.composedRules.length, 4, '4 rules without guard (2 per original)');

    Store.clear();

    // Rebuild with fresh hashes
    const BC2 = Store.put('metavar', ['BC2']);
    const PC2 = Store.put('metavar', ['PC2']);
    const Val3 = Store.put('metavar', ['Val3']);
    const rule1b = makeRule('bc_read',
      tensor(
        Store.put('bang', [GRADE_W, Store.put('arr_get', [BC2, PC2, Val3])]),
        Store.put('bytecode', [BC2])
      ),
      Store.put('read', [Val3])
    );

    const S2 = Store.put('metavar', ['S2']);
    const I2 = Store.put('metavar', ['I2']);
    const Val4 = Store.put('metavar', ['Val4']);
    const rule2b = makeRule('stack_peek',
      tensor(
        Store.put('bang', [GRADE_W, Store.put('arr_get', [S2, I2, Val4])]),
        Store.put('stack', [S2])
      ),
      Store.put('peek', [Val4])
    );

    const myArr2 = Store.put('myarr', [Store.put('atom', ['h1'])]);
    const extraFacts2 = new Map([
      ['arr_get', [
        { name: 'ag/0', hash: Store.put('arr_get', [myArr2, intToBin(0n), intToBin(0x60n)]) },
        { name: 'ag/1', hash: Store.put('arr_get', [myArr2, intToBin(1n), intToBin(0x40n)]) },
      ]],
    ]);

    // With scoping guard: only bc_read gets specialized, stack_peek passes through unchanged
    const resGuard = composeGrade0(
      [rule1b, rule2b], ILL_CONNECTIVES, null, null, null, extraFacts2, bytecodeArrGetGuard
    );
    // 2 specialized bc_read rules + 1 unmodified stack_peek (passed through by guard)
    assert.equal(resGuard.composedRules.length, 3, '3 rules: 2 specialized bc_read + 1 preserved stack_peek');
    assert.equal(resGuard.diagnostics.scopeGuarded, 1, '1 rule scope-guarded');
    const bcRules = resGuard.composedRules.filter(r => r.name.includes('bc_read'));
    assert.equal(bcRules.length, 2, '2 specialized bc_read rules');
    // stack_peek preserved with original name
    const stackRules = resGuard.composedRules.filter(r => r.name === 'stack_peek');
    assert.equal(stackRules.length, 1, 'stack_peek preserved unchanged');
  });
});

// ─── EVM integration: bytecode specialization ───────────────────────────────

describe('bytecode specialization: EVM integration', { timeout: 30000 }, () => {
  it('specializes real EVM rules with bytecode facts via load opts', () => {
    Store.clear();
    const path = require('path');
    const mde = require('../../lib/engine/index');

    const evmPath = path.join(__dirname, '../../calculus/ill/programs/evm.ill');

    // PUSH1 0x40 STOP = 60 40 00
    const bc = loadBytecode('604000');
    const entryFacts = bc.facts.get('arr_get').filter((_, i) => bc.entryPoints.has(i));
    const filteredFacts = new Map([['arr_get', entryFacts]]);

    // Load with bytecode facts + scoping guard injected into the compose pipeline
    const calc = mde.load(evmPath, {
      cache: false,
      extraGrade0Facts: filteredFacts,
      scopeGuard: bytecodeArrGetGuard,
    });

    // Should have specialized arr_get rules
    const arrGetRules = calc.forwardRules.filter(r => r.name.includes('arr_get/'));
    assert.ok(arrGetRules.length > 0, 'arr_get-specialized rules present');

    // Verify some specialized rules have ground PC values
    let hasGroundPC = false;
    for (const r of calc.forwardRules) {
      for (const pat of (r.antecedent.linear || [])) {
        if (Store.tag(pat) === 'pc') {
          const pcVal = Store.child(pat, 0);
          if (Store.tag(pcVal) === 'binlit') hasGroundPC = true;
        }
      }
    }
    assert.ok(hasGroundPC, 'some specialized rules have ground PC values');
  });

  it('bytecode specialization via load opts', () => {
    Store.clear();
    const path = require('path');
    const fs = require('fs');
    const os = require('os');
    const mde = require('../../lib/engine/index');

    // Minimal program with bytecode-dependent rule
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'bc-int-'));
    fs.writeFileSync(path.join(tmpDir, 'bc_test.ill'),
      'bc_src : type.\n' +
      'bc_dst : bin -> type.\n' +
      'bc_lk/0: !_0 bc_lk 0x0 0xa.\n' +
      'bc_lk/1: !_0 bc_lk 0x1 0xb.\n' +
      'bc_step: !bc_lk KEY VAL * bc_src -o { bc_dst VAL }.\n' +
      '#symex bc_src.\n'
    );

    const calc = mde.load(path.join(tmpDir, 'bc_test.ill'), { cache: false });

    // bc_step should be specialized against bc_lk facts
    const specialized = calc.forwardRules.filter(r => r.name.includes('bc_lk/'));
    assert.equal(specialized.length, 2, '2 specialized rules');

    // Execute and verify
    const queryHash = calc.queries.get('symex');
    const state = mde.decomposeQuery(queryHash);
    const result = calc.exec(state, { maxSteps: 5, trace: true });
    assert.ok(result.steps > 0, 'should execute');

    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });
});

// ─── Benchmark: composition timing ──────────────────────────────────────────

describe('bytecode specialization: benchmark', { timeout: 30000 }, () => {
  it('measures load+compose time with bytecode facts', () => {
    Store.clear();
    const path = require('path');
    const mde = require('../../lib/engine/index');

    const evmPath = path.join(__dirname, '../../calculus/ill/programs/evm.ill');

    // ~40 byte contract: enough to measure
    const hex = '6080604052348015600f57600080fd5b5060' +
                '40805190602001604051809103902060005500';
    // Warm up (without bytecode)
    mde.load(evmPath, { cache: false });

    // Measure load with bytecode specialization
    Store.clear();
    const t0 = performance.now();
    const bc2 = loadBytecode(hex);
    const ef2 = bc2.facts.get('arr_get').filter((_, i) => bc2.entryPoints.has(i));
    const ff2 = new Map([['arr_get', ef2]]);
    const calc = mde.load(evmPath, {
      cache: false,
      extraGrade0Facts: ff2,
      scopeGuard: bytecodeArrGetGuard,
    });
    const dt = performance.now() - t0;

    const entryCount = bc2.entryPoints.size;
    const totalFacts = bc2.facts.get('arr_get').length;
    const arrGetRules = calc.forwardRules.filter(r => r.name.includes('arr_get/'));
    console.log(
      `  Bytecode: ${hex.length / 2} bytes, ${totalFacts} arr_get facts, ` +
      `${entryCount} entry points, ${ef2.length} filtered facts`
    );
    console.log(
      `  Result: ${calc.forwardRules.length} total rules, ` +
      `${arrGetRules.length} arr_get-specialized, ${dt.toFixed(1)}ms`
    );

    assert.ok(calc.forwardRules.length > 0, 'should have rules');
    assert.ok(arrGetRules.length > 0, 'should have arr_get-specialized rules');
    assert.ok(dt < 10000, `load+compose should complete in < 10s, got ${dt.toFixed(0)}ms`);
  });
});
