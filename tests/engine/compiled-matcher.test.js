/**
 * Tests for compiled pattern matching (Opt_G).
 *
 * Verifies compilePM, compilePS, compilePSAll
 * produce identical results to the generic matching pipeline.
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const forward = require('../../lib/engine/forward');
const {
  compilePM, execPM,
} = require('../../lib/engine/compile');
const { tryMatch } = require('../../lib/engine/match');
const { execPS, compilePS } = require('../../lib/engine/opt/ffi');
const illFfi = require('../../lib/engine/ill/ffi');
const illFfiContext = {
  meta: illFfi.defaultMeta,
  parsedModes: illFfi.parsedModes,
  get: illFfi.get,
  isFFIGround: illFfi.convert.isGround,
};
const illMatchOpts = {
  ffiMeta: illFfi.defaultMeta,
  ffiGet: illFfi.get,
  ffiParsedModes: illFfi.parsedModes,
  ffiIsGround: illFfi.convert.isGround,
};
const { countNodes, getAllLeaves } = require('../../lib/engine/tree-utils');

// ─── compilePM ─────────────────────────────────────────────

describe('compilePM', () => {
  beforeEach(() => { Store.clear(); });

  it('matches flat pred(X, Y) binding both vars', () => {
    Store.registerTag('pred');
    const xVar = Store.put('metavar', ['X']);
    const yVar = Store.put('metavar', ['Y']);
    const pattern = Store.put('pred', [xVar, yVar]);
    const slots = { [xVar]: 0, [yVar]: 1 };

    const instructions = compilePM(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const valB = Store.put('atom', ['b']);
    const fact = Store.put('pred', [valA, valB]);
    const theta = new Array(2);

    assert(execPM(instructions, fact, theta), 'should match');
    assert.strictEqual(theta[0], valA, 'X bound to a');
    assert.strictEqual(theta[1], valB, 'Y bound to b');
  });

  it('checks ground child (pred(X, ground))', () => {
    Store.registerTag('pred');
    const xVar = Store.put('metavar', ['X']);
    const ground = Store.put('atom', ['c1']);
    const pattern = Store.put('pred', [xVar, ground]);
    const slots = { [xVar]: 0 };

    const instructions = compilePM(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const factOk = Store.put('pred', [valA, ground]);
    const factBad = Store.put('pred', [valA, Store.put('atom', ['c2'])]);

    const theta1 = new Array(1);
    assert(execPM(instructions, factOk, theta1), 'should match with correct ground');
    assert.strictEqual(theta1[0], valA);

    const theta2 = new Array(1);
    assert(!execPM(instructions, factBad, theta2), 'should not match wrong ground');
  });

  it('matches depth-1 compound pred(s(X))', () => {
    Store.registerTag('pred');
    Store.registerTag('s');
    const xVar = Store.put('metavar', ['X']);
    const sX = Store.put('s', [xVar]);
    const pattern = Store.put('pred', [sX]);
    const slots = { [xVar]: 0 };

    const instructions = compilePM(pattern, slots);

    const inner = Store.put('atom', ['e']);
    const sInner = Store.put('s', [inner]);
    const fact = Store.put('pred', [sInner]);

    const theta = new Array(1);
    assert(execPM(instructions, fact, theta), 'should match s(e)');
    assert.strictEqual(theta[0], inner, 'X bound to e');
  });

  it('matches depth-2 compound pred(s(s(X)))', () => {
    Store.registerTag('pred');
    Store.registerTag('s');
    const xVar = Store.put('metavar', ['X']);
    const ssX = Store.put('s', [Store.put('s', [xVar])]);
    const pattern = Store.put('pred', [ssX]);
    const slots = { [xVar]: 0 };

    const instructions = compilePM(pattern, slots);

    const inner = Store.put('atom', ['e']);
    const ssInner = Store.put('s', [Store.put('s', [inner])]);
    const fact = Store.put('pred', [ssInner]);

    const theta = new Array(1);
    assert(execPM(instructions, fact, theta), 'should match s(s(e))');
    assert.strictEqual(theta[0], inner);

    // depth-1 should not match depth-2 pattern
    const sInner = Store.put('s', [inner]);
    const factShallow = Store.put('pred', [sInner]);
    const theta2 = new Array(1);
    assert(!execPM(instructions, factShallow, theta2), 'depth-1 should not match depth-2 pattern');
  });

  it('enforces metavar consistency (shared var)', () => {
    Store.registerTag('pred');
    const xVar = Store.put('metavar', ['X']);
    const pattern = Store.put('pred', [xVar, xVar]);
    const slots = { [xVar]: 0 };

    const instructions = compilePM(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const valB = Store.put('atom', ['b']);
    const factSame = Store.put('pred', [valA, valA]);
    const factDiff = Store.put('pred', [valA, valB]);

    const theta1 = new Array(1);
    assert(execPM(instructions, factSame, theta1), 'should match when both children equal');

    const theta2 = new Array(1);
    assert(!execPM(instructions, factDiff, theta2), 'should not match when children differ');
  });

  it('rejects wrong tag', () => {
    Store.registerTag('pred');
    Store.registerTag('other');
    const xVar = Store.put('metavar', ['X']);
    const pattern = Store.put('pred', [xVar]);
    const slots = { [xVar]: 0 };

    const instructions = compilePM(pattern, slots);

    const val = Store.put('atom', ['a']);
    const wrongTag = Store.put('other', [val]);

    const theta = new Array(1);
    assert(!execPM(instructions, wrongTag, theta), 'should reject wrong tag');
  });
});

// ─── compilePS ───────────────────────────────────────────

describe('compilePS', () => {
  beforeEach(() => { Store.clear(); });

  it('compiles inc FFI fast path', () => {
    Store.registerTag('inc');
    const xVar = Store.put('metavar', ['X']);
    const yVar = Store.put('metavar', ['Y']);
    const pattern = Store.put('inc', [xVar, yVar]);
    const slots = { [xVar]: 0, [yVar]: 1 };

    const spec = compilePS(pattern, slots, null, illFfiContext);
    assert(spec, 'should compile inc');

    const input = Store.put('binlit', [5n]);
    const theta = [input, undefined];
    const result = execPS(spec, theta);

    assert.strictEqual(result, true, 'should succeed');
    // inc(5) = 6
    const expected = Store.put('binlit', [6n]);
    assert.strictEqual(theta[1], expected, 'Y should be 6');
  });

  it('compiles plus FFI fast path', () => {
    Store.registerTag('plus');
    const aVar = Store.put('metavar', ['A']);
    const bVar = Store.put('metavar', ['B']);
    const cVar = Store.put('metavar', ['C']);
    const pattern = Store.put('plus', [aVar, bVar, cVar]);
    const slots = { [aVar]: 0, [bVar]: 1, [cVar]: 2 };

    const spec = compilePS(pattern, slots, null, illFfiContext);
    assert(spec, 'should compile plus');

    const a = Store.put('binlit', [3n]);
    const b = Store.put('binlit', [7n]);
    const theta = [a, b, undefined];
    const result = execPS(spec, theta);

    assert.strictEqual(result, true, 'should succeed');
    const expected = Store.put('binlit', [10n]);
    assert.strictEqual(theta[2], expected, 'C should be 10');
  });

  it('returns false for definitive neq failure', () => {
    Store.registerTag('neq');
    const aVar = Store.put('metavar', ['A']);
    const bVar = Store.put('metavar', ['B']);
    const pattern = Store.put('neq', [aVar, bVar]);
    const slots = { [aVar]: 0, [bVar]: 1 };

    const spec = compilePS(pattern, slots, null, illFfiContext);
    assert(spec, 'should compile neq');

    const val = Store.put('binlit', [5n]);
    const theta = [val, val]; // equal values → definitive failure
    const result = execPS(spec, theta);

    assert.strictEqual(result, false, 'should return false (definitive)');
  });

  it('returns null for unknown predicates (no FFI)', () => {
    Store.registerTag('unknown_pred');
    const xVar = Store.put('metavar', ['X']);
    const pattern = Store.put('unknown_pred', [xVar]);
    const slots = { [xVar]: 0 };

    const step = compilePS(pattern, slots, null, illFfiContext);
    assert.strictEqual(step, null, 'should return null for unknown pred');
  });
});

// ─── structured output patterns (fusion creates these) ──────────────

describe('structured output patterns in FFI', () => {
  beforeEach(() => { Store.clear(); });

  it('arr_set with cons pattern output binds component metavars', () => {
    // Simulates what fusion creates: arr_set(Arr, Idx, Val, [Head | Tail])
    // where the output position is a structured pattern, not a simple metavar
    Store.registerTag('arr_set');
    const arrVar = Store.put('metavar', ['Arr']);
    const idxVar = Store.put('metavar', ['Idx']);
    const valVar = Store.put('metavar', ['Val']);
    const headVar = Store.put('metavar', ['Head']);
    const tailVar = Store.put('metavar', ['Tail']);
    const consPattern = Store.put('acons', [headVar, tailVar]);

    const pattern = Store.put('arr_set', [arrVar, idxVar, valVar, consPattern]);
    const slots = {
      [arrVar]: 0, [idxVar]: 1, [valVar]: 2,
      [headVar]: 3, [tailVar]: 4,
    };

    const spec = compilePS(pattern, slots, null, illFfiContext);
    assert(spec, 'should compile arr_set with structured output');
    assert.strictEqual(spec.argSpecs[3].pattern, consPattern,
      'output position should have pattern argSpec');

    // Build input: arrlit [10, 20, 30]
    const e10 = Store.put('binlit', [10n]);
    const e20 = Store.put('binlit', [20n]);
    const e30 = Store.put('binlit', [30n]);
    const arr = Store.put('arrlit', [new Uint32Array([e10, e20, e30])]);
    const idx = Store.put('binlit', [0n]);
    const newVal = Store.put('binlit', [99n]);

    // arr_set(arr, 0, 99, [Head|Tail]) → new arr = [99, 20, 30]
    // Expect Head = 99, Tail = arrlit([20, 30])
    const theta = [arr, idx, newVal, undefined, undefined];
    const result = execPS(spec, theta);

    assert.strictEqual(result, true, 'should succeed with structured output');
    assert.strictEqual(theta[3], Store.put('binlit', [99n]), 'Head should be 99');
    const expectedTail = Store.put('arrlit', [new Uint32Array([e20, e30])]);
    assert.strictEqual(theta[4], expectedTail, 'Tail should be [20, 30]');
  });

  it('arr_get with cons pattern output binds head and tail', () => {
    Store.registerTag('arr_get');
    const arrVar = Store.put('metavar', ['Arr']);
    const idxVar = Store.put('metavar', ['Idx']);
    const headVar = Store.put('metavar', ['Head']);
    const tailVar = Store.put('metavar', ['Tail']);
    const consPattern = Store.put('acons', [headVar, tailVar]);

    // arr_get mode is + + - : two inputs, one output
    const pattern = Store.put('arr_get', [arrVar, idxVar, consPattern]);
    const slots = {
      [arrVar]: 0, [idxVar]: 1,
      [headVar]: 2, [tailVar]: 3,
    };

    const spec = compilePS(pattern, slots, null, illFfiContext);
    assert(spec, 'should compile arr_get with structured output');

    const e5 = Store.put('binlit', [5n]);
    const e6 = Store.put('binlit', [6n]);
    const e7 = Store.put('binlit', [7n]);
    const arr = Store.put('arrlit', [new Uint32Array([e5, e6, e7])]);
    const idx = Store.put('binlit', [1n]);

    // arr_get(arr, 1) → result at index 1 = 6, rest = [5, 7]
    // But arr_get returns just the element, not a cons!
    // Mode + + - means output is the element. So cons pattern won't match...
    // Actually this tests a FAILURE case: arr_get returns a scalar, not a cons
    const theta = [arr, idx, undefined, undefined];
    const result = execPS(spec, theta);
    // arr_get returns the scalar value 6, not a cons. Unification with acons fails.
    assert.strictEqual(result, false, 'should fail: scalar vs cons pattern');
  });

  it('proveWithFFI handles structured output pattern', () => {
    Store.registerTag('arr_set');
    const { proveWithFFI } = require('../../lib/engine/opt/ffi');

    const arrVar = Store.put('metavar', ['Arr']);
    const idxVar = Store.put('metavar', ['Idx']);
    const valVar = Store.put('metavar', ['Val']);
    const headVar = Store.put('metavar', ['Head']);
    const tailVar = Store.put('metavar', ['Tail']);
    const consPattern = Store.put('acons', [headVar, tailVar]);

    const pattern = Store.put('arr_set', [arrVar, idxVar, valVar, consPattern]);
    const slots = {
      [arrVar]: 0, [idxVar]: 1, [valVar]: 2,
      [headVar]: 3, [tailVar]: 4,
    };

    const e10 = Store.put('binlit', [10n]);
    const e20 = Store.put('binlit', [20n]);
    const arr = Store.put('arrlit', [new Uint32Array([e10, e20])]);
    const idx = Store.put('binlit', [0n]);
    const newVal = Store.put('binlit', [42n]);
    const theta = [arr, idx, newVal, undefined, undefined];

    // Minimal state object with empty persistent facts
    const forward = require('../../lib/engine/forward');
    const state = forward.createState({}, {});

    const result = proveWithFFI([pattern], 0, theta, slots, state, null, null, illMatchOpts);
    assert.strictEqual(result, 1, 'should prove the pattern (index past end)');
    assert.strictEqual(theta[3], Store.put('binlit', [42n]), 'Head bound to 42');
    const expectedTail = Store.put('arrlit', [new Uint32Array([e20])]);
    assert.strictEqual(theta[4], expectedTail, 'Tail bound to [20]');
  });
});

// ─── persistentSteps attachment ──────────────────────────────────────

describe('persistentSteps attachment', { timeout: 10000 }, () => {
  it('attaches persistentSteps for rules with FFI antecedents', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );

    let withSteps = 0, total = 0;
    for (const rule of calc.forwardRules) {
      total++;
      if (rule.persistentSteps) withSteps++;
    }

    assert(withSteps > 0, `Expected some rules with persistentSteps, got ${withSteps}/${total}`);
    // EVM rules: ~40 of 74 have FFI persistent antecedents
    assert(withSteps >= 30, `Expected ≥30 rules with persistentSteps, got ${withSteps}/${total}`);
  });

  it('does not attach for rules without persistent antecedents', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );

    for (const rule of calc.forwardRules) {
      const pats = rule.antecedent.persistent || [];
      if (pats.length === 0) {
        assert(!rule.persistentSteps,
          `Rule ${rule.name} has no persistent antecedents but got persistentSteps`);
      }
    }
  });

  it('persistentSteps length matches persistent antecedent count', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );

    for (const rule of calc.forwardRules) {
      if (!rule.persistentSteps) continue;
      const pats = rule.antecedent.persistent || [];
      assert.strictEqual(rule.persistentSteps.length, pats.length,
        `Rule ${rule.name}: persistentSteps length mismatch`);
    }
  });
});

// ─── Persistent step integration with tryMatch ──────────────────────

describe('persistent step integration', { timeout: 10000 }, () => {
  it('tryMatch produces same results with and without persistentSteps', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const plainState = mde.decomposeQuery(calc.queries.get('symex'));
    const state = forward.createState(plainState.linear, plainState.persistent);

    let testedCount = 0;
    for (const rule of calc.forwardRules) {
      if (!rule.persistentSteps) continue;

      // Run with persistent steps
      const resultWith = tryMatch(rule, state, {
        clauses: calc.clauses, definitions: calc.definitions
      }, { optimizePreserved: true });

      // Temporarily disable persistent steps and run generic path
      const saved = rule.persistentSteps;
      rule.persistentSteps = null;
      const resultWithout = tryMatch(rule, state, {
        clauses: calc.clauses, definitions: calc.definitions
      }, { optimizePreserved: true });
      rule.persistentSteps = saved;

      // Both should agree on match/no-match
      if (resultWith === null) {
        assert.strictEqual(resultWithout, null,
          `Rule ${rule.name}: with steps says no match but without matches`);
      } else {
        assert(resultWithout !== null,
          `Rule ${rule.name}: with steps matches but without says no match`);
        // Same consumed keys
        const withKeys = Object.keys(resultWith.consumed).sort();
        const withoutKeys = Object.keys(resultWithout.consumed).sort();
        assert.deepStrictEqual(withKeys, withoutKeys,
          `Rule ${rule.name}: consumed keys differ`);
      }
      testedCount++;
    }
    assert(testedCount > 20, `Expected ≥20 dual-run tests, got ${testedCount}`);
  });
});

// ─── E2E: persistent steps produce same tree ─────────────────────────

describe('E2E persistent step correctness', { timeout: 30000, concurrency: 1 }, () => {
  it('multisig tree identical with persistent steps (267 nodes)', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    const tree = calc.explore(state, {
      maxDepth: 2000,
      dangerouslyUseFFI: true // Testing compiled matchers, not adversarial soundness
    });

    assert.strictEqual(countNodes(tree), 267, 'Expected 267 nodes');
    assert.strictEqual(getAllLeaves(tree).length, 1, 'Expected 1 leaf');
  });

  it('symbolic multisig (structural memo) unchanged', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    // Full exploration
    const treeFull = calc.explore(state, {
      maxDepth: 500,
      structuralMemo: false,
      dangerouslyUseFFI: true // Testing structural memo, not adversarial soundness
    });
    assert.strictEqual(countNodes(treeFull), 214, 'Full: expected 214 nodes');
    assert.strictEqual(getAllLeaves(treeFull).length, 2, 'Full: expected 2 leaves');

    // With structural memo (same tree — no redundant branches to memo)
    const treeMemo = calc.explore(state, {
      maxDepth: 500,
      structuralMemo: true,
      dangerouslyUseFFI: true
    });
    assert.strictEqual(countNodes(treeMemo), 214, `Memo: expected 214 nodes, got ${countNodes(treeMemo)}`);
  });
});
