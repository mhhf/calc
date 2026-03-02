/**
 * Tests for compiled pattern matching (Opt_G).
 *
 * Verifies compilePatternMatch, compilePersistentStep, compilePersistentSteps
 * produce identical results to the generic matching pipeline.
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const forward = require('../../lib/engine/forward');
const {
  compilePatternMatch, executePatternMatch, compilePersistentStep,
} = require('../../lib/engine/compile');
const { tryMatch, executePersistentStep } = require('../../lib/engine/match');
const { explore } = require('../../lib/engine/symexec');
const { countNodes, getAllLeaves } = require('../../lib/engine/tree-utils');

// ─── compilePatternMatch ─────────────────────────────────────────────

describe('compilePatternMatch', () => {
  beforeEach(() => { Store.clear(); });

  it('matches flat pred(X, Y) binding both vars', () => {
    Store.registerTag('pred');
    const xVar = Store.put('freevar', ['_X']);
    const yVar = Store.put('freevar', ['_Y']);
    const pattern = Store.put('pred', [xVar, yVar]);
    const slots = { [xVar]: 0, [yVar]: 1 };

    const instructions = compilePatternMatch(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const valB = Store.put('atom', ['b']);
    const fact = Store.put('pred', [valA, valB]);
    const theta = new Array(2);

    assert(executePatternMatch(instructions, fact, theta), 'should match');
    assert.strictEqual(theta[0], valA, 'X bound to a');
    assert.strictEqual(theta[1], valB, 'Y bound to b');
  });

  it('checks ground child (pred(X, ground))', () => {
    Store.registerTag('pred');
    const xVar = Store.put('freevar', ['_X']);
    const ground = Store.put('atom', ['c1']);
    const pattern = Store.put('pred', [xVar, ground]);
    const slots = { [xVar]: 0 };

    const instructions = compilePatternMatch(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const factOk = Store.put('pred', [valA, ground]);
    const factBad = Store.put('pred', [valA, Store.put('atom', ['c2'])]);

    const theta1 = new Array(1);
    assert(executePatternMatch(instructions, factOk, theta1), 'should match with correct ground');
    assert.strictEqual(theta1[0], valA);

    const theta2 = new Array(1);
    assert(!executePatternMatch(instructions, factBad, theta2), 'should not match wrong ground');
  });

  it('matches depth-1 compound pred(s(X))', () => {
    Store.registerTag('pred');
    Store.registerTag('s');
    const xVar = Store.put('freevar', ['_X']);
    const sX = Store.put('s', [xVar]);
    const pattern = Store.put('pred', [sX]);
    const slots = { [xVar]: 0 };

    const instructions = compilePatternMatch(pattern, slots);

    const inner = Store.put('atom', ['e']);
    const sInner = Store.put('s', [inner]);
    const fact = Store.put('pred', [sInner]);

    const theta = new Array(1);
    assert(executePatternMatch(instructions, fact, theta), 'should match s(e)');
    assert.strictEqual(theta[0], inner, 'X bound to e');
  });

  it('matches depth-2 compound pred(s(s(X)))', () => {
    Store.registerTag('pred');
    Store.registerTag('s');
    const xVar = Store.put('freevar', ['_X']);
    const ssX = Store.put('s', [Store.put('s', [xVar])]);
    const pattern = Store.put('pred', [ssX]);
    const slots = { [xVar]: 0 };

    const instructions = compilePatternMatch(pattern, slots);

    const inner = Store.put('atom', ['e']);
    const ssInner = Store.put('s', [Store.put('s', [inner])]);
    const fact = Store.put('pred', [ssInner]);

    const theta = new Array(1);
    assert(executePatternMatch(instructions, fact, theta), 'should match s(s(e))');
    assert.strictEqual(theta[0], inner);

    // depth-1 should not match depth-2 pattern
    const sInner = Store.put('s', [inner]);
    const factShallow = Store.put('pred', [sInner]);
    const theta2 = new Array(1);
    assert(!executePatternMatch(instructions, factShallow, theta2), 'depth-1 should not match depth-2 pattern');
  });

  it('enforces metavar consistency (shared var)', () => {
    Store.registerTag('pred');
    const xVar = Store.put('freevar', ['_X']);
    const pattern = Store.put('pred', [xVar, xVar]);
    const slots = { [xVar]: 0 };

    const instructions = compilePatternMatch(pattern, slots);

    const valA = Store.put('atom', ['a']);
    const valB = Store.put('atom', ['b']);
    const factSame = Store.put('pred', [valA, valA]);
    const factDiff = Store.put('pred', [valA, valB]);

    const theta1 = new Array(1);
    assert(executePatternMatch(instructions, factSame, theta1), 'should match when both children equal');

    const theta2 = new Array(1);
    assert(!executePatternMatch(instructions, factDiff, theta2), 'should not match when children differ');
  });

  it('rejects wrong tag', () => {
    Store.registerTag('pred');
    Store.registerTag('other');
    const xVar = Store.put('freevar', ['_X']);
    const pattern = Store.put('pred', [xVar]);
    const slots = { [xVar]: 0 };

    const instructions = compilePatternMatch(pattern, slots);

    const val = Store.put('atom', ['a']);
    const wrongTag = Store.put('other', [val]);

    const theta = new Array(1);
    assert(!executePatternMatch(instructions, wrongTag, theta), 'should reject wrong tag');
  });
});

// ─── compilePersistentStep ───────────────────────────────────────────

describe('compilePersistentStep', () => {
  beforeEach(() => { Store.clear(); });

  it('compiles inc FFI fast path', () => {
    Store.registerTag('inc');
    const xVar = Store.put('freevar', ['_X']);
    const yVar = Store.put('freevar', ['_Y']);
    const pattern = Store.put('inc', [xVar, yVar]);
    const slots = { [xVar]: 0, [yVar]: 1 };

    const spec = compilePersistentStep(pattern, slots);
    assert(spec, 'should compile inc');

    const input = Store.put('binlit', [5n]);
    const theta = [input, undefined];
    const result = executePersistentStep(spec, theta);

    assert.strictEqual(result, true, 'should succeed');
    // inc(5) = 6
    const expected = Store.put('binlit', [6n]);
    assert.strictEqual(theta[1], expected, 'Y should be 6');
  });

  it('compiles plus FFI fast path', () => {
    Store.registerTag('plus');
    const aVar = Store.put('freevar', ['_A']);
    const bVar = Store.put('freevar', ['_B']);
    const cVar = Store.put('freevar', ['_C']);
    const pattern = Store.put('plus', [aVar, bVar, cVar]);
    const slots = { [aVar]: 0, [bVar]: 1, [cVar]: 2 };

    const spec = compilePersistentStep(pattern, slots);
    assert(spec, 'should compile plus');

    const a = Store.put('binlit', [3n]);
    const b = Store.put('binlit', [7n]);
    const theta = [a, b, undefined];
    const result = executePersistentStep(spec, theta);

    assert.strictEqual(result, true, 'should succeed');
    const expected = Store.put('binlit', [10n]);
    assert.strictEqual(theta[2], expected, 'C should be 10');
  });

  it('returns false for definitive neq failure', () => {
    Store.registerTag('neq');
    const aVar = Store.put('freevar', ['_A']);
    const bVar = Store.put('freevar', ['_B']);
    const pattern = Store.put('neq', [aVar, bVar]);
    const slots = { [aVar]: 0, [bVar]: 1 };

    const spec = compilePersistentStep(pattern, slots);
    assert(spec, 'should compile neq');

    const val = Store.put('binlit', [5n]);
    const theta = [val, val]; // equal values → definitive failure
    const result = executePersistentStep(spec, theta);

    assert.strictEqual(result, false, 'should return false (definitive)');
  });

  it('returns null for unknown predicates (no FFI)', () => {
    Store.registerTag('unknown_pred');
    const xVar = Store.put('freevar', ['_X']);
    const pattern = Store.put('unknown_pred', [xVar]);
    const slots = { [xVar]: 0 };

    const step = compilePersistentStep(pattern, slots);
    assert.strictEqual(step, null, 'should return null for unknown pred');
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
        clauses: calc.clauses, types: calc.types
      }, { optimizePreserved: true });

      // Temporarily disable persistent steps and run generic path
      const saved = rule.persistentSteps;
      rule.persistentSteps = null;
      const resultWithout = tryMatch(rule, state, {
        clauses: calc.clauses, types: calc.types
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

describe('E2E persistent step correctness', { timeout: 30000 }, () => {
  it('multisig tree identical with persistent steps (280 nodes)', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    const tree = explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: { clauses: calc.clauses, types: calc.types }
    });

    assert.strictEqual(countNodes(tree), 280, 'Expected 280 nodes');
    assert.strictEqual(getAllLeaves(tree).length, 1, 'Expected 1 leaf');
  });

  it('symbolic multisig (structural memo) unchanged', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    // Full exploration
    const treeFull = explore(state, calc.forwardRules, {
      maxDepth: 500,
      calc: { clauses: calc.clauses, types: calc.types },
      structuralMemo: false
    });
    assert.strictEqual(countNodes(treeFull), 2125, 'Full: expected 2125 nodes');
    assert.strictEqual(getAllLeaves(treeFull).length, 31, 'Full: expected 31 leaves');

    // With structural memo
    const treeMemo = explore(state, calc.forwardRules, {
      maxDepth: 500,
      calc: { clauses: calc.clauses, types: calc.types },
      structuralMemo: true
    });
    assert(countNodes(treeMemo) < 500, `Memo: expected <500 nodes, got ${countNodes(treeMemo)}`);
  });
});
