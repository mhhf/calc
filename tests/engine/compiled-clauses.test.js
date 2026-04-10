/**
 * Tests for compiled clause dispatch (Tier 1).
 * Validates zero-subgoal clause dispatch via mode-driven matching.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const { buildClauseDispatch, tryCompiledClause } = require('../../lib/engine/opt/compiled-clauses');
const { buildTheoryLookup, defaultTheories } = require('../../lib/kernel/eq-theory');
const { binlitTheory } = require('../../lib/engine/ill/binlit-theory');
const { show } = require('../../lib/engine/show');

const PROGRAM = path.join(__dirname, '..', '..', 'calculus', 'ill', 'programs', 'evm.ill');

describe('Compiled Clause Dispatch', { timeout: 10000 }, () => {
  let calc, dispatch, theoryLookup, parsedModes;

  before(() => {
    calc = mde.load(PROGRAM, { cache: true });
    dispatch = calc.clauseDispatch || buildClauseDispatch(
      require('../../lib/engine/backchain').buildIndex(calc.clauses, calc.definitions)
    );
    theoryLookup = calc.theoryLookup || buildTheoryLookup([...defaultTheories, binlitTheory]);
    const { ffiParsedModes } = require('../../lib/engine/opt/ffi');
    parsedModes = ffiParsedModes;
  });

  describe('buildClauseDispatch', () => {
    it('creates dispatch table with expected predicates', () => {
      assert.ok(dispatch.inc, 'should have inc predicate');
      assert.ok(dispatch.plus, 'should have plus predicate');
    });

    it('indexes by first-argument head', () => {
      // inc(e, i(e)) base case should be under firstArg 'e'
      assert.ok(dispatch.inc['e'], 'inc should have entries under firstArg e');
      assert.ok(dispatch.inc['e'].length > 0);
    });

    it('excludes clauses with subgoals', () => {
      // All entries should be zero-subgoal
      for (const pred in dispatch) {
        for (const fa in dispatch[pred]) {
          const entries = dispatch[pred][fa];
          if (!Array.isArray(entries)) continue;
          for (const compiled of entries) {
            assert.ok(
              !compiled.premises || compiled.premises.length === 0,
              `${pred}/${fa} should only have zero-subgoal clauses`
            );
          }
        }
      }
    });
  });

  describe('tryCompiledClause — ground goals', () => {
    it('resolves inc(0, ?) base case', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const zero = intToBin(0n);
      const mv = Store.put('metavar', ['test_out']);
      const goal = Store.put('inc', [zero, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCompiledClause(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'should resolve inc(0, ?)');
      assert.ok(theta[0] !== undefined, 'output should be bound');
      // inc(0) = 1
      const outVal = Store.child(theta[0], 0);
      assert.equal(outVal, 1n, 'inc(0) should equal 1');
    });

    it('resolves inc(2, ?) = 3 via o(X) → i(X) clause', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const two = intToBin(2n);
      const mv = Store.put('metavar', ['test_out2']);
      const goal = Store.put('inc', [two, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCompiledClause(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'should resolve inc(2, ?)');
      const outVal = Store.child(theta[0], 0);
      assert.equal(outVal, 3n, 'inc(2) should equal 3');
    });

    it('falls through for inc(1, ?) — needs carry (subgoal clause)', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const one = intToBin(1n);
      const mv = Store.put('metavar', ['test_out3']);
      const goal = Store.put('inc', [one, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCompiledClause(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, null, 'carry case should fall through');
      assert.equal(theta[0], undefined, 'output should remain unbound');
    });

    it('verifies ground output for fully ground goal', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const zero = intToBin(0n);
      const one = intToBin(1n);
      // inc(0, 1) — fully ground, should succeed
      const goal = Store.put('inc', [zero, one]);

      const slots = {};
      const theta = [];

      const result = tryCompiledClause(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'inc(0, 1) is provable');
    });

    it('rejects wrong ground output', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const zero = intToBin(0n);
      const five = intToBin(5n);
      // inc(0, 5) — should fail (0+1 ≠ 5)
      const goal = Store.put('inc', [zero, five]);

      const slots = {};
      const theta = [];

      const result = tryCompiledClause(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, null, 'inc(0, 5) should not match');
    });
  });

  describe('tryCompiledClause — no modes fallback', () => {
    it('returns null for predicate without modes', () => {
      const mv = Store.put('metavar', ['test_unknown']);
      const goal = Store.put('unknown_pred', [mv]);

      const result = tryCompiledClause(dispatch, goal, {}, [],
        null, null, parsedModes);

      assert.equal(result, null);
    });

    it('returns null for predicate not in dispatch', () => {
      const goal = Store.put('nonexistent', [Store.put('atom', ['x'])]);

      const result = tryCompiledClause(dispatch, goal, {}, [],
        null, null, parsedModes);

      assert.equal(result, null);
    });
  });

  describe('end-to-end integration', () => {
    it('noFFI exec produces same result with compiled dispatch', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );

      // Track which methods are used
      const methods = new Set();
      const result = calc.exec(initial, {
        onProveSuccess: (goal, method) => methods.add(method),
      });

      assert.ok(result.quiescent, 'should reach quiescence');
      // With compiled dispatch active, 'compiled' should appear
      // (for inc/plus base cases resolved without backchainer)
      assert.ok(
        methods.has('compiled') || methods.has('cache') || methods.has('clause'),
        `expected compiled/cache/clause methods, got: ${[...methods].join(', ')}`
      );
    });

    it('compiled method appears in onProveSuccess for noFFI path', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );

      const successes = [];
      calc.exec(initial, {
        onProveSuccess: (goal, method, info) => successes.push({ goal: show(goal), method, info }),
      });

      const compiledHits = successes.filter(s => s.method === 'compiled');
      assert.ok(compiledHits.length > 0,
        `expected compiled method hits, methods seen: ${[...new Set(successes.map(s => s.method))].join(', ')}`);

      // Info parameter should include ground and hasFfi fields
      for (const s of successes) {
        assert.ok(s.info && typeof s.info.ground === 'boolean',
          'info should have ground field');
        assert.ok(s.info && typeof s.info.hasFfi === 'boolean',
          'info should have hasFfi field');
      }
    });
  });
});
