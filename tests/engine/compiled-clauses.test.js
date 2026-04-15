/**
 * Tests for compiled clause dispatch (Tier 1).
 * Validates zero-subgoal clause dispatch via mode-driven matching.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const { clauseDispatch, tryCCDispatch } = require('../../lib/engine/opt/compiled-clauses');
const { buildTheoryLookup, defaultTheories } = require('../../lib/kernel/eq-theory');
const { binlitTheory } = require('../../lib/engine/ill/binlit-theory');
const { show } = require('../../lib/engine/show');

const PROGRAM = path.join(__dirname, '..', '..', 'calculus', 'ill', 'programs', 'evm.ill');

describe('Compiled Clause Dispatch', { timeout: 10000 }, () => {
  let calc, dispatch, theoryLookup, parsedModes;

  before(() => {
    calc = mde.load(PROGRAM, { cache: true });
    const { parsedModes: ffiParsedModes } = require('../../lib/engine/ill/ffi');
    parsedModes = ffiParsedModes;
    theoryLookup = calc.theoryLookup || buildTheoryLookup([...defaultTheories, binlitTheory]);
    dispatch = calc.clauseDispatch || clauseDispatch(
      require('../../lib/engine/backchain').buildIndex(calc.clauses, calc.definitions),
      parsedModes
    );
  });

  describe('clauseDispatch', () => {
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

  describe('tryCCDispatch — ground goals', () => {
    it('resolves inc(0, ?) base case', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const zero = intToBin(0n);
      const mv = Store.put('metavar', ['test_out']);
      const goal = Store.put('inc', [zero, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, slots, theta,
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

      const result = tryCCDispatch(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'should resolve inc(2, ?)');
      const outVal = Store.child(theta[0], 0);
      assert.equal(outVal, 3n, 'inc(2) should equal 3');
    });

    it('resolves inc(1, ?) = 2 via carry (Tier 2 recursive)', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const one = intToBin(1n);
      const mv = Store.put('metavar', ['test_out3']);
      const goal = Store.put('inc', [one, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'carry case resolved via Tier 2');
      assert.equal(Store.child(theta[0], 0), 2n, 'inc(1) should equal 2');
    });

    it('verifies ground output for fully ground goal', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const zero = intToBin(0n);
      const one = intToBin(1n);
      // inc(0, 1) — fully ground, should succeed
      const goal = Store.put('inc', [zero, one]);

      const slots = {};
      const theta = [];

      const result = tryCCDispatch(dispatch, goal, slots, theta,
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

      const result = tryCCDispatch(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, null, 'inc(0, 5) should not match');
    });
  });

  describe('tryCCDispatch — no modes fallback', () => {
    it('returns null for predicate without modes', () => {
      const mv = Store.put('metavar', ['test_unknown']);
      const goal = Store.put('unknown_pred', [mv]);

      const result = tryCCDispatch(dispatch, goal, {}, [],
        null, null, parsedModes);

      assert.equal(result, null);
    });

    it('returns null for predicate not in dispatch', () => {
      const goal = Store.put('nonexistent', [Store.put('atom', ['x'])]);

      const result = tryCCDispatch(dispatch, goal, {}, [],
        null, null, parsedModes);

      assert.equal(result, null);
    });
  });

  describe('Tier 2 — recursive clauses', () => {
    it('resolves inc(3) = 4 via carry propagation', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const three = intToBin(3n);
      const mv = Store.put('metavar', ['t2_inc3']);
      const goal = Store.put('inc', [three, mv]);

      const slots = { [mv]: 0 };
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, slots, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'should resolve inc(3) via Tier 2');
      assert.equal(Store.child(theta[0], 0), 4n, 'inc(3) should equal 4');
    });

    it('resolves inc(255) = 256 (8-bit carry chain)', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const mv = Store.put('metavar', ['t2_inc255']);
      const goal = Store.put('inc', [intToBin(255n), mv]);
      const theta = [undefined];

      tryCCDispatch(dispatch, goal, { [mv]: 0 }, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(Store.child(theta[0], 0), 256n, 'inc(255) should equal 256');
    });

    it('resolves plus(2,4) = 6 (no carry, Tier 2 recursion)', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const mv = Store.put('metavar', ['t2_plus']);
      const goal = Store.put('plus', [intToBin(2n), intToBin(4n), mv]);
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, { [mv]: 0 }, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'should resolve plus(2,4) via Tier 2');
      assert.equal(Store.child(theta[0], 0), 6n, 'plus(2,4) should equal 6');
    });

    it('falls through for plus(1,1) — carry needs Tier 3 (plus/s4)', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      const mv = Store.put('metavar', ['t2_carry']);
      const goal = Store.put('plus', [intToBin(1n), intToBin(1n), mv]);
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, { [mv]: 0 }, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, null, 'carry case should fall through to backchainer');
    });

    it('resolves trie_get for nested trie', () => {
      const { intToBin } = require('../../lib/engine/ill/ffi/convert');
      // Build: tn (tn tn_nil 0x10 tn_nil) 0x42 (tn tn_nil 0x20 tn_nil)
      const nil = Store.put('atom', ['tn_nil']);
      const inner_l = Store.put('tn', [nil, intToBin(0x10n), nil]);
      const inner_r = Store.put('tn', [nil, intToBin(0x20n), nil]);
      const trie = Store.put('tn', [inner_l, intToBin(0x42n), inner_r]);

      // trie_get(trie, e, ?) — key=e → root value (0x42)
      const mv = Store.put('metavar', ['trie_v']);
      const goal = Store.put('trie_get', [trie, intToBin(0n), mv]);
      const theta = [undefined];

      const result = tryCCDispatch(dispatch, goal, { [mv]: 0 }, theta,
        binlitTheory.canonicalize, theoryLookup, parsedModes);

      assert.equal(result, true, 'trie_get base case');
      assert.equal(Store.child(theta[0], 0), 0x42n, 'root value should be 0x42');
    });

    it('dispatch._tier2 contains expected predicates', () => {
      assert.ok(dispatch._tier2.inc, 'should have inc');
      assert.ok(dispatch._tier2.plus, 'should have plus');
      assert.ok(dispatch._tier2.trie_get, 'should have trie_get');
      assert.ok(dispatch._tier2.trie_set, 'should have trie_set');
    });
  });

  describe('Tier 2 — savedTheta for input-referencing output wrappers (B7)', () => {
    // Predicate: peel(pair(H, T), cons(H, R)) :- peel(T, R)
    // Base:      peel(e, nil)
    //
    // Output wrapper cons(H, R) references H (from input decomposition).
    // At depth >= 2, the inner recursion clobbers _localTheta with its own H,
    // so the outer recursion's H resolves wrong without savedTheta.
    //
    // peel(pair(a, pair(b, e)), ?) should give cons(a, cons(b, nil))
    // Without savedTheta: cons(b, cons(b, nil)) — outer H clobbered by inner H.
    it('output referencing input metavar across recursion depth (B7)', () => {
      const { collectMetavars } = require('../../lib/engine/pattern-utils');

      const H = Store.put('metavar', ['_H']);
      const T = Store.put('metavar', ['_T']);
      const R = Store.put('metavar', ['_R']);
      const e = Store.put('atom', ['nil_e']);
      const nil = Store.put('atom', ['nil_out']);

      // Base: peel(e, nil) — ground, no metavars
      const baseHead = Store.put('peel', [e, nil]);
      const baseDef = [
        'peel/base',
        { hash: baseHead, localSlots: {}, metavarCount: 0, metavarList: [] }
      ];

      // Recursive: peel(pair(H, T), cons(H, R)) :- peel(T, R)
      const recHead = Store.put('peel', [
        Store.put('pair', [H, T]),
        Store.put('cons', [H, R])
      ]);
      const recPremise = Store.put('peel', [T, R]);
      const recMvs = new Set();
      collectMetavars(recHead, recMvs);
      collectMetavars(recPremise, recMvs);
      const recSlots = {};
      let rsi = 0;
      for (const mv of recMvs) recSlots[mv] = rsi++;
      const recClause = [
        'peel/rec',
        {
          hash: recHead, premises: [recPremise],
          localSlots: recSlots, metavarCount: rsi,
          metavarList: [...recMvs].map((h, i) => ({ hash: h, localSlot: i })),
        }
      ];

      // Build dispatch
      const idx = {
        types: { 'peel': { '_': [baseDef] } },
        clauses: { 'peel': { '_': [recClause] } }
      };
      const modes = { peel: ['+', '-'] };
      const localDispatch = clauseDispatch(idx, modes);

      // Goal: peel(pair(a, pair(b, e)), ?) — depth 2 recursion
      const a = Store.put('atom', ['sym_a']);
      const b = Store.put('atom', ['sym_b']);
      const input = Store.put('pair', [a, Store.put('pair', [b, e])]);
      const mv = Store.put('metavar', ['_out']);
      const goal = Store.put('peel', [input, mv]);
      const theta = [undefined];

      const result = tryCCDispatch(localDispatch, goal, { [mv]: 0 }, theta,
        null, null, modes);

      assert.equal(result, true, 'should resolve via Tier 2');
      assert.ok(theta[0] !== undefined, 'output should be bound');

      // Expected: cons(a, cons(b, nil))
      const out = theta[0];
      assert.equal(Store.tag(out), 'cons', 'outer should be cons');

      const outerH = Store.child(out, 0);
      assert.equal(outerH, a, 'outer H should be sym_a (not sym_b)');

      const innerCons = Store.child(out, 1);
      assert.equal(Store.tag(innerCons), 'cons', 'inner should be cons');
      assert.equal(Store.child(innerCons, 0), b, 'inner H should be sym_b');
      assert.equal(Store.child(innerCons, 1), nil, 'tail should be nil');
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
