/**
 * Tests for compile-time SLD resolution (tabling) — resolve-all.js.
 * Phase A of TODO_0160: cross-stage specialization.
 */
const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const { resolve } = require('../../lib/engine/resolve-all');
const { load, parseExpr } = require('../../lib/engine/convert');
const { apply } = require('../../lib/kernel/substitute');
const { unify } = require('../../lib/kernel/unify');
const { binlitTheory } = require('../../lib/engine/ill/binlit-theory');
const { show } = require('../../lib/engine/show');
const illFfi = require('../../lib/engine/ill/ffi');
const { ffiDirect } = require('../../lib/engine/opt/ffi');
const { makeILLBackchainOpts } = require('../../lib/engine/ill/backchain-ill');
const { binToInt, intToBin } = require('../../lib/engine/ill/ffi/convert');
const Store = require('../../lib/kernel/store');

const EVM_PATH = path.join(__dirname, '../../calculus/ill/programs/evm.ill');
let clauses, definitions;

// ILL-specific resolve opts (canonicalize + between handler + FFI + backchain)
const illResolveOpts = {
  canonicalize: binlitTheory.canonicalize,
  ffiDirect,
  ffiContext: {
    meta: illFfi.defaultMeta,
    parsedModes: illFfi.parsedModes,
    get: illFfi.get,
    isFFIGround: illFfi.convert.isGround,
  },
  backchainOpts: makeILLBackchainOpts(),
  nativePredicates: {
    between(currentGoal, rest, thetaMap, depth, searchFn) {
      if (Store.arity(currentGoal) !== 3) return false;
      const x = Store.child(currentGoal, 0);
      const lo = Store.child(currentGoal, 1);
      const hi = Store.child(currentGoal, 2);
      const loInt = binToInt(lo);
      const hiInt = binToInt(hi);
      if (loInt === null || hiInt === null) return false;
      const xInt = binToInt(x);
      if (xInt !== null) {
        if (xInt >= loInt && xInt <= hiInt) searchFn(rest, thetaMap, depth + 1);
      } else {
        for (let n = loInt; n <= hiInt; n++) {
          const valHash = intToBin(n);
          const theta2 = unify(x, valHash);
          if (theta2) {
            const { apply: subApply } = require('../../lib/kernel/substitute');
            const { isGround } = require('../../lib/engine/pattern-utils');
            const newMap = new Map();
            for (const [mv, val] of thetaMap) {
              newMap.set(mv, isGround(val) ? val : subApply(val, theta2));
            }
            for (const [mv, val] of theta2) {
              if (!newMap.has(mv)) newMap.set(mv, binlitTheory.canonicalize ? binlitTheory.canonicalize(val) : val);
            }
            searchFn(rest, newMap, depth + 1);
          }
        }
      }
      return true;
    },
  },
};

function setup() {
  if (!clauses) {
    const result = load([EVM_PATH]);
    clauses = result.clauses;
    definitions = result.definitions;
  }
}

function collectFacts(goals, template) {
  setup();
  const solutions = resolve(goals, clauses, definitions, { ...illResolveOpts, maxSolutions: 10000 });
  const seen = new Map();
  for (const sol of solutions) {
    let fact = apply(template, sol);
    fact = binlitTheory.canonicalize(fact);
    const s = show(fact);
    if (!seen.has(s)) seen.set(s, fact);
  }
  return { solutions, unique: seen };
}

describe('resolve-all: compile-time SLD resolution', () => {

  describe('basic arithmetic', () => {
    it('plus(1, 1, OP) yields exactly 1 solution (OP=2)', () => {
      setup();
      const goal = parseExpr('plus 0x1 0x1 OP');
      const solutions = resolve([goal], clauses, definitions, illResolveOpts);
      assert.equal(solutions.length, 1);
    });

    it('inc(3, R) yields exactly 1 solution (R=4)', () => {
      setup();
      const goal = parseExpr('inc 0x3 R');
      const solutions = resolve([goal], clauses, definitions, illResolveOpts);
      assert.equal(solutions.length, 1);
    });

    it('between(N, 1, 5) yields 5 values', () => {
      setup();
      const goal = parseExpr('between N 0x1 0x5');
      const solutions = resolve([goal], clauses, definitions, illResolveOpts);
      assert.equal(solutions.length, 5);
    });
  });

  describe('is_push tabling', () => {
    it('produces exactly 32 unique facts', () => {
      const g1 = parseExpr('between N 0x1 0x20');
      const g2 = parseExpr('plus 0x5f N OP');
      const template = parseExpr('is_push OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert.equal(unique.size, 32);
    });

    it('produces correct range (0x60–0x7f)', () => {
      const g1 = parseExpr('between N 0x1 0x20');
      const g2 = parseExpr('plus 0x5f N OP');
      const template = parseExpr('is_push OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert(unique.has('is_push(0x60, 0x1)'), 'should have is_push(0x60, 1)');
      assert(unique.has('is_push(0x7f, 0x20)'), 'should have is_push(0x7f, 32)');
    });
  });

  describe('is_dup tabling', () => {
    it('produces exactly 16 unique facts', () => {
      const g1 = parseExpr('between N 0x0 0xf');
      const g2 = parseExpr('plus 0x80 N OP');
      const template = parseExpr('is_dup OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert.equal(unique.size, 16);
    });

    it('produces correct range (0x80–0x8f)', () => {
      const g1 = parseExpr('between N 0x0 0xf');
      const g2 = parseExpr('plus 0x80 N OP');
      const template = parseExpr('is_dup OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert(unique.has('is_dup(0x80, 0x0)'), 'should have is_dup(0x80, 0)');
      assert(unique.has('is_dup(0x8f, 0xf)'), 'should have is_dup(0x8f, 15)');
    });
  });

  describe('is_swap tabling', () => {
    it('produces exactly 16 unique facts', () => {
      const g1 = parseExpr('between N 0x0 0xf');
      const g2 = parseExpr('plus 0x90 N OP');
      const template = parseExpr('is_swap OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert.equal(unique.size, 16);
    });

    it('produces correct range (0x90–0x9f)', () => {
      const g1 = parseExpr('between N 0x0 0xf');
      const g2 = parseExpr('plus 0x90 N OP');
      const template = parseExpr('is_swap OP N');
      const { unique } = collectFacts([g1, g2], template);
      assert(unique.has('is_swap(0x90, 0x0)'), 'should have is_swap(0x90, 0)');
      assert(unique.has('is_swap(0x9f, 0xf)'), 'should have is_swap(0x9f, 15)');
    });
  });

  describe('native between enumeration', () => {
    it('between(N, 1, 5) via native path matches SLD path', () => {
      setup();
      const goal = parseExpr('between N 0x1 0x5');
      const solutions = resolve([goal], clauses, definitions, illResolveOpts);
      assert.equal(solutions.length, 5);
    });

    it('between with ground X acts as membership check', () => {
      setup();
      // 0x3 is in [0x1, 0x5] — should succeed
      const goal1 = parseExpr('between 0x3 0x1 0x5');
      const sol1 = resolve([goal1], clauses, definitions, illResolveOpts);
      assert.equal(sol1.length, 1, 'ground membership should find 1 solution');

      // 0x10 is NOT in [0x1, 0x5] — should fail
      const goal2 = parseExpr('between 0x10 0x1 0x5');
      const sol2 = resolve([goal2], clauses, definitions, illResolveOpts);
      assert.equal(sol2.length, 0, 'out-of-range should find 0 solutions');
    });

    it('between(N, 0, 0) yields exactly 1 value (N=0)', () => {
      setup();
      const goal = parseExpr('between N 0x0 0x0');
      const solutions = resolve([goal], clauses, definitions, illResolveOpts);
      assert.equal(solutions.length, 1);
    });
  });

  describe('performance', () => {
    it('resolves all 64 facts in < 50ms total', () => {
      setup();
      const start = Date.now();

      const push1 = parseExpr('between N 0x1 0x20');
      const push2 = parseExpr('plus 0x5f N OP');
      resolve([push1, push2], clauses, definitions, illResolveOpts);

      const dup1 = parseExpr('between N 0x0 0xf');
      const dup2 = parseExpr('plus 0x80 N OP');
      resolve([dup1, dup2], clauses, definitions, illResolveOpts);

      const swap1 = parseExpr('between N 0x0 0xf');
      const swap2 = parseExpr('plus 0x90 N OP');
      resolve([swap1, swap2], clauses, definitions, illResolveOpts);

      const elapsed = Date.now() - start;
      assert(elapsed < 50, `Tabling took ${elapsed}ms, expected < 50ms`);
    });
  });

  describe('maxSolutions guard', () => {
    it('throws when solutions exceed limit', () => {
      setup();
      // between(N, 0, 100) generates 101 values — over a limit of 50
      const goal = parseExpr('between N 0x0 0x64');
      assert.throws(
        () => resolve([goal], clauses, definitions, { ...illResolveOpts, maxSolutions: 50 }),
        /exceeded max solutions/
      );
    });
  });
});
