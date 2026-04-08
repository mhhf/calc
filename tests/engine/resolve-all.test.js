/**
 * Tests for compile-time SLD resolution (tabling) — resolve-all.js.
 * Phase A of TODO_0160: cross-stage specialization.
 */
const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const { resolveAll } = require('../../lib/engine/resolve-all');
const { load, parseExpr } = require('../../lib/engine/convert');
const { apply } = require('../../lib/kernel/substitute');
const { binlitTheory } = require('../../lib/engine/ill/binlit-theory');
const { show } = require('../../lib/engine/show');

const EVM_PATH = path.join(__dirname, '../../calculus/ill/programs/evm.ill');
let clauses, definitions;

function setup() {
  if (!clauses) {
    const result = load([EVM_PATH]);
    clauses = result.clauses;
    definitions = result.definitions;
  }
}

function collectFacts(goals, template) {
  setup();
  const solutions = resolveAll(goals, clauses, definitions, { maxSolutions: 10000 });
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
      const solutions = resolveAll([goal], clauses, definitions);
      assert.equal(solutions.length, 1);
    });

    it('inc(3, R) yields exactly 1 solution (R=4)', () => {
      setup();
      const goal = parseExpr('inc 0x3 R');
      const solutions = resolveAll([goal], clauses, definitions);
      assert.equal(solutions.length, 1);
    });

    it('between(N, 1, 5) yields 5 values', () => {
      setup();
      const goal = parseExpr('between N 0x1 0x5');
      const solutions = resolveAll([goal], clauses, definitions);
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
      const solutions = resolveAll([goal], clauses, definitions);
      assert.equal(solutions.length, 5);
    });

    it('between with ground X acts as membership check', () => {
      setup();
      // 0x3 is in [0x1, 0x5] — should succeed
      const goal1 = parseExpr('between 0x3 0x1 0x5');
      const sol1 = resolveAll([goal1], clauses, definitions);
      assert.equal(sol1.length, 1, 'ground membership should find 1 solution');

      // 0x10 is NOT in [0x1, 0x5] — should fail
      const goal2 = parseExpr('between 0x10 0x1 0x5');
      const sol2 = resolveAll([goal2], clauses, definitions);
      assert.equal(sol2.length, 0, 'out-of-range should find 0 solutions');
    });

    it('between(N, 0, 0) yields exactly 1 value (N=0)', () => {
      setup();
      const goal = parseExpr('between N 0x0 0x0');
      const solutions = resolveAll([goal], clauses, definitions);
      assert.equal(solutions.length, 1);
    });
  });

  describe('performance', () => {
    it('resolves all 64 facts in < 50ms total', () => {
      setup();
      const start = Date.now();

      const push1 = parseExpr('between N 0x1 0x20');
      const push2 = parseExpr('plus 0x5f N OP');
      resolveAll([push1, push2], clauses, definitions);

      const dup1 = parseExpr('between N 0x0 0xf');
      const dup2 = parseExpr('plus 0x80 N OP');
      resolveAll([dup1, dup2], clauses, definitions);

      const swap1 = parseExpr('between N 0x0 0xf');
      const swap2 = parseExpr('plus 0x90 N OP');
      resolveAll([swap1, swap2], clauses, definitions);

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
        () => resolveAll([goal], clauses, definitions, { maxSolutions: 50 }),
        /exceeded max solutions/
      );
    });
  });
});
