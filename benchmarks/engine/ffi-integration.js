/**
 * FFI Integration Tests
 *
 * Tests FFI integration with the backward prover using actual MDE files.
 */

const assert = require('assert');
const mde = require('../../lib/engine');
const backward = require('../../lib/engine/prove');
const { binToInt } = require('../../lib/engine/ffi/convert');
const path = require('path');
const Store = require('../../lib/kernel/store');

/**
 * Format binary term fully (no depth limit)
 */
function formatBin(h) {
  const node = Store.get(h);
  if (!node) return '?';
  if (node.tag === 'atom') return node.children[0];
  if (node.tag === 'freevar') return node.children[0];
  if (node.tag === 'app') {
    const [fn, arg] = node.children;
    const argNode = Store.get(arg);
    const argStr = (argNode && (argNode.tag === 'atom' || argNode.tag === 'freevar'))
      ? formatBin(arg)
      : `(${formatBin(arg)})`;
    return `${formatBin(fn)} ${argStr}`;
  }
  return node.tag;
}

describe('FFI Integration', () => {
  // Note: We reload calc for each test suite to avoid Store.clear() issues
  // The Store is shared and clearing it would invalidate cached clause hashes

  describe('plus with FFI', () => {
    let calc;

    before(async () => {
      calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
    });

    it('proves plus 0 0 C', async () => {
      const goal = await mde.parseExpr('plus e e C');

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true });

      assert(result.success, 'Should succeed with FFI');
      // Check result value directly
      const cHash = result.theta.find(([v]) => {
        const node = Store.get(v);
        return node?.tag === 'freevar' && node.children[0] === '_C';
      })?.[1];
      assert(cHash, 'Should have binding for C');
      assert.strictEqual(binToInt(cHash), 0n);
    });

    it('proves plus 3 2 C = 5', async () => {
      const goal = await mde.parseExpr('plus (i (i e)) (o (i e)) C');  // 3 + 2

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true });

      assert(result.success, 'Should succeed with FFI');
      const cHash = result.theta.find(([v]) => {
        const node = Store.get(v);
        return node?.tag === 'freevar' && node.children[0] === '_C';
      })?.[1];
      assert(cHash, 'Should have binding for C');
      assert.strictEqual(binToInt(cHash), 5n);
    });

    it('proves plus 255 1 C = 256', async () => {
      const goal = await mde.parseExpr('plus (i (i (i (i (i (i (i (i e)))))))) (i e) C');

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true });

      assert(result.success, 'Should succeed with FFI');
      const cHash = result.theta.find(([v]) => {
        const node = Store.get(v);
        return node?.tag === 'freevar' && node.children[0] === '_C';
      })?.[1];
      assert(cHash, 'Should have binding for C');
      assert.strictEqual(binToInt(cHash), 256n);
    });

    it('also works without FFI (slower)', async () => {
      const goal = await mde.parseExpr('plus (i (i e)) (o (i e)) C');  // 3 + 2

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: false });

      assert(result.success, 'Should succeed without FFI');

      // Use extractSolution to get the final value of C
      const solution = backward.extractSolution(result.theta, goal);
      // Parse the result - it should be a binary representation of 5
      const resultStr = solution.C;
      assert(resultStr, 'Should have solution for C');
      // 5 = i (o (i e))
      assert(resultStr.includes('i') && resultStr.includes('o'), `Result should be binary: ${resultStr}`);
    });
  });

  describe('inc with FFI', () => {
    let calc;

    before(async () => {
      calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
    });

    it('proves inc 0 C = 1', async () => {
      const goal = await mde.parseExpr('inc e C');

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true });

      assert(result.success);
      const cHash = result.theta.find(([v]) => {
        const node = Store.get(v);
        return node?.tag === 'freevar' && node.children[0] === '_C';
      })?.[1];
      assert.strictEqual(binToInt(cHash), 1n);
    });

    it('proves inc 255 C = 256', async () => {
      const goal = await mde.parseExpr('inc (i (i (i (i (i (i (i (i e)))))))) C');

      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true });

      assert(result.success);
      const cHash = result.theta.find(([v]) => {
        const node = Store.get(v);
        return node?.tag === 'freevar' && node.children[0] === '_C';
      })?.[1];
      assert.strictEqual(binToInt(cHash), 256n);
    });
  });

  describe('FFI fallback', () => {
    let calc;

    before(async () => {
      calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
    });

    it('falls back to clauses when FFI mode does not match', async () => {
      // Test with inc where first arg is metavar - FFI requires ground first arg
      // inc A (i e) means: succ(A) = 1, so A = 0
      // But the clause inc/z2: inc e (i e) should match

      // We'll test by checking that when we have non-ground inputs,
      // FFI is skipped but clauses still work
      const goal = await mde.parseExpr('inc e B');  // succ(0) = B

      const result = backward.prove(goal, calc.clauses, calc.types, {
        useFFI: true,
        trace: true
      });

      assert(result.success, 'Should succeed');

      // Check if FFI was used (it should be since e is ground)
      const usedFFI = result.trace.some(l => l.includes('FFI:'));
      assert(usedFFI, 'FFI should be used when mode matches');

      // Now test with non-ground first arg
      const goal2 = await mde.parseExpr('inc A (i e)');  // succ(A) = 1

      const result2 = backward.prove(goal2, calc.clauses, calc.types, {
        useFFI: true,
        trace: true,
        maxDepth: 5
      });

      // This will fail because clauses don't support inverse mode
      // but FFI should be skipped (no FFI in trace)
      const usedFFI2 = result2.trace.some(l => l.includes('FFI:'));
      assert(!usedFFI2, 'FFI should not be used when mode does not match');
    });
  });
});

describe('FFI Performance', function() {
  this.timeout(30000);

  let calc;
  let backwardIndex;

  before(async () => {
    calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
    backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  });

  it('FFI is faster than clause search for plus 255 1', async () => {
    const iterations = 50;

    const goal = await mde.parseExpr('plus (i (i (i (i (i (i (i (i e)))))))) (i e) C');

    // Warmup
    for (let i = 0; i < 5; i++) {
      backward.prove(goal, calc.clauses, calc.types, { useFFI: true, index: backwardIndex });
    }

    // Benchmark with FFI
    const startFFI = performance.now();
    for (let i = 0; i < iterations; i++) {
      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: true, index: backwardIndex });
      assert(result.success);
    }
    const ffiTime = (performance.now() - startFFI) / iterations;

    // Warmup without FFI
    for (let i = 0; i < 5; i++) {
      backward.prove(goal, calc.clauses, calc.types, { useFFI: false, index: backwardIndex });
    }

    // Benchmark without FFI
    const startNoFFI = performance.now();
    for (let i = 0; i < iterations; i++) {
      const result = backward.prove(goal, calc.clauses, calc.types, { useFFI: false, index: backwardIndex });
      assert(result.success);
    }
    const noFFITime = (performance.now() - startNoFFI) / iterations;

    console.log(`\n  plus 255 1: FFI ${ffiTime.toFixed(3)}ms vs No-FFI ${noFFITime.toFixed(3)}ms (${(noFFITime/ffiTime).toFixed(1)}x speedup)`);

    assert(ffiTime < noFFITime / 5, `FFI should be at least 5x faster (was ${(noFFITime/ffiTime).toFixed(1)}x)`);
  });

  it('FFI scales better with larger numbers', async () => {
    const testCases = [
      { name: 'plus 15 1', expr: 'plus (i (i (i (i e)))) (i e) C' },
      { name: 'plus 255 1', expr: 'plus (i (i (i (i (i (i (i (i e)))))))) (i e) C' },
      { name: 'plus 1023 1', expr: 'plus (i (i (i (i (i (i (i (i (i (i e)))))))))) (i e) C' },
    ];

    const iterations = 30;
    const results = [];

    for (const tc of testCases) {
      const goal = await mde.parseExpr(tc.expr);

      // Benchmark with FFI
      const startFFI = performance.now();
      for (let i = 0; i < iterations; i++) {
        backward.prove(goal, calc.clauses, calc.types, { useFFI: true, index: backwardIndex });
      }
      const ffiTime = (performance.now() - startFFI) / iterations;

      // Benchmark without FFI
      const startNoFFI = performance.now();
      for (let i = 0; i < iterations; i++) {
        backward.prove(goal, calc.clauses, calc.types, { useFFI: false, index: backwardIndex });
      }
      const noFFITime = (performance.now() - startNoFFI) / iterations;

      const speedup = noFFITime / ffiTime;
      results.push({ name: tc.name, ffiTime, noFFITime, speedup });
    }

    console.log('\n  Scaling comparison:');
    for (const r of results) {
      console.log(`    ${r.name}: FFI ${r.ffiTime.toFixed(3)}ms, No-FFI ${r.noFFITime.toFixed(3)}ms (${r.speedup.toFixed(1)}x)`);
    }

    // FFI should have roughly constant time, No-FFI should grow with bit size
    assert(results[2].speedup > results[0].speedup,
      'Speedup should increase with larger numbers');
  });
});
