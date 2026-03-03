/**
 * Tests for EVM memory model (write-log with McCarthy axiom traversal)
 */

const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const backward = require('../../lib/engine/prove');
const { explore } = require('../../lib/engine/symexec');
const { getAllLeaves, countNodes } = require('../../lib/engine/tree-utils');
const Store = require('../../lib/kernel/store');
const { apply: subApply } = require('../../lib/kernel/substitute');
const { intToBin, binToInt } = require('../../lib/engine/ffi/convert');
const memory = require('../../lib/engine/ffi/memory');

// ============================================================================
// FFI Unit Tests
// ============================================================================

describe('Memory FFI', () => {
  beforeEach(() => Store.clear());

  describe('mem_expand', () => {
    it('zero-length access does not expand', () => {
      const old = intToBin(32n);
      const off = intToBin(100n);
      const len = intToBin(0n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_expand([old, off, len, out]);
      assert(r.success);
      // Should return oldSize unchanged
      assert.strictEqual(r.theta[0][1], old);
    });

    it('expands to 32-byte boundary', () => {
      const old = intToBin(0n);
      const off = intToBin(0n);
      const len = intToBin(32n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_expand([old, off, len, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 32n);
    });

    it('rounds up to next 32-byte boundary', () => {
      const old = intToBin(0n);
      const off = intToBin(0n);
      const len = intToBin(1n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_expand([old, off, len, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 32n);
    });

    it('preserves existing size if larger', () => {
      const old = intToBin(128n);
      const off = intToBin(0n);
      const len = intToBin(32n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_expand([old, off, len, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 128n);
    });

    it('handles offset + length spanning boundary', () => {
      const old = intToBin(0n);
      const off = intToBin(16n);
      const len = intToBin(32n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_expand([old, off, len, out]);
      assert(r.success);
      // ceil((16 + 32) / 32) * 32 = ceil(48/32) * 32 = 2 * 32 = 64
      assert.strictEqual(binToInt(r.theta[0][1]), 64n);
    });
  });

  describe('no_overlap', () => {
    it('disjoint ranges succeed', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(32n), intToBin(32n), intToBin(32n)
      ]);
      assert(r.success);
    });

    it('overlapping ranges fail', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(32n), intToBin(16n), intToBin(32n)
      ]);
      assert(!r.success);
    });

    it('adjacent ranges succeed (left boundary)', () => {
      const r = memory.no_overlap([
        intToBin(32n), intToBin(32n), intToBin(0n), intToBin(32n)
      ]);
      assert(r.success);
    });

    it('contained range fails', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(64n), intToBin(16n), intToBin(16n)
      ]);
      assert(!r.success);
    });

    it('write8 disjoint from 32-byte read', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(32n), intToBin(32n), intToBin(1n)
      ]);
      assert(r.success);
    });

    it('write8 inside 32-byte read fails', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(32n), intToBin(15n), intToBin(1n)
      ]);
      assert(!r.success);
    });
  });

});

// ============================================================================
// Backward Clause Tests (theory without FFI)
// ============================================================================

describe('Memory Backward Clauses', { timeout: 30000 }, () => {
  let calc;

  before(async () => {
    Store.clear();
    calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/evm.ill')
    );
  });

  /** Prove a goal via backward clauses only, return result */
  async function proveNoFFI(expr, opts = {}) {
    const goal = await mde.parseExpr(expr);
    return backward.prove(goal, calc.clauses, calc.types, {
      useFFI: false,
      maxDepth: opts.maxDepth || 100,
      trace: opts.trace || false,
    });
  }

  /** Prove and extract freevar V from result */
  async function proveAndExtract(expr, varName = 'V') {
    const goal = await mde.parseExpr(expr);
    const vHash = Store.put('freevar', ['_' + varName]);
    const result = backward.prove(goal, calc.clauses, calc.types, {
      useFFI: false,
      maxDepth: 100,
    });
    if (!result.success) return null;
    const resolved = subApply(vHash, result.theta);
    return resolved;
  }

  describe('no_overlap', () => {
    it('disjoint: [0,32) vs [32,64) — left boundary', async () => {
      const r = await proveNoFFI('no_overlap 0 32 32 32');
      assert(r.success, 'Disjoint ranges should succeed');
    });

    it('disjoint: [32,64) vs [0,32) — right boundary', async () => {
      const r = await proveNoFFI('no_overlap 32 32 0 32');
      assert(r.success, 'Disjoint ranges (reversed) should succeed');
    });

    it('overlapping: [0,32) vs [16,48) — fails', async () => {
      const r = await proveNoFFI('no_overlap 0 32 16 32');
      assert(!r.success, 'Overlapping ranges should fail');
    });

    it('disjoint: write8 [32,33) vs read [0,32)', async () => {
      const r = await proveNoFFI('no_overlap 0 32 32 1');
      assert(r.success, 'write8 disjoint from 32-byte read should succeed');
    });
  });

  describe('mem_read', () => {
    it('exact hit: write at 0, read at 0 → V = 42', async () => {
      const v = await proveAndExtract('mem_read (write 0 42 empty_mem) 0 V');
      assert(v !== null, 'Should prove mem_read');
      assert.strictEqual(binToInt(v), 42n);
    });

    it('miss + zero: write at 32, read at 0 → V = 0', async () => {
      const v = await proveAndExtract('mem_read (write 32 42 empty_mem) 0 V');
      assert(v !== null, 'Should prove mem_read with miss + zero');
      assert.strictEqual(binToInt(v), 0n);
    });

    it('most recent wins: write 0xBB over 0xAA at same offset', async () => {
      const v = await proveAndExtract(
        'mem_read (write 0 0xBB (write 0 0xAA empty_mem)) 0 V'
      );
      assert(v !== null, 'Should prove mem_read');
      assert.strictEqual(binToInt(v), 0xBBn);
    });

    it('chain traversal: 3 writes, read at 64', async () => {
      const v = await proveAndExtract(
        'mem_read (write 64 0xCC (write 32 0xBB (write 0 0xAA empty_mem))) 64 V'
      );
      assert(v !== null, 'Should prove mem_read with chain traversal');
      assert.strictEqual(binToInt(v), 0xCCn);
    });

    it('overlap → stuck: write at 16, read at 0 — fails (sound)', async () => {
      const r = await proveNoFFI(
        'mem_read (write 16 0xBB (write 0 0xAA empty_mem)) 0 V'
      );
      assert(!r.success, 'Partial overlap should fail (no clause matches)');
    });

    it('write8 miss: write8 at 32, read at 0 → V = 0', async () => {
      const v = await proveAndExtract(
        'mem_read (write8 32 0xAB empty_mem) 0 V'
      );
      assert(v !== null, 'Should prove mem_read with write8 miss');
      assert.strictEqual(binToInt(v), 0n);
    });

    it('empty memory: read at 0 → V = 0', async () => {
      const v = await proveAndExtract('mem_read empty_mem 0 V');
      assert(v !== null, 'Should prove mem_read from empty memory');
      assert.strictEqual(binToInt(v), 0n);
    });
  });
});

// ============================================================================
// Integration Tests via EVM Execution
// ============================================================================

describe('EVM Memory Integration', { timeout: 30000 }, () => {
  /**
   * Build a minimal EVM initial state with bytecode.
   * bytecodeMap: { address: opcode, ... }  e.g. { 0: 0x60, 1: 0x42, 2: 0x60, 3: 0x00, 4: 0x52 }
   * Returns { linear, persistent } state.
   */
  async function buildEvmState(bytecodeMap) {
    const linear = {};
    const persistent = {};

    linear[await mde.parseExpr('pc 0')] = 1;
    linear[await mde.parseExpr('stack ae')] = 1;
    linear[await mde.parseExpr('gas 0')] = 1;
    linear[await mde.parseExpr('mem empty_mem')] = 1;
    linear[await mde.parseExpr('memsize 0')] = 1;

    // Build bytecode arrlit from byte map, then apply bytesToSemantic
    const maxAddr = Math.max(...Object.keys(bytecodeMap).map(Number));
    const elems = [];
    for (let i = 0; i <= maxAddr; i++) {
      const v = bytecodeMap[i] || bytecodeMap[String(i)];
      elems.push(v ? v : '0x00');
    }
    const bcExpr = `bytecode [${elems.join(', ')}]`;
    const bcHash = await mde.parseExpr(bcExpr);
    // Apply bytesToSemantic to convert byte-level → semantic
    const tmpState = mde.bytesToSemantic({ linear: { [bcHash]: 1 }, persistent: {} });
    Object.assign(linear, tmpState.linear);

    // Standard persistent facts for inc
    for (let i = 0; i < 20; i++) {
      persistent[await mde.parseExpr(`inc ${i} ${i + 1}`)] = true;
    }

    return { linear, persistent };
  }

  describe('MSTORE + MLOAD', () => {
    it('MSTORE then MLOAD at same offset returns correct value', async () => {
      Store.clear();
      calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill')
      );

      // Bytecode: PUSH1 0x42, PUSH1 0x00, MSTORE, PUSH1 0x00, MLOAD
      // 0: PUSH1(0x60), 1: 0x42, 2: PUSH1(0x60), 3: 0x00, 4: MSTORE(0x52), 5: PUSH1(0x60), 6: 0x00, 7: MLOAD(0x51)
      const state = await buildEvmState({
        0: '0x60', 1: '0x42',
        2: '0x60', 3: '0x00',
        4: '0x52',
        5: '0x60', 6: '0x00',
        7: '0x51'
      });

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 100,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      const leaves = getAllLeaves(tree);
      assert(leaves.length > 0, 'Should have leaves');

      // Check that at least one leaf has stack with value 0x42
      let found = false;
      const stackTagId = Store.TAG['stack'];
      for (const leaf of leaves) {
        if (leaf.state && stackTagId !== undefined) {
          const grp = leaf.state.linear.group(stackTagId);
          for (let i = 0; i < grp.length; i++) {
            const arrHash = Store.child(grp[i], 0);
            const elems = Store.getArrayElements(arrHash);
            if (elems) {
              for (let j = 0; j < elems.length; j++) {
                if (binToInt(elems[j]) === 0x42n) found = true;
              }
            }
          }
        }
      }
      assert(found, 'MLOAD should return 0x42 on the stack');
    });

    it('MLOAD at unwritten offset returns 0', async () => {
      Store.clear();
      calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill')
      );

      // Bytecode: PUSH1 0x42, PUSH1 0x00, MSTORE, PUSH1 0x20, MLOAD
      // Write at offset 0, read at offset 0x20 (32)
      const state = await buildEvmState({
        0: '0x60', 1: '0x42',
        2: '0x60', 3: '0x00',
        4: '0x52',
        5: '0x60', 6: '0x20',
        7: '0x51'
      });

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 100,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      const leaves = getAllLeaves(tree);
      assert(leaves.length > 0, 'Should have leaves');

      // Check that at least one leaf has stack with value 0
      let found = false;
      const stackTagId2 = Store.TAG['stack'];
      for (const leaf of leaves) {
        if (leaf.state && stackTagId2 !== undefined) {
          const grp = leaf.state.linear.group(stackTagId2);
          for (let i = 0; i < grp.length; i++) {
            const arrHash = Store.child(grp[i], 0);
            const elems = Store.getArrayElements(arrHash);
            if (elems) {
              for (let j = 0; j < elems.length; j++) {
                if (binToInt(elems[j]) === 0n) found = true;
              }
            }
          }
        }
      }
      assert(found, 'MLOAD at unwritten offset should return 0');
    });

    it('two MSTOREs then MLOAD returns latest value', async () => {
      Store.clear();
      calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill')
      );

      // Bytecode: PUSH1 0xAA, PUSH1 0x00, MSTORE, PUSH1 0xBB, PUSH1 0x00, MSTORE, PUSH1 0x00, MLOAD
      const state = await buildEvmState({
        0: '0x60', 1: '0xAA',
        2: '0x60', 3: '0x00',
        4: '0x52',
        5: '0x60', 6: '0xBB',
        7: '0x60', 8: '0x00',
        9: '0x52',
        10: '0x60', 11: '0x00',
        12: '0x51'
      });

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 200,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      const leaves = getAllLeaves(tree);
      assert(leaves.length > 0, 'Should have leaves');

      // The latest write (0xBB) should win
      let foundBB = false;
      const stackTagId3 = Store.TAG['stack'];
      for (const leaf of leaves) {
        if (leaf.state && stackTagId3 !== undefined) {
          const grp = leaf.state.linear.group(stackTagId3);
          for (let i = 0; i < grp.length; i++) {
            const arrHash = Store.child(grp[i], 0);
            const elems = Store.getArrayElements(arrHash);
            if (elems) {
              for (let j = 0; j < elems.length; j++) {
                if (binToInt(elems[j]) === 0xBBn) foundBB = true;
              }
            }
          }
        }
      }
      assert(foundBB, 'MLOAD should return 0xBB (latest write)');
    });
  });

  describe('MSIZE tracking', () => {
    it('MSTORE at offset 0 expands to 32', async () => {
      Store.clear();
      calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill')
      );

      // PUSH1 0x42, PUSH1 0x00, MSTORE, MSIZE
      const state = await buildEvmState({
        0: '0x60', 1: '0x42',
        2: '0x60', 3: '0x00',
        4: '0x52',
        5: '0x59'
      });

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 50,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      const leaves = getAllLeaves(tree);
      assert(leaves.length > 0, 'Should have leaves');

      // MSIZE should push 32 on stack
      let found = false;
      const stackTagId4 = Store.TAG['stack'];
      for (const leaf of leaves) {
        if (leaf.state && stackTagId4 !== undefined) {
          const grp = leaf.state.linear.group(stackTagId4);
          for (let i = 0; i < grp.length; i++) {
            const arrHash = Store.child(grp[i], 0);
            const elems = Store.getArrayElements(arrHash);
            if (elems) {
              for (let j = 0; j < elems.length; j++) {
                if (binToInt(elems[j]) === 32n) found = true;
              }
            }
          }
        }
      }
      assert(found, 'MSIZE should return 32 after MSTORE at offset 0');
    });
  });

  describe('Abstract CALL', () => {
    it('CALL produces nondeterministic fork with memory preserved', async () => {
      Store.clear();
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/evm.ill')
      );

      // PUSH1 0x42, PUSH1 0x00, MSTORE → non-empty memory
      // Then 7 × PUSH1 + CALL
      const state = await buildEvmState({
        0: '0x60', 1: '0x42',    // PUSH1 0x42 (value)
        2: '0x60', 3: '0x00',    // PUSH1 0x00 (offset)
        4: '0x52',                // MSTORE → mem (write 0 0x42 empty_mem)
        5: '0x60', 6: '0x00',    // PUSH1 OutSize
        7: '0x60', 8: '0x00',    // PUSH1 OutOffset
        9: '0x60', 10: '0x00',   // PUSH1 InSize
        11: '0x60', 12: '0x00',  // PUSH1 InOffset
        13: '0x60', 14: '0x00',  // PUSH1 Value
        15: '0x60', 16: '0x01',  // PUSH1 To
        17: '0x60', 18: '0xFF',  // PUSH1 Gas
        19: '0xf1'                // CALL
      });

      const tree = explore(state, calc.forwardRules, {
        maxDepth: 100,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      const leaves = getAllLeaves(tree);
      assert.strictEqual(leaves.length, 2,
        'CALL should produce 2 leaves (success + failure)');

      // Check stack values: one branch has 1 (success), one has 0 (failure)
      const stackValues = [];
      const stackTagId5 = Store.TAG['stack'];
      for (const leaf of leaves) {
        if (leaf.state && stackTagId5 !== undefined) {
          const grp = leaf.state.linear.group(stackTagId5);
          for (let i = 0; i < grp.length; i++) {
            const arrHash = Store.child(grp[i], 0);
            const elems = Store.getArrayElements(arrHash);
            if (elems) {
              for (let j = 0; j < elems.length; j++) {
                stackValues.push(binToInt(elems[j]));
              }
            }
          }
        }
      }
      assert(stackValues.includes(1n), 'One branch should have stack 1 (success)');
      assert(stackValues.includes(0n), 'One branch should have stack 0 (failure)');

      // Verify memory preserved in both leaves (non-empty: write 0 0x42 empty_mem)
      const memTagId = Store.TAG['mem'];
      for (const leaf of leaves) {
        let memHash = null;
        if (memTagId !== undefined) {
          const grp = leaf.state.linear.group(memTagId);
          for (let i = 0; i < grp.length; i++) {
            memHash = Store.child(grp[i], 0);
          }
        }
        assert(memHash !== null, 'Memory should be preserved after CALL');
        assert.strictEqual(Store.tag(memHash), 'write',
          'Memory should contain a write node (not empty_mem)');
      }
    });
  });

  describe('Multisig no-call symexec baseline', () => {
    let tree, allLeaves;

    it('explores to exact expected tree shape', async () => {
      Store.clear();
      const msCalc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig_nocall.ill')
      );

      const state = mde.decomposeQuery(msCalc.queries.get('symex'));

      tree = explore(state, msCalc.forwardRules, {
        maxDepth: 200,
        calc: { clauses: msCalc.clauses, types: msCalc.types }
      });

      allLeaves = getAllLeaves(tree);

      // Exact tree shape — catches accidental pruning or explosion
      assert.strictEqual(countNodes(tree), 56, 'Expected 56 nodes');
      assert.strictEqual(allLeaves.length, 1, 'Expected 1 leaf');
    });

    it('has exactly 1 STOP leaf (successful termination)', async () => {
      const { classifyLeaf } = require('../../lib/engine/show');
      const stopLeaves = allLeaves.filter(l => classifyLeaf(l.state) === 'STOP');
      assert.strictEqual(stopLeaves.length, 1,
        `Expected 1 STOP leaf, got ${stopLeaves.length}`);
    });

    it('has no bound or cycle leaves (full exploration)', async () => {
      const bound = allLeaves.filter(l => l.type === 'bound');
      const cycle = allLeaves.filter(l => l.type === 'cycle');
      assert.strictEqual(bound.length, 0, 'No depth-bound leaves');
      assert.strictEqual(cycle.length, 0, 'No cycle leaves');
    });
  });

  describe('Multisig with abstract CALL', () => {
    let tree, allLeaves;

    it('explores past CALL with no stuck call facts', async () => {
      Store.clear();
      const msCalc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig.ill')
      );

      const state = mde.decomposeQuery(msCalc.queries.get('symex'));

      tree = explore(state, msCalc.forwardRules, {
        maxDepth: 300,
        calc: { clauses: msCalc.clauses, types: msCalc.types }
      });

      allLeaves = getAllLeaves(tree);

      // No leaves should have stuck `call(...)` facts
      const callTagId = Store.TAG['call'];
      for (const leaf of allLeaves) {
        if (leaf.state && callTagId !== undefined) {
          assert.strictEqual(leaf.state.linear.groupLen(callTagId), 0,
            'No leaf should have stuck call(...) facts');
        }
      }
    });

    it('has exact expected tree shape', async () => {
      // Abstract CALL forks into success + failure, doubling paths after CALL
      assert.strictEqual(countNodes(tree), 84, 'Expected 84 nodes');
      assert.strictEqual(allLeaves.length, 2, 'Expected 2 leaves');
    });

    it('has exactly 1 STOP leaf', async () => {
      const { classifyLeaf } = require('../../lib/engine/show');
      const stopLeaves = allLeaves.filter(l => classifyLeaf(l.state) === 'STOP');
      assert.strictEqual(stopLeaves.length, 1,
        `Expected 1 STOP leaf, got ${stopLeaves.length}`);
    });

    it('has no bound or cycle leaves', async () => {
      const bound = allLeaves.filter(l => l.type === 'bound');
      const cycle = allLeaves.filter(l => l.type === 'cycle');
      assert.strictEqual(bound.length, 0, 'No depth-bound leaves');
      assert.strictEqual(cycle.length, 0, 'No cycle leaves');
    });
  });
});
