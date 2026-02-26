/**
 * Tests for EVM memory model (write-log with McCarthy axiom traversal)
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const { explore } = require('../../lib/engine/symexec');
const { getAllLeaves, countNodes } = require('../../lib/engine/tree-utils');
const Store = require('../../lib/kernel/store');
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

    it('adjacent ranges succeed (right boundary)', () => {
      const r = memory.no_overlap([
        intToBin(0n), intToBin(32n), intToBin(32n), intToBin(32n)
      ]);
      assert(r.success);
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

  describe('overlaps', () => {
    it('overlapping ranges succeed', () => {
      const r = memory.overlaps([
        intToBin(0n), intToBin(32n), intToBin(16n), intToBin(32n)
      ]);
      assert(r.success);
    });

    it('disjoint ranges fail', () => {
      const r = memory.overlaps([
        intToBin(0n), intToBin(32n), intToBin(64n), intToBin(32n)
      ]);
      assert(!r.success);
    });
  });

  describe('splice', () => {
    it('no overlap returns base unchanged', () => {
      const base = intToBin(0xAAn);
      const rOff = intToBin(0n);
      const wOff = intToBin(100n);
      const wVal = intToBin(0xBBn);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice([base, rOff, wOff, wVal, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0xAAn);
    });

    it('full overlap replaces all bytes', () => {
      // Same offset → full overlap → writeVal replaces base
      const base = intToBin(0xAAn);
      const off = intToBin(0n);
      const wVal = intToBin(0xBBn);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice([base, off, off, wVal, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0xBBn);
    });

    it('partial overlap splices bytes correctly', () => {
      // Read at 0, write at 16 → overlap [16,32)
      // Base: 0xFF..FF (32 bytes all 0xFF)
      // Write: 0x00..00 (32 bytes all 0x00)
      // Result: bytes [0,16) from base (0xFF), bytes [16,32) from write (0x00)
      const base = (1n << 256n) - 1n;  // all 0xFF bytes
      const wVal = 0n;                  // all 0x00 bytes
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice([intToBin(base), intToBin(0n), intToBin(16n), intToBin(wVal), out]);
      assert(r.success);
      const result = binToInt(r.theta[0][1]);
      // First 16 bytes = 0xFF, last 16 bytes = 0x00
      const expected = ((1n << 128n) - 1n) << 128n;
      assert.strictEqual(result, expected);
    });
  });

  describe('splice_byte', () => {
    it('sets byte at correct position', () => {
      const base = intToBin(0n);  // all zeros
      const rOff = intToBin(0n);
      const addr = intToBin(0n);  // first byte
      const byte_ = intToBin(0xABn);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice_byte([base, rOff, addr, byte_, out]);
      assert(r.success);
      // byte 0 = 0xAB, rest = 0x00
      assert.strictEqual(binToInt(r.theta[0][1]), 0xABn << (31n * 8n));
    });

    it('sets byte at last position', () => {
      const base = intToBin(0n);
      const rOff = intToBin(0n);
      const addr = intToBin(31n);  // last byte
      const byte_ = intToBin(0xFFn);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice_byte([base, rOff, addr, byte_, out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0xFFn);
    });

    it('preserves other bytes', () => {
      const base = intToBin((1n << 256n) - 1n);  // all 0xFF
      const rOff = intToBin(0n);
      const addr = intToBin(16n);  // middle byte
      const byte_ = intToBin(0x00n);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.splice_byte([base, rOff, addr, byte_, out]);
      assert(r.success);
      const result = binToInt(r.theta[0][1]);
      // byte 16 should be 0x00, all others 0xFF
      const shift = BigInt(8 * (31 - 16));
      assert.strictEqual((result >> shift) & 0xFFn, 0x00n);
      // byte 15 still 0xFF
      assert.strictEqual((result >> BigInt(8 * (31 - 15))) & 0xFFn, 0xFFn);
    });
  });

  describe('mem_read_range', () => {
    it('reads from empty memory (all zeros)', () => {
      const emptyMem = Store.put('empty_mem', []);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([emptyMem, intToBin(0n), intToBin(32n), out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0n);
    });

    it('reads exact hit from single write', () => {
      const emptyMem = Store.put('empty_mem', []);
      const value = 0x42n;
      const mem = Store.put('write', [intToBin(0n), intToBin(value), emptyMem]);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([mem, intToBin(0n), intToBin(32n), out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), value);
    });

    it('most recent write wins', () => {
      const emptyMem = Store.put('empty_mem', []);
      const mem1 = Store.put('write', [intToBin(0n), intToBin(0xAAn), emptyMem]);
      const mem2 = Store.put('write', [intToBin(0n), intToBin(0xBBn), mem1]);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([mem2, intToBin(0n), intToBin(32n), out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0xBBn);
    });

    it('reads zero for unwritten offset', () => {
      const emptyMem = Store.put('empty_mem', []);
      const mem = Store.put('write', [intToBin(0n), intToBin(0x42n), emptyMem]);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([mem, intToBin(32n), intToBin(32n), out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0n);
    });

    it('zero-size read returns 0', () => {
      const emptyMem = Store.put('empty_mem', []);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([emptyMem, intToBin(0n), intToBin(0n), out]);
      assert(r.success);
      assert.strictEqual(binToInt(r.theta[0][1]), 0n);
    });

    it('handles write8 nodes', () => {
      const emptyMem = Store.put('empty_mem', []);
      // write8 at offset 0, byte value 0xAB
      const mem = Store.put('write8', [intToBin(0n), intToBin(0xABn), emptyMem]);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([mem, intToBin(0n), intToBin(32n), out]);
      assert(r.success);
      // byte 0 = 0xAB, rest = 0x00
      const expected = 0xABn << (31n * 8n);
      assert.strictEqual(binToInt(r.theta[0][1]), expected);
    });

    it('rejects symbolic offset', () => {
      const emptyMem = Store.put('empty_mem', []);
      const symOff = Store.put('freevar', ['_Sym']);
      const mem = Store.put('write', [symOff, intToBin(0x42n), emptyMem]);
      const out = Store.put('freevar', ['_Out']);
      const r = memory.mem_read_range([mem, intToBin(0n), intToBin(32n), out]);
      assert(!r.success);
      assert.strictEqual(r.reason, 'symbolic_offset');
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
    linear[await mde.parseExpr('sh ee')] = 1;
    linear[await mde.parseExpr('gas 0')] = 1;
    linear[await mde.parseExpr('mem empty_mem')] = 1;
    linear[await mde.parseExpr('memsize 0')] = 1;

    // Code bytes (linear — EVM rules consume and re-produce code facts)
    for (const [addr, opcode] of Object.entries(bytecodeMap)) {
      const h = await mde.parseExpr(`code ${addr} ${opcode}`);
      linear[h] = (linear[h] || 0) + 1;
    }

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
      for (const leaf of leaves) {
        if (leaf.state) {
          for (const h of Object.keys(leaf.state.linear)) {
            const tag = Store.tag(Number(h));
            if (tag === 'stack') {
              const v = Store.child(Number(h), 1);
              if (binToInt(v) === 0x42n) {
                found = true;
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
      for (const leaf of leaves) {
        if (leaf.state) {
          for (const h of Object.keys(leaf.state.linear)) {
            const tag = Store.tag(Number(h));
            if (tag === 'stack') {
              const v = Store.child(Number(h), 1);
              if (binToInt(v) === 0n) {
                found = true;
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
      for (const leaf of leaves) {
        if (leaf.state) {
          for (const h of Object.keys(leaf.state.linear)) {
            const tag = Store.tag(Number(h));
            if (tag === 'stack') {
              const v = Store.child(Number(h), 1);
              if (binToInt(v) === 0xBBn) {
                foundBB = true;
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
      for (const leaf of leaves) {
        if (leaf.state) {
          for (const h of Object.keys(leaf.state.linear)) {
            const tag = Store.tag(Number(h));
            if (tag === 'stack') {
              const v = Store.child(Number(h), 1);
              if (binToInt(v) === 32n) {
                found = true;
              }
            }
          }
        }
      }
      assert(found, 'MSIZE should return 32 after MSTORE at offset 0');
    });
  });

  describe('Multisig symexec baseline', () => {
    let tree, allLeaves;

    it('explores to exact expected tree shape', async () => {
      Store.clear();
      const msCalc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig.ill')
      );

      const state = mde.decomposeQuery(msCalc.queries.get('symex'));

      tree = explore(state, msCalc.forwardRules, {
        maxDepth: 200,
        calc: { clauses: msCalc.clauses, types: msCalc.types }
      });

      allLeaves = getAllLeaves(tree);

      // Exact tree shape — catches accidental pruning or explosion
      assert.strictEqual(countNodes(tree), 210, 'Expected 210 nodes');
      assert.strictEqual(allLeaves.length, 19, 'Expected 19 leaves');
      assert(allLeaves.every(l =>
        l.type === 'leaf' || l.type === 'bound' || l.type === 'cycle'
      ), 'All leaves should be terminal types (no bound/cycle)');
    });

    it('has exactly 4 STOP leaves (successful termination)', async () => {
      const { classifyLeaf } = require('../../lib/engine/show');
      const stopLeaves = allLeaves.filter(l => classifyLeaf(l.state) === 'STOP');
      assert.strictEqual(stopLeaves.length, 4,
        `Expected 4 STOP leaves, got ${stopLeaves.length}`);
    });

    it('has no bound or cycle leaves (full exploration)', async () => {
      const bound = allLeaves.filter(l => l.type === 'bound');
      const cycle = allLeaves.filter(l => l.type === 'cycle');
      assert.strictEqual(bound.length, 0, 'No depth-bound leaves');
      assert.strictEqual(cycle.length, 0, 'No cycle leaves');
    });
  });
});
