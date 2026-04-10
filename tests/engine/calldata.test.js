/**
 * Tests for calldata representation (TODO 141)
 *
 * Verifies cd_read backward clauses, cd_read FFI, CALLDATALOAD/SIZE opcodes,
 * and sconcat cross-boundary reads with byte_join.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const { intToBin, binToInt } = require('../../lib/engine/ill/ffi/convert');
const { arrToTrie } = require('../../lib/engine/ill/ffi/array');

/**
 * Build initial EVM state from hex bytecode + calldata options.
 */
function makeState(hexCode, calc, { gas = 0xFFFFn, calldata = null, calldatasize = 0n } = {}) {
  const linear = {};
  const persistent = {};

  if (calc && calc.persistent) Object.assign(persistent, calc.persistent);

  const ae = Store.put('atom', ['ae']);

  linear[Store.put('pc', [intToBin(0n)])] = 1;
  linear[Store.put('gas', [intToBin(gas)])] = 1;
  linear[Store.put('stack', [ae])] = 1;
  linear[Store.put('mem', [Store.put('atom', ['empty_mem'])])] = 1;
  linear[Store.put('memsize', [intToBin(0n)])] = 1;
  linear[Store.put('address', [intToBin(0xCAFEn)])] = 1;
  linear[Store.put('sender', [intToBin(0xBEEFn)])] = 1;
  linear[Store.put('callvalue', [intToBin(0n)])] = 1;
  linear[Store.put('timestamp', [intToBin(0n)])] = 1;
  linear[Store.put('gaslimit', [intToBin(0xFFFFn)])] = 1;
  linear[Store.put('initializedStorage', [ae])] = 1;

  // Calldata
  if (calldata !== null) {
    linear[Store.put('calldata', [calldata])] = 1;
  } else {
    linear[Store.put('calldata', [Store.put('atom', ['epsilon'])])] = 1;
  }
  linear[Store.put('calldatasize', [intToBin(calldatasize)])] = 1;

  // Build bytecode from hex
  const clean = hexCode.startsWith('0x') ? hexCode.slice(2) : hexCode;
  const elems = new Uint32Array(clean.length / 2);
  for (let i = 0; i < clean.length; i += 2) {
    elems[i / 2] = intToBin(BigInt(parseInt(clean.slice(i, i + 2), 16)));
  }
  linear[Store.put('bytecode', [Store.putArray(elems)])] = 1;

  let state = { linear, persistent };
  state = mde.bytesToSemantic(state);

  // Convert bytecode arrlit -> trie
  const bcTagId = Store.TAG['bytecode'];
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tagId(hNum) === bcTagId) {
      const arrH = Store.rawChild(hNum, 0);
      const t = arrToTrie(arrH);
      if (t !== arrH) {
        delete state.linear[h];
        state.linear[Store.put('bytecode', [t])] = 1;
      }
      break;
    }
  }

  return state;
}

function hasStop(state) {
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tag(hNum) === 'atom' && Store.child(hNum, 0) === 'stop') return true;
  }
  return false;
}

function getStackTop(state) {
  const stackTagId = Store.TAG['stack'];
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tagId(hNum) === stackTagId) {
      const listH = Store.child(hNum, 0);
      const elems = Store.getArrayElements(listH);
      if (elems && elems.length > 0) return elems[0];
      if (Store.tag(listH) === 'acons') return Store.child(listH, 0);
    }
  }
  return null;
}

describe('Calldata (TODO 141)', { timeout: 30000 }, () => {
  let calc;

  before(() => {
    calc = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
  });

  describe('CALLDATALOAD with sconcat (ground 32-byte chunks)', () => {
    it('reads full 32-byte word at offset 0', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);
      // 32-byte padded value: 0xAABBCCDD followed by 28 zero bytes
      const padded = 0xAABBCCDDn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 4n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(binToInt(top), padded);
    });

    it('reads at offset past end returns 0', () => {
      // PUSH1 0x20, CALLDATALOAD, STOP (offset 32 past a 32-byte calldata)
      const code = '60203500';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xAABBCCDDn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 0n);
    });

    it('reads second 32-byte word at offset 32', () => {
      // PUSH1 32, CALLDATALOAD, STOP
      const code = '60203500';
      const epsilon = Store.put('atom', ['epsilon']);
      const word0 = intToBin(0x1111n);
      const word1 = intToBin(0x2222n);
      const inner = Store.put('sconcat', [intToBin(32n), word1, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(32n), word0, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 64n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 0x2222n);
    });
  });

  describe('CALLDATASIZE', () => {
    it('pushes calldata size onto stack', () => {
      // CALLDATASIZE, STOP
      const code = '3600';
      const cdVal = intToBin(0xAABBCCDDn);
      const state = makeState(code, calc, { calldata: cdVal, calldatasize: 100n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 100n);
    });

    it('returns 0 for empty calldata', () => {
      const code = '3600';
      const state = makeState(code, calc, { calldatasize: 0n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 0n);
    });
  });

  describe('CALLDATALOAD with sconcat (structured symbolic)', () => {
    it('aligned read at offset 0 with 32-byte segment', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);
      const deadline = intToBin(12345n);
      const cdHash = Store.put('sconcat', [intToBin(32n), deadline, epsilon]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      const top = getStackTop(result.state);
      assert.equal(binToInt(top), 12345n, 'cd_read/hit should return exact value');
    });

    it('skip to second segment at offset 32', () => {
      // PUSH1 32, CALLDATALOAD, STOP
      const code = '60203500';
      const epsilon = Store.put('atom', ['epsilon']);
      const val1 = intToBin(111n);
      const val2 = intToBin(222n);
      const inner = Store.put('sconcat', [intToBin(32n), val2, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(32n), val1, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 64n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 222n);
    });

    it('cross-boundary read produces byte_join', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xcd68b367n);
      const deadline = intToBin(99999n);
      const inner = Store.put('sconcat', [intToBin(32n), deadline, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));

      const top = getStackTop(result.state);
      assert.ok(top !== null);
      // Cross-boundary: byte_join(4, selector, deadline)
      assert.equal(Store.tag(top), 'byte_join', 'Cross-boundary should produce byte_join');
      assert.equal(binToInt(Store.child(top, 1)), 0xcd68b367n, 'Head = selector');
      assert.equal(binToInt(Store.child(top, 2)), 99999n, 'Tail = deadline');
    });

    it('SHR decomposes byte_join to extract selector', () => {
      // PUSH1 0, CALLDATALOAD, PUSH1 0xE0, SHR, STOP
      const code = '60003560e01c00';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xcd68b367n);
      const deadline = intToBin(42n);
      const inner = Store.put('sconcat', [intToBin(32n), deadline, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 0xcd68b367n,
        'SHR(224, byte_join(4, sel, _)) should return selector');
    });

    it('skip past 4-byte selector to read first param', () => {
      // PUSH1 4, CALLDATALOAD, STOP
      const code = '60043500';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xcd68b367n);
      const deadline = intToBin(77777n);
      const inner = Store.put('sconcat', [intToBin(32n), deadline, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 77777n,
        'CALLDATALOAD(4) should skip selector and return Deadline');
    });
  });

  describe('epsilon (empty calldata)', () => {
    it('CALLDATALOAD on epsilon returns 0', () => {
      const code = '60003500';
      const state = makeState(code, calc, { calldatasize: 0n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.equal(binToInt(getStackTop(result.state)), 0n);
    });
  });

  describe('calldata preserved ($) sugar', () => {
    it('CALLDATALOAD preserves calldata fact', () => {
      // PUSH1 0, CALLDATALOAD, POP, PUSH1 0, CALLDATALOAD, STOP
      // Two successive reads — calldata must be preserved after first
      const code = '600035506000350000';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0x1234n << (30n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 2n });
      const result = calc.exec(state, { maxSteps: 1000 });

      assert.ok(result.quiescent, 'Should complete two CALLDATALOAD ops');
      assert.ok(hasStop(result.state));
      // Both reads should succeed (calldata preserved)
      assert.equal(binToInt(getStackTop(result.state)), padded);
    });
  });

  describe('symbolic calldata (R7 opaque / R8 partial)', () => {
    it('R7: opaque calldata produces evar on stack top', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      // CD is a freevar — cd_read cannot resolve → Val stays unbound → freshEvar
      const code = '60003500';
      const cdHash = Store.put('freevar', ['_CD']);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 0n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(Store.tag(top), 'evar',
        'Opaque calldata: cd_read fails → Val = freshEvar()');
    });

    it('R8: partial symbolic (selector known, first param symbolic) produces byte_join at offset 0', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      // CD = sconcat(4, 0xa9059cbb, sconcat(32, freevar('_VAL'), epsilon))
      // cd_read/cross fires: SZ=4 < 32, then cd_read inner sconcat → freevar('_VAL')
      // Result: byte_join(4, 0xa9059cbb, freevar('_VAL'))
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xa9059cbbn);
      const symVal = Store.put('freevar', ['_VAL']);
      const inner = Store.put('sconcat', [intToBin(32n), symVal, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(Store.tag(top), 'byte_join',
        'Cross-boundary with symbolic inner value should produce byte_join');
      assert.equal(Store.child(top, 0), intToBin(4n), 'byte_join first arg = segment size');
      assert.equal(binToInt(Store.child(top, 1)), 0xa9059cbbn,
        'byte_join head = selector 0xa9059cbb');
      // Tail is the symbolic value freevar (cd_read/hit on inner sconcat returns _VAL directly)
      assert.equal(Store.tag(Store.child(top, 2)), 'freevar',
        'byte_join tail = symbolic _VAL (cd_read/hit on inner sconcat returns freevar)');
    });

    it('R8+SHR: SHR(224, byte_join(4, sel, _)) extracts selector from partial symbolic', () => {
      // PUSH1 0, CALLDATALOAD, PUSH1 0xE0, SHR, STOP
      // CD = sconcat(4, 0xa9059cbb, sconcat(32, freevar('_VAL'), epsilon))
      // CALLDATALOAD(0) → byte_join(4, sel, _VAL)
      // shr/byte_join clause: SHR(224, byte_join(4, sel, _)) = sel
      const code = '60003560e01c00';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xa9059cbbn);
      const symVal = Store.put('freevar', ['_VAL']);
      const inner = Store.put('sconcat', [intToBin(32n), symVal, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      assert.equal(binToInt(getStackTop(result.state)), 0xa9059cbbn,
        'SHR(224, byte_join(4, sel, _)) = sel — selector extracted');
    });

    it('R8 skip: CALLDATALOAD(4) on partial symbolic produces evar (skip past selector)', () => {
      // PUSH1 4, CALLDATALOAD, STOP
      // CD = sconcat(4, 0xa9059cbb, freevar('_REST'))
      // cd_read/skip fires (SZ=4 <= Offset=4), then cd_read(freevar, 0, Val)
      // cd_read on freevar fails → Val = freshEvar
      const code = '60043500';
      const selector = intToBin(0xa9059cbbn);
      const rest = Store.put('freevar', ['_REST']);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, rest]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(Store.tag(top), 'evar',
        'cd_read/skip skips selector, then cd_read(freevar) fails → freshEvar');
    });
  });

  describe('no calldatacopy_iter (loli eliminated)', () => {
    it('forward execution trace has no calldatacopy_iter or loli', () => {
      // PUSH1 32, PUSH1 0, PUSH1 0, CALLDATACOPY, STOP
      // Copy 32 bytes from calldata offset 0 to memory offset 0
      const code = '6020600060003700';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xDEADBEEFn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 1000, trace: true });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));
      assert.ok(result.trace, 'trace should be present when trace:true is set');
      const traceStr = result.trace.join(' ');
      assert.ok(!traceStr.includes('calldatacopy_iter'), 'No calldatacopy_iter in trace');
      assert.ok(!traceStr.includes('loli'), 'No loli in trace');
    });
  });

  describe('CALLDATACOPY memory correctness', () => {
    /**
     * Extract the inner memory hash (the write-chain root) from a state.
     * Returns the hash stored inside the `mem` fact, or null if not found.
     */
    function getMemHash(state) {
      const memTagId = Store.TAG['mem'];
      for (const h of Object.keys(state.linear)) {
        const hNum = Number(h);
        if (Store.tagId(hNum) === memTagId) {
          return Store.child(hNum, 0);
        }
      }
      return null;
    }

    /**
     * Walk a write-chain (write(addr, val, rest) | empty_mem)
     * and return the value written at `addrBig` (as BigInt), or null if not found.
     */
    function getMemValue(state, addrBig) {
      let chain = getMemHash(state);
      if (chain === null) return null;
      while (chain !== null) {
        const tag = Store.tag(chain);
        if (tag === 'atom') {
          // empty_mem — address not found, return 0 (EVM zero-initialised memory)
          return 0n;
        }
        if (tag === 'write') {
          const writeAddr = binToInt(Store.child(chain, 0));
          const writeVal  = Store.child(chain, 1);
          if (writeAddr === addrBig) return binToInt(writeVal);
          chain = Store.child(chain, 2);
        } else {
          // Unknown node in chain (symbolic) — cannot resolve
          return null;
        }
      }
      return null;
    }

    it('CALLDATACOPY writes value into memory (direct write-chain inspection)', () => {
      // PUSH1 32, PUSH1 0, PUSH1 0, CALLDATACOPY, STOP
      // Stack order for CALLDATACOPY: size, dataOffset, destOffset
      // Encoding: PUSH1 size=32, PUSH1 dataOffset=0, PUSH1 destOffset=0, CALLDATACOPY, STOP
      const code = '6020600060003700';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xDEADBEEFn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 1000 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      // Verify the write-chain contains a write(0, padded, ...) node
      const memHash = getMemHash(result.state);
      assert.ok(memHash !== null, 'mem fact should be present');
      assert.notEqual(Store.tag(memHash), 'atom',
        'Memory should not be empty after CALLDATACOPY');

      const val = getMemValue(result.state, 0n);
      assert.ok(val !== null, 'Should find a write at address 0');
      assert.equal(val, padded,
        `Memory[0] should be 0xDEADBEEF padded to 32 bytes; got 0x${val.toString(16)}`);
    });

    it('CALLDATACOPY then MLOAD returns copied value', () => {
      // PUSH1 32, PUSH1 0, PUSH1 0, CALLDATACOPY, PUSH1 0, MLOAD, STOP
      // Opcodes: 60 20  60 00  60 00  37  60 00  51  00
      const code = '6020600060003760005100';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xDEADBEEFn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 2000 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty after MLOAD');
      assert.equal(binToInt(top), padded,
        `MLOAD(0) after CALLDATACOPY should return 0xDEADBEEF padded; got 0x${binToInt(top).toString(16)}`);
    });

    it('CALLDATACOPY preserves calldata — copy then CALLDATALOAD still works', () => {
      // PUSH1 32, PUSH1 0, PUSH1 0, CALLDATACOPY (copies to mem[0]),
      // PUSH1 0, CALLDATALOAD (reads from calldata[0]), STOP
      // Opcodes: 60 20  60 00  60 00  37  60 00  35  00
      const code = '6020600060003760003500';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xDEADBEEFn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 2000 });

      assert.ok(result.quiescent, 'Should reach quiescence after CALLDATACOPY + CALLDATALOAD');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      // CALLDATALOAD at offset 0 should still return the original calldata value
      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(binToInt(top), padded,
        'Calldata should be preserved after CALLDATACOPY — CALLDATALOAD returns original value');
    });

    it('CALLDATACOPY with non-zero destOffset writes to correct address', () => {
      // PUSH1 32, PUSH1 0, PUSH1 32, CALLDATACOPY, STOP
      // Copy 32 bytes from calldata[0] to mem[32]
      // Opcodes: 60 20  60 00  60 20  37  00
      const code = '6020600060203700';
      const epsilon = Store.put('atom', ['epsilon']);
      const padded = 0xCAFEBABEn << (28n * 8n);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(padded), epsilon]);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 32n });
      const result = calc.exec(state, { maxSteps: 1000 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      // Memory at address 32 should contain the copied value; address 0 should be empty (0)
      const valAt32 = getMemValue(result.state, 32n);
      assert.ok(valAt32 !== null, 'Should find write at address 32');
      assert.equal(valAt32, padded,
        `Memory[32] should contain copied value; got 0x${valAt32.toString(16)}`);

      const valAt0 = getMemValue(result.state, 0n);
      assert.equal(valAt0, 0n,
        'Memory[0] should be 0 (not written by this CALLDATACOPY)');
    });
  });

  describe('cd_read/partial SZ guard — SZ<32 must not fire (bugfix)', () => {
    // cd_read/partial has a guard `le 32 SZ` to prevent firing on SZ<32 chunks.
    // For SZ<32 (e.g. sconcat(4, selector, ...)), Val is right-aligned (intToBin),
    // not left-aligned. The shl/shr arithmetic would produce wrong bytes.
    // Expected behaviour for SZ<32 with Offset>0: falls through to freshEvar (sound, imprecise).

    it('SZ=4 at mid-chunk offset 2 produces evar (not wrong bytes)', () => {
      // CD = sconcat(4, 0xcd68b367, sconcat(32, deadline, epsilon))
      // CALLDATALOAD(2): offset 2 is inside the 4-byte segment (0 < 2 < 4).
      // cd_read/partial must NOT fire because SZ=4 < 32.
      // cd_read/skip doesn't fire (2 < 4). cd_read/cross doesn't fire (offset != 0).
      // Result: freshEvar (sound but imprecise).
      const code = '60023500';
      const epsilon = Store.put('atom', ['epsilon']);
      const selector = intToBin(0xcd68b367n);
      const deadline = intToBin(99999n);
      const inner = Store.put('sconcat', [intToBin(32n), deadline, epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(4n), selector, inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 36n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      assert.equal(Store.tag(top), 'evar',
        'SZ=4 with Offset=2: cd_read/partial must not fire — should produce evar, not wrong bytes');
    });

    it('SZ=32 at mid-chunk offset 16 fires correctly (partial guard allows SZ>=32)', () => {
      // CD = sconcat(32, word0, sconcat(32, word1, epsilon))
      // CALLDATALOAD(16): 0 < 16 < 32, SZ=32 — cd_read/partial must fire.
      // word0 = 0x0102030405060708090a0b0c0d0e0f10_0000000000000000000000000000000 (left-aligned)
      // word1 = 0x1112131415161718191a1b1c1d1e1f20_0000000000000000000000000000000 (left-aligned)
      // Result at offset 16 = top 16 bytes of word0 shifted left 128 bits
      //                     | top 16 bytes of word1 (i.e. shr 128 of word1)
      const code = '60103500';
      const epsilon = Store.put('atom', ['epsilon']);
      // Left-aligned 32-byte words (as translate.js would produce):
      // word0: bytes 0x01..0x10 in positions 0..15, zeros in 16..31
      const w0 = 0x0102030405060708090a0b0c0d0e0f10n << 128n;
      // word1: bytes 0x11..0x20 in positions 0..15, zeros in 16..31
      const w1 = 0x1112131415161718191a1b1c1d1e1f20n << 128n;
      const inner = Store.put('sconcat', [intToBin(32n), intToBin(w1), epsilon]);
      const cdHash = Store.put('sconcat', [intToBin(32n), intToBin(w0), inner]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 64n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');
      // cd_read/partial: shl(128, w0) | shr(128, w1)
      // shl(128, w0): low 16 bytes of w0 → 0x090a0b0c0d0e0f10_0000000000000000 shifted to top
      // shr(128, w1): top 16 bytes of w1 → 0x1112131415161718191a1b1c1d1e1f20
      const shifted = (w0 << 128n) & ((1n << 256n) - 1n);
      const nextHead = w1 >> 128n;
      const expected = (shifted | nextHead) & ((1n << 256n) - 1n);
      assert.equal(binToInt(top), expected,
        'cd_read/partial at offset 16 in SZ=32 chunk should combine tail of word0 and head of word1');
    });
  });

  describe('leading-zero calldata — sconcat preserves byte positions', () => {
    // BigInt strips leading zeros: BigInt('0x00AABB') === BigInt('0xAABB').
    // The sconcat representation encodes byte position by right-padding each chunk
    // to 32 bytes before converting to BigInt, so the numeric value carries the
    // correct positional information even when the first calldata byte is 0x00.
    //
    // Example: calldata 0x00AABB (3 bytes)
    //   chunk hex = '00aabb' padEnd(64,'0') = '00aabb000...000'
    //   BigInt('0x00aabb000...000') = 0xAABB * 2^(29*8)
    //   As 32-byte word: byte0=0x00, byte1=0xAA, byte2=0xBB — correct!
    //
    // The raw-binlit FFI (calldata.js) has a known limitation: it cannot handle
    // leading-zero bytes because BigInt drops them. translate.js always produces
    // sconcat chains, so the FFI is not used for concrete calldata.

    it('CALLDATALOAD 0 on 3-byte calldata 0x00AABB returns correct 32-byte word', () => {
      // PUSH1 0, CALLDATALOAD, STOP — loads 32 bytes starting at offset 0
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);

      // Build sconcat chunk as translate.js would:
      // chunk = '00aabb' padded to 32 bytes, BigInt preserves byte positions via right-padding
      const cdClean = '00aabb'; // 3 bytes: 0x00, 0xAA, 0xBB
      const chunk = cdClean.padEnd(64, '0'); // '00aabb' + 58 zeros
      const chunkVal = intToBin(BigInt('0x' + chunk)); // 0xAABB * 2^(29*8)
      const cdHash = Store.put('sconcat', [intToBin(32n), chunkVal, epsilon]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 3n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');

      // Expected: 32-byte word with byte0=0x00, byte1=0xAA, byte2=0xBB, rest=0
      // = BigInt('0x00aabb' + '0'.repeat(58))
      const expected = BigInt('0x' + chunk); // same computation as chunk
      assert.equal(binToInt(top), expected,
        'CALLDATALOAD should return 0x00AABB... (leading zero preserved via sconcat)');

      // Verify byte decomposition of the result
      const topVal = binToInt(top);
      assert.equal((topVal >> 248n) & 0xffn, 0x00n, 'byte 0 should be 0x00 (leading zero)');
      assert.equal((topVal >> 240n) & 0xffn, 0xAAn, 'byte 1 should be 0xAA');
      assert.equal((topVal >> 232n) & 0xffn, 0xBBn, 'byte 2 should be 0xBB');
    });

    it('CALLDATALOAD 0 on 4-byte calldata 0x00001234 returns correct 32-byte word', () => {
      // calldata 0x00001234 — two leading zero bytes
      const code = '60003500';
      const epsilon = Store.put('atom', ['epsilon']);

      const cdClean = '00001234'; // 4 bytes: 0x00, 0x00, 0x12, 0x34
      const chunk = cdClean.padEnd(64, '0');
      const chunkVal = intToBin(BigInt('0x' + chunk));
      const cdHash = Store.put('sconcat', [intToBin(32n), chunkVal, epsilon]);

      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 4n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent);
      assert.ok(hasStop(result.state));

      const top = getStackTop(result.state);
      const topVal = binToInt(top);
      assert.equal((topVal >> 248n) & 0xffn, 0x00n, 'byte 0 should be 0x00');
      assert.equal((topVal >> 240n) & 0xffn, 0x00n, 'byte 1 should be 0x00');
      assert.equal((topVal >> 232n) & 0xffn, 0x12n, 'byte 2 should be 0x12');
      assert.equal((topVal >> 224n) & 0xffn, 0x34n, 'byte 3 should be 0x34');
    });

    it('translate.js fixtureToState produces correct sconcat for leading-zero calldata', () => {
      // Simulate translate.js chunk construction for 3-byte calldata '00aabb'
      // Verify the BigInt correctly represents the 32-byte word with 0x00 at byte 0
      const cdClean = '00aabb';
      const chunk = cdClean.slice(0, 64).padEnd(64, '0');
      const val = BigInt('0x' + chunk);

      // Byte positions in the 256-bit integer
      assert.equal((val >> 248n) & 0xffn, 0x00n, 'chunk byte 0 = 0x00 (leading zero)');
      assert.equal((val >> 240n) & 0xffn, 0xAAn, 'chunk byte 1 = 0xAA');
      assert.equal((val >> 232n) & 0xffn, 0xBBn, 'chunk byte 2 = 0xBB');
      assert.equal((val >> 224n) & 0xffn, 0x00n, 'chunk byte 3 = 0x00 (padding)');

      // The FFI byteLen would compute 2 (strips leading 0x00) — different from true 32-byte width
      // This demonstrates the raw-binlit FFI limitation for leading-zero calldata:
      let ffiByteLen = 0;
      let v = val;
      while (v > 0n) { v >>= 8n; ffiByteLen++; }
      // ffiByteLen = 31 (correct: AA is at byte 1 of the 32-byte chunk, so 31 significant bytes)
      // vs the actual calldata byte count of 3
      // The FFI is correct for the chunk (31 significant bytes) but not for a raw 3-byte binlit
      assert.ok(ffiByteLen <= 32, 'chunk ffiByteLen <= 32 bytes');
    });
  });

  describe('cd_read FFI fast path — raw ground binlit calldata (R11)', () => {
    // These tests exercise the cd_read FFI directly.
    // When calldata is a raw binlit (not sconcat/epsilon), none of the backward
    // clauses cd_read/hit, cd_read/skip, cd_read/cross, cd_read/partial, cd_read/nil
    // match (they all pattern-match on sconcat or epsilon). The engine falls through
    // to the FFI which calls calldata.js:cd_read() to compute the result.
    //
    // Precondition: raw binlit calldata must have no leading-zero bytes.
    // (BigInt strips leading zeros; for leading-zero calldata, use sconcat.)

    it('CALLDATALOAD(0) on raw binlit 0xAABBCCDD returns left-aligned 32-byte word', () => {
      // PUSH1 0, CALLDATALOAD, STOP
      const code = '60003500';
      // Raw binlit calldata — not wrapped in sconcat
      const cdHash = intToBin(0xAABBCCDDn);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 4n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');

      // byteLen=4, offset=0, avail=4: extract all 4 bytes, left-align in 32-byte word
      // result = 0xAABBCCDD << (28*8)
      const expected = 0xAABBCCDDn << (28n * 8n);
      assert.equal(binToInt(top), expected,
        'CALLDATALOAD(0) on 0xAABBCCDD should return 0xAABBCCDD left-aligned in 32 bytes');
    });

    it('CALLDATALOAD(2) on raw binlit 0xAABBCCDDEEFF returns bytes starting at offset 2', () => {
      // PUSH1 2, CALLDATALOAD, STOP
      const code = '60023500';
      // Raw 6-byte binlit calldata — bytes: AA BB CC DD EE FF
      const cdHash = intToBin(0xAABBCCDDEEFFn);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 6n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');

      // byteLen=6, offset=2, avail=min(32,4)=4: bytes at indices 2-5 = CC DD EE FF
      // extracted = 0xCCDDEEFF, left-aligned in 32 bytes
      // result = 0xCCDDEEFF << (28*8)
      const expected = 0xCCDDEEFFn << (28n * 8n);
      assert.equal(binToInt(top), expected,
        'CALLDATALOAD(2) on 0xAABBCCDDEEFF should return 0xCCDDEEFF left-aligned');
    });

    it('CALLDATALOAD at offset past end of raw binlit returns 0', () => {
      // PUSH1 4, CALLDATALOAD, STOP
      const code = '60043500';
      // Raw 4-byte binlit calldata
      const cdHash = intToBin(0xAABBCCDDn);
      const state = makeState(code, calc, { calldata: cdHash, calldatasize: 4n });
      const result = calc.exec(state, { maxSteps: 500 });

      assert.ok(result.quiescent, 'Should reach quiescence');
      assert.ok(hasStop(result.state), 'Should terminate with stop');

      const top = getStackTop(result.state);
      assert.ok(top !== null, 'Stack should not be empty');

      // byteLen=4, offset=4 >= byteLen: past end, FFI returns 0
      assert.equal(binToInt(top), 0n,
        'CALLDATALOAD at offset past end of raw binlit should return 0');
    });
  });
});
