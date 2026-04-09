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
      if (result.trace) {
        const traceStr = result.trace.join(' ');
        assert.ok(!traceStr.includes('calldatacopy_iter'), 'No calldatacopy_iter in trace');
        assert.ok(!traceStr.includes('loli'), 'No loli in trace');
      }
    });
  });
});
