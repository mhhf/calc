/**
 * Tests for SHA3 opcode (exists + backward clauses + keccak256 FFI)
 *
 * Verifies that evm/sha3 produces correct concrete keccak256 hashes
 * when memory is ground, via the sha3_compute FFI.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const { intToBin, binToInt } = require('../../lib/engine/ill/ffi/convert');
const { arrToTrie } = require('../../lib/engine/ill/ffi/array');

/**
 * Build initial EVM state from hex bytecode string.
 */
function makeState(hexCode, calc, { gas = 0xFFFFn } = {}) {
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
  linear[Store.put('calldata', [Store.put('atom', ['epsilon'])])] = 1;
  linear[Store.put('calldatasize', [intToBin(0n)])] = 1;
  linear[Store.put('initializedStorage', [ae])] = 1;

  // Build bytecode from hex
  const clean = hexCode.startsWith('0x') ? hexCode.slice(2) : hexCode;
  const elems = new Uint32Array(clean.length / 2);
  for (let i = 0; i < clean.length; i += 2) {
    elems[i / 2] = intToBin(BigInt(parseInt(clean.slice(i, i + 2), 16)));
  }
  linear[Store.put('bytecode', [Store.putArray(elems)])] = 1;

  let state = { linear, persistent };
  state = mde.bytesToSemantic(state);

  // Convert bytecode arrlit → bit-indexed trie
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

/**
 * Check if the terminal state has a `stop` atom.
 */
function hasStop(state) {
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tag(hNum) === 'atom' && Store.child(hNum, 0) === 'stop') return true;
  }
  return false;
}

/**
 * Extract the stack top from a result state.
 */
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

describe('SHA3 opcode (exists + sha3_compute)', { timeout: 30000 }, () => {
  let calc;

  before(() => {
    calc = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));
  });

  it('SHA3 of 32 bytes produces concrete keccak256', () => {
    // PUSH1 0xFF, PUSH1 0x00, MSTORE, PUSH1 0x20, PUSH1 0x00, SHA3, STOP
    const code = '60ff6000526020600020 00'.replace(/\s/g, '');
    const state = makeState(code, calc);
    const result = calc.exec(state, { maxSteps: 500 });

    assert.ok(result.quiescent, 'Should reach quiescence');
    assert.ok(hasStop(result.state), 'Should terminate with stop');

    const top = getStackTop(result.state);
    assert.ok(top !== null, 'Stack should not be empty');
    const val = binToInt(top);
    assert.ok(val !== null, 'Stack top should be a concrete number');
    // keccak256(0x00..00FF) = e08ec2af...
    assert.equal(val, BigInt('0xe08ec2af2cfc251225e1968fd6ca21e4044f129bffa95bac3503be8bdb30a367'));
  });

  it('SHA3 of 64 bytes produces correct keccak256', () => {
    // PUSH1 0xAA, PUSH1 0x00, MSTORE,
    // PUSH1 0xBB, PUSH1 0x20, MSTORE,
    // PUSH1 0x40, PUSH1 0x00, SHA3, STOP
    const code = '60aa6000 52 60bb6020 52 60406000 20 00'.replace(/\s/g, '');
    const state = makeState(code, calc);
    const result = calc.exec(state, { maxSteps: 500 });

    assert.ok(result.quiescent, 'Should reach quiescence');
    assert.ok(hasStop(result.state), 'Should terminate with stop');

    const top = getStackTop(result.state);
    assert.ok(top !== null, 'Stack should not be empty');
    const val = binToInt(top);
    assert.ok(val !== null, 'Stack top should be a concrete number');
    assert.equal(val, BigInt('0xe75341cef40916e44766738c5c2fc48518809c87d2843a8bec425b4bc23f242e'));
  });

  it('SHA3 of 0 bytes produces keccak256(empty)', () => {
    // PUSH1 0x00, PUSH1 0x00, SHA3, STOP
    const code = '6000600020 00'.replace(/\s/g, '');
    const state = makeState(code, calc);
    const result = calc.exec(state, { maxSteps: 500 });

    assert.ok(result.quiescent, 'Should reach quiescence');
    assert.ok(hasStop(result.state), 'Should terminate with stop');

    const top = getStackTop(result.state);
    assert.ok(top !== null, 'Stack should not be empty');
    const val = binToInt(top);
    assert.ok(val !== null, 'Stack top should be a concrete number');
    // keccak256('') = c5d24601...
    assert.equal(val, BigInt('0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'));
  });

  it('SHA3 takes few forward steps (no state machine)', () => {
    const code = '60ff6000526020600020 00'.replace(/\s/g, '');
    const state = makeState(code, calc);
    const result = calc.exec(state, { maxSteps: 500, trace: true });

    assert.ok(result.quiescent);
    assert.ok(result.steps <= 7, `Expected <= 7 steps, got ${result.steps}`);
    const traceStr = result.trace.join(' ');
    assert.ok(!traceStr.includes('sha3_iter'), 'Should not use sha3_iter');
    assert.ok(!traceStr.includes('loli'), 'Should not use loli');
  });
});
