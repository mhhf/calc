/**
 * VMTest Fixture → CALC State Translator
 *
 * Converts Ethereum VMTest JSON fixtures into CALC initial states
 * for forward execution. Pure function, no test dependencies.
 */

const Store = require('../../../lib/kernel/store');
const { intToBin } = require('../../../lib/engine/ill/ffi/convert');
const { bytesToSemantic } = require('../../../lib/engine/index');
const { arrToTrie } = require('../../../lib/engine/ill/ffi/array');

/**
 * Convert a hex string (with or without 0x prefix) to a BigInt.
 */
function hexToBigInt(hex) {
  if (!hex || hex === '0x' || hex === '0x0' || hex === '0x00') return 0n;
  const clean = hex.startsWith('0x') ? hex.slice(2) : hex;
  if (clean === '' || clean === '0') return 0n;
  return BigInt('0x' + clean);
}

/**
 * Convert a hex string to a binlit Store hash.
 */
function hexToBinHash(hex) {
  return intToBin(hexToBigInt(hex));
}

/**
 * Convert a hex code string to a bytecode arrlit (byte-level).
 * E.g. "0x6001600201" → arrlit of [0x60, 0x01, 0x60, 0x02, 0x01]
 */
function hexToByteArray(hex) {
  const clean = hex.startsWith('0x') ? hex.slice(2) : hex;
  if (clean.length % 2 !== 0) throw new Error('Odd hex length: ' + hex);
  const elems = new Uint32Array(clean.length / 2);
  for (let i = 0; i < clean.length; i += 2) {
    elems[i / 2] = intToBin(BigInt(parseInt(clean.slice(i, i + 2), 16)));
  }
  return Store.putArray(elems);
}

/**
 * Build CALC initial state from a VMTest fixture.
 *
 * @param {Object} fixture - The test object (e.g. fixture.add0)
 * @param {Object} calc - Loaded calculus object (for persistent clauses)
 * @returns {{ linear: Object, persistent: Object }}
 */
function fixtureToState(fixture, calc) {
  const exec = fixture.exec;
  const linear = {};
  const persistent = {};

  // Copy all persistent clauses from the calculus
  if (calc && calc.persistent) {
    Object.assign(persistent, calc.persistent);
  }

  // pc(0)
  const pc = Store.put('pc', [intToBin(0n)]);
  linear[pc] = 1;

  // gas(exec.gas)
  const gas = Store.put('gas', [hexToBinHash(exec.gas)]);
  linear[gas] = 1;

  // stack(ae) — empty stack
  const ae = Store.put('atom', ['ae']);
  const stack = Store.put('stack', [ae]);
  linear[stack] = 1;

  // mem(empty_mem)
  const emptyMem = Store.put('atom', ['empty_mem']);
  const mem = Store.put('mem', [emptyMem]);
  linear[mem] = 1;

  // memsize(0)
  const memsize = Store.put('memsize', [intToBin(0n)]);
  linear[memsize] = 1;

  // bytecode — build from hex code, then semantic transform
  const arrHash = hexToByteArray(exec.code);
  const bytecodeHash = Store.put('bytecode', [arrHash]);
  linear[bytecodeHash] = 1;

  // address, sender, origin, callvalue, gasprice
  const address = Store.put('address', [hexToBinHash(exec.address)]);
  linear[address] = 1;

  const sender = Store.put('sender', [hexToBinHash(exec.caller)]);
  linear[sender] = 1;

  const origin = Store.put('origin', [hexToBinHash(exec.origin || exec.caller)]);
  linear[origin] = 1;

  const callvalue = Store.put('callvalue', [hexToBinHash(exec.value)]);
  linear[callvalue] = 1;

  const gasprice = Store.put('gasprice', [hexToBinHash(exec.gasPrice || '0x0')]);
  linear[gasprice] = 1;

  // codesize — byte length of the deployed contract code
  const codeClean = exec.code.startsWith('0x') ? exec.code.slice(2) : exec.code;
  const codeLenBytes = BigInt(codeClean.length / 2);
  linear[Store.put('codesize', [intToBin(codeLenBytes)])] = 1;

  // Environment: timestamp, gaslimit, coinbase, number, difficulty
  if (fixture.env) {
    const timestamp = Store.put('timestamp', [hexToBinHash(fixture.env.currentTimestamp)]);
    linear[timestamp] = 1;

    const gaslimit = Store.put('gaslimit', [hexToBinHash(fixture.env.currentGasLimit)]);
    linear[gaslimit] = 1;

    const coinbase = Store.put('coinbase', [hexToBinHash(fixture.env.currentCoinbase)]);
    linear[coinbase] = 1;

    const number = Store.put('number', [hexToBinHash(fixture.env.currentNumber)]);
    linear[number] = 1;

    const difficulty = Store.put('difficulty', [hexToBinHash(fixture.env.currentDifficulty)]);
    linear[difficulty] = 1;
  }

  // Pre-existing storage + initializedStorage list
  const preAddr = exec.address.toLowerCase();
  const pre = fixture.pre && fixture.pre[preAddr];
  const preStorage = (pre && pre.storage) || {};
  const storageKeys = Object.keys(preStorage);

  // Build initializedStorage list: acons(k1, acons(k2, ... ae))
  let isetHash = ae; // ae = empty list
  for (const key of storageKeys) {
    const keyHash = hexToBinHash(key);
    const valHash = hexToBinHash(preStorage[key]);
    const storageFact = Store.put('storage', [keyHash, valHash]);
    linear[storageFact] = 1;
    isetHash = Store.put('acons', [keyHash, isetHash]);
  }
  const isetFact = Store.put('initializedStorage', [isetHash]);
  linear[isetFact] = 1;

  // Balance for the contract address
  if (pre && pre.balance) {
    const balance = Store.put('balance', [hexToBinHash(preAddr), hexToBinHash(pre.balance)]);
    linear[balance] = 1;
  }

  // Calldata — sconcat chain of 32-byte chunks (D1/D6: calldata is linear, single fact)
  const calldataHex = exec.data;
  const epsilon = Store.put('atom', ['epsilon']);
  if (calldataHex && calldataHex !== '0x') {
    const cdClean = calldataHex.startsWith('0x') ? calldataHex.slice(2) : calldataHex;
    const cdLen = cdClean.length / 2;
    linear[Store.put('calldatasize', [intToBin(BigInt(cdLen))])] = 1;
    // Build sconcat chain from last chunk backwards
    let cdStruct = epsilon;
    const numChunks = Math.ceil(cdLen / 32);
    for (let i = numChunks - 1; i >= 0; i--) {
      const offset = i * 32;
      const chunk = cdClean.slice(offset * 2, (offset + 32) * 2).padEnd(64, '0');
      const valHash = intToBin(BigInt('0x' + chunk));
      cdStruct = Store.put('sconcat', [intToBin(32n), valHash, cdStruct]);
    }
    linear[Store.put('calldata', [cdStruct])] = 1;
  } else {
    linear[Store.put('calldatasize', [intToBin(0n)])] = 1;
    linear[Store.put('calldata', [epsilon])] = 1;
  }

  // Apply bytesToSemantic to combine PUSH data bytes
  let state = { linear, persistent };
  state = bytesToSemantic(state);

  // Convert bytecode arrlit → bit-indexed trie for O(log N) clause access
  const bcTagId = Store.TAG['bytecode'];
  for (const h of Object.keys(state.linear)) {
    const hNum = Number(h);
    if (Store.tagId(hNum) === bcTagId) {
      const arrH = Store.rawChild(hNum, 0);
      const trieH = arrToTrie(arrH);
      if (trieH !== arrH) {
        delete state.linear[h];
        state.linear[Store.put('bytecode', [trieH])] = 1;
      }
      break;
    }
  }

  return state;
}

module.exports = { fixtureToState, hexToBigInt, hexToBinHash };
