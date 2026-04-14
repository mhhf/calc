/**
 * Shared arithmetic core — pure BigInt dispatch.
 *
 * No Store dependency. Both FFI (returns theta) and residual-resolver
 * (returns ground fact hash) call this shared core.
 *
 * @param {string} pred - predicate name
 * @param {bigint[]} args - ground BigInt arguments (input positions only)
 * @returns {bigint|null} computed result, or null on failure/division-by-zero
 */

'use strict';

function computeArith(pred, args) {
  switch (pred) {
    case 'inc':
      return args[0] + 1n;

    case 'plus':
      return args[0] + args[1];

    case 'checked_sub':
      return args[0] >= args[1] ? args[0] - args[1] : null;

    case 'gt': {
      const [a, b, c] = args;
      return a > b ? 1n : (a < b ? 0n : c);
    }

    case 'add_mod':
      return args[2] === 0n ? null : (args[0] + args[1]) % args[2];

    case 'mul_mod':
      return args[2] === 0n ? null : (args[0] * args[1]) % args[2];

    case 'div':
      return args[1] === 0n ? null : args[0] / args[1];

    case 'mod':
      return args[1] === 0n ? null : args[0] % args[1];

    case 'cd_read':
      return _cdRead(args[0], args[1]);

    default:
      return null;
  }
}

/**
 * cd_read byte extraction — pure BigInt.
 * Reads 32 bytes from ground BigInt calldata at offset.
 * Leading-zero limitation: cdVal must not have leading-zero bytes.
 */
function _cdRead(cdVal, offVal) {
  const off = Number(offVal);
  let byteLen = 0;
  if (cdVal > 0n) {
    let v = cdVal;
    while (v > 0n) { v >>= 8n; byteLen++; }
  }
  if (off >= byteLen) return 0n;
  const avail = Math.min(32, byteLen - off);
  const rShift = BigInt(Math.max(0, byteLen - off - 32) * 8);
  const mask = (1n << BigInt(avail * 8)) - 1n;
  const extracted = (cdVal >> rShift) & mask;
  return (extracted << BigInt((32 - avail) * 8)) & ((1n << 256n) - 1n);
}

module.exports = { computeArith };
