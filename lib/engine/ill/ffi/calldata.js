/**
 * Calldata FFI — cd_read for ground binlit calldata
 *
 * Delegates byte extraction to arith-core.js (shared with residual-resolver).
 *
 * LEADING-ZERO LIMITATION: This FFI only handles raw binlit calldata where the
 * BigInt value has no leading-zero bytes. For calldata like 0x00AABB (3 bytes,
 * first byte = 0x00), the BigInt strips the leading zero to 0xAABB (2 bytes),
 * causing byteLen = 2 instead of 3 — wrong byte offsets result.
 *
 * The canonical calldata representation is sconcat(32, chunk, rest), which
 * encode byte positions correctly in 32-byte aligned chunks. translate.js always
 * produces sconcat chains; this FFI is only an optimization for non-leading-zero
 * binlit cases. For any calldata with leading-zero bytes, use sconcat form.
 */

'use strict';

const { binToInt, intToBin } = require('./convert');
const { computeArith } = require('./arith-core');

/**
 * FFI for cd_read: read 32 bytes from ground binlit calldata at offset.
 * Mode: + + - (multiModal)
 * cd_read(CD, Offset, Value)
 */
function cd_read(args) {
  const [cdHash, offsetHash, valueSlot] = args;
  const cdVal = binToInt(cdHash);
  if (cdVal === null) return { success: false, reason: 'symbolic_calldata' };
  const offset = binToInt(offsetHash);
  if (offset === null) return { success: false, reason: 'symbolic_offset' };
  const result = computeArith('cd_read', [cdVal, offset]);
  return { success: true, theta: [[valueSlot, intToBin(result)]] };
}

module.exports = { cd_read };
