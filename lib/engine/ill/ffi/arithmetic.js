/**
 * Arithmetic Operations for FFI
 *
 * All functions follow the pattern:
 * - Check mode (ground inputs)
 * - Convert to BigInt
 * - Compute result
 * - Return substitution binding output to result
 */

const { binToInt, intToBin, strToHash, hashToStr, isGround } = require('./convert');
const { computeArith } = require('./arith-core');

// Shared empty theta array for comparison FFIs (avoids allocation per call)
const EMPTY_THETA = [];

/**
 * FFI for plus: A + B = C (multi-modal)
 * Mode + + -: C = A + B (used by evm/add)
 * Mode - + +: A = C - B (used by evm/sub via !plus C B A)
 * Uses binToInt for mode detection (correctly rejects freevars unlike isGround).
 */
function plus(args) {
  const [a, b, c] = args;
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt !== null && bInt !== null) {
    return { success: true, theta: [[c, intToBin(aInt + bInt)]] };
  }

  if (bInt !== null) {
    const cInt = binToInt(c);
    if (cInt !== null) {
      if (cInt < bInt) return { success: false, reason: 'negative_result' };
      return { success: true, theta: [[a, intToBin(cInt - bInt)]] };
    }
  }

  return { success: false, reason: 'mode_mismatch' };
}

/**
 * FFI for inc: succ(A) = B
 * Mode: + -
 */
function inc(args) {
  const [a, b] = args;
  if (!isGround(a)) return { success: false, reason: 'mode_mismatch' };
  const aInt = binToInt(a);
  if (aInt === null) return { success: false, reason: 'conversion_failed' };
  return { success: true, theta: [[b, intToBin(computeArith('inc', [aInt]))]] };
}

/**
 * FFI for mul: A * B = C
 * Mode: + + -
 */
function mul(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt * bInt;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for sub: A - B = C (saturating at 0)
 * Mode: + + -
 */
function sub(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt >= bInt ? aInt - bInt : 0n;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for div: A / B = Q (integer division)
 * Mode: + + -
 */
function div(args) {
  const [a, b, q] = args;
  if (!isGround(a) || !isGround(b)) return { success: false, reason: 'mode_mismatch' };
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  if (aInt === null || bInt === null) return { success: false, reason: 'conversion_failed' };
  const result = computeArith('div', [aInt, bInt]);
  if (result === null) return { success: false, reason: 'division_by_zero' };
  return { success: true, theta: [[q, intToBin(result)]] };
}

/**
 * FFI for mod: A % B = R
 * Mode: + + -
 */
function mod(args) {
  const [a, b, r] = args;
  if (!isGround(a) || !isGround(b)) return { success: false, reason: 'mode_mismatch' };
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  if (aInt === null || bInt === null) return { success: false, reason: 'conversion_failed' };
  const result = computeArith('mod', [aInt, bInt]);
  if (result === null) return { success: false, reason: 'division_by_zero' };
  return { success: true, theta: [[r, intToBin(result)]] };
}

/**
 * FFI for lt: A < B
 * Mode: + +
 * Returns success if true, failure if false
 */
function lt(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: aInt < bInt, theta: EMPTY_THETA };
}

/**
 * FFI for le: A <= B
 * Mode: + +
 */
function le(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: aInt <= bInt, theta: EMPTY_THETA };
}

/**
 * FFI for eq: A == B
 * Mode: + +
 */
function eq(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: aInt === bInt, theta: EMPTY_THETA };
}

/**
 * FFI for eq_bool: deterministic boolean equality
 * eq_bool(A, B, R): R = 1 if A == B, R = 0 if A != B
 * Mode: + + -
 */
function eq_bool(args) {
  const [a, b, z] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const result = aInt === bInt ? 1n : 0n;
  return { success: true, theta: [[z, intToBin(result)]] };
}

/**
 * FFI for fixed_mul: Fixed-point multiplication
 * C = (A * B) / 10^D
 * Mode: + + + -
 */
function fixed_mul(args) {
  const [d, a, b, c] = args;

  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const scale = 10n ** decimals;
  const result = (aInt * bInt) / scale;
  const cHash = intToBin(result);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for fixed_div: Fixed-point division
 * C = (A * 10^D) / B
 * Mode: + + + -
 */
function fixed_div(args) {
  const [d, a, b, c] = args;

  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const scale = 10n ** decimals;
  const result = (aInt * scale) / bInt;
  const cHash = intToBin(result);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for string_concat: String concatenation
 * C = A ++ B
 * Mode: + + -
 */
function string_concat(args) {
  const [a, b, c] = args;

  const aStr = hashToStr(a);
  const bStr = hashToStr(b);

  if (aStr === null || bStr === null) {
    return { success: false, reason: 'not_string' };
  }

  const cHash = strToHash(aStr + bStr);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for string_length: String length
 * Len = length(S)
 * Mode: + -
 */
function string_length(args) {
  const [s, len] = args;

  const str = hashToStr(s);

  if (str === null) {
    return { success: false, reason: 'not_string' };
  }

  const lenHash = intToBin(BigInt(str.length));

  return {
    success: true,
    theta: [[len, lenHash]]
  };
}

/**
 * FFI for neq: A != B
 * Mode: + +
 * Returns success if values are not equal, failure if equal
 */
function neq(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: aInt !== bInt, theta: EMPTY_THETA };
}

/**
 * FFI for gt: greater-than comparison with carry
 * gt(A, B, Carry, Z): Z = A > B ? 1 : (A < B ? 0 : Carry)
 * Mode: + + + -
 */
function gt(args) {
  const [a, b, carry, z] = args;
  if (!isGround(a) || !isGround(b) || !isGround(carry)) return { success: false, reason: 'mode_mismatch' };
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  const cInt = binToInt(carry);
  if (aInt === null || bInt === null || cInt === null) return { success: false, reason: 'conversion_failed' };
  return { success: true, theta: [[z, intToBin(computeArith('gt', [aInt, bInt, cInt]))]] };
}

/**
 * FFI for bitwiseAnd: bitwise AND
 * and(A, B, Z): Z = A & B
 * Mode: + + -
 */
function bitwiseAnd(args) {
  const [a, b, z] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: true, theta: [[z, intToBin(aInt & bInt)]] };
}

/**
 * FFI for to256: mod 2^256 (pad/truncate to 256 bits)
 * to256(X, Y): Y = X mod 2^256
 * Mode: + -
 */
const MOD_256 = (1n << 256n) - 1n;

function to256(args) {
  const [x, y] = args;

  if (!isGround(x)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const xInt = binToInt(x);
  if (xInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: true, theta: [[y, intToBin(xInt & MOD_256)]] };
}

/**
 * FFI for shr: logical right shift
 * shr(Shift, Value, Z): Z = Value >> Shift (mod 2^256)
 * Mode: + + -
 */
function shr(args) {
  const [shift, value, z] = args;

  if (!isGround(shift) || !isGround(value)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const shiftInt = binToInt(shift);
  const valueInt = binToInt(value);

  if (shiftInt === null || valueInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const result = shiftInt >= 256n ? 0n : valueInt >> shiftInt;
  return { success: true, theta: [[z, intToBin(result & MOD_256)]] };
}

/**
 * FFI for shl: logical left shift
 * shl(Shift, Value, Z): Z = (Value << Shift) mod 2^256
 * Mode: + + -
 */
function shl(args) {
  const [shift, value, z] = args;

  if (!isGround(shift) || !isGround(value)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const shiftInt = binToInt(shift);
  const valueInt = binToInt(value);

  if (shiftInt === null || valueInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const result = shiftInt >= 256n ? 0n : (valueInt << shiftInt) & MOD_256;
  return { success: true, theta: [[z, intToBin(result)]] };
}

/**
 * FFI for bitwiseOr: bitwise OR
 * or(A, B, Z): Z = A | B
 * Mode: + + -
 */
function bitwiseOr(args) {
  const [a, b, z] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: true, theta: [[z, intToBin(aInt | bInt)]] };
}

/**
 * FFI for bitwiseNot: bitwise NOT (256-bit)
 * not(X, Y): Y = ~X (mod 2^256)
 * Mode: + -
 */
function bitwiseNot(args) {
  const [x, y] = args;

  if (!isGround(x)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const xInt = binToInt(x);
  if (xInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: true, theta: [[y, intToBin(xInt ^ MOD_256)]] };
}

/**
 * FFI for slt: signed less-than (256-bit two's complement)
 * slt(A, B, Z): Z = signed(A) < signed(B) ? 1 : 0
 * Mode: + + -
 */
const SIGN_BIT = 1n << 255n;
const MOD_2_256 = 1n << 256n;

function slt(args) {
  const [a, b, z] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const aSigned = aInt >= SIGN_BIT ? aInt - MOD_2_256 : aInt;
  const bSigned = bInt >= SIGN_BIT ? bInt - MOD_2_256 : bInt;

  const result = aSigned < bSigned ? 1n : 0n;
  return { success: true, theta: [[z, intToBin(result)]] };
}

// ============================================================================
// EVM-specific arithmetic (modular / signed / zero-safe)
// General arithmetic (plus, mul, sub, div, mod, exp) stays pure.
// ============================================================================

/**
 * FFI for sub256: EVM modular subtraction
 * sub256(A, B, C): C = (A - B) mod 2^256
 * Mode: + + -
 *
 * Unlike `sub` (saturating), this wraps: sub256(3, 5) = 2^256 - 2.
 * EVM-specific — general arithmetic uses saturating `sub`.
 */
function sub256(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = ((aInt - bInt) % MOD_2_256 + MOD_2_256) % MOD_2_256;
  return { success: true, theta: [[c, intToBin(cInt)]] };
}

/**
 * FFI for div256: EVM integer division (zero-safe)
 * div256(A, B, Q): Q = A / B, or 0 when B = 0
 * Mode: + + -
 *
 * EVM-specific — general `div` fails on zero divisor.
 */
function div256(args) {
  const [a, b, q] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const qInt = bInt === 0n ? 0n : aInt / bInt;
  return { success: true, theta: [[q, intToBin(qInt)]] };
}

/**
 * FFI for mod256: EVM modulo (zero-safe)
 * mod256(A, B, R): R = A % B, or 0 when B = 0
 * Mode: + + -
 *
 * EVM-specific — general `mod` fails on zero divisor.
 */
function mod256(args) {
  const [a, b, r] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const rInt = bInt === 0n ? 0n : aInt % bInt;
  return { success: true, theta: [[r, intToBin(rInt)]] };
}

/**
 * FFI for exp256: EVM modular exponentiation
 * exp256(Base, Exp, Result): Result = Base^Exp mod 2^256
 * Mode: + + -
 *
 * Uses square-and-multiply with modular reduction at each step.
 * EVM-specific — general `exp` computes unbounded.
 */
function exp256(args) {
  const [base, exponent, result] = args;

  if (!isGround(base) || !isGround(exponent)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const baseInt = binToInt(base);
  const expInt = binToInt(exponent);

  if (baseInt === null || expInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (expInt === 0n) {
    return { success: true, theta: [[result, intToBin(1n)]] };
  }

  let r = 1n, b = baseInt & MOD_256, e = expInt;
  while (e > 0n) {
    if (e & 1n) r = (r * b) & MOD_256;
    b = (b * b) & MOD_256;
    e >>= 1n;
  }
  return { success: true, theta: [[result, intToBin(r)]] };
}

/**
 * FFI for trim: normalize binary number (remove leading zeros)
 * trim(X, Y): Y = canonical form of X
 * Mode: + -
 *
 * For binlit values, this is a no-op (already canonical).
 * The binToInt → intToBin roundtrip normalizes any representation.
 */
function trim(args) {
  const [x, y] = args;

  const xInt = binToInt(x);
  if (xInt === null) {
    return { success: false, reason: 'mode_mismatch' };
  }

  return { success: true, theta: [[y, intToBin(xInt)]] };
}

/**
 * FFI for sdiv256: EVM signed integer division (zero-safe)
 * sdiv256(A, B, Q): Q = signed(A) / signed(B), truncated toward zero
 * Mode: + + -
 *
 * If B = 0, Q = 0. JS BigInt division truncates toward zero — matches EVM.
 * INT256_MIN / -1 = INT256_MIN (overflow wraps) — handled naturally since
 * the unsigned 256-bit representation of 2^255 IS INT256_MIN.
 */
function sdiv256(args) {
  const [a, b, q] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: true, theta: [[q, intToBin(0n)]] };
  }

  const aSigned = aInt >= SIGN_BIT ? aInt - MOD_2_256 : aInt;
  const bSigned = bInt >= SIGN_BIT ? bInt - MOD_2_256 : bInt;
  const result = aSigned / bSigned;
  const unsigned = ((result % MOD_2_256) + MOD_2_256) % MOD_2_256;
  return { success: true, theta: [[q, intToBin(unsigned)]] };
}

/**
 * FFI for smod256: EVM signed modulo (zero-safe)
 * smod256(A, B, R): R = signed(A) % signed(B), sign follows A (dividend)
 * Mode: + + -
 *
 * If B = 0, R = 0. JS BigInt % preserves sign of dividend — matches EVM.
 */
function smod256(args) {
  const [a, b, r] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: true, theta: [[r, intToBin(0n)]] };
  }

  const aSigned = aInt >= SIGN_BIT ? aInt - MOD_2_256 : aInt;
  const bSigned = bInt >= SIGN_BIT ? bInt - MOD_2_256 : bInt;
  const result = aSigned % bSigned;
  const unsigned = ((result % MOD_2_256) + MOD_2_256) % MOD_2_256;
  return { success: true, theta: [[r, intToBin(unsigned)]] };
}

/**
 * FFI for addmod256: EVM add-then-mod (zero-safe, 257-bit intermediate)
 * addmod256(A, B, N, R): R = (A + B) mod N, or 0 when N = 0
 * Mode: + + + -
 *
 * Addition is unbounded (BigInt handles 257-bit naturally).
 */
function addmod256(args) {
  const [a, b, n, r] = args;

  if (!isGround(a) || !isGround(b) || !isGround(n)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);
  const nInt = binToInt(n);

  if (aInt === null || bInt === null || nInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (nInt === 0n) {
    return { success: true, theta: [[r, intToBin(0n)]] };
  }

  return { success: true, theta: [[r, intToBin((aInt + bInt) % nInt)]] };
}

/**
 * FFI for mulmod256: EVM mul-then-mod (zero-safe, 512-bit intermediate)
 * mulmod256(A, B, N, R): R = (A * B) mod N, or 0 when N = 0
 * Mode: + + + -
 *
 * Multiplication is unbounded (BigInt handles 512-bit naturally).
 */
function mulmod256(args) {
  const [a, b, n, r] = args;

  if (!isGround(a) || !isGround(b) || !isGround(n)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);
  const nInt = binToInt(n);

  if (aInt === null || bInt === null || nInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (nInt === 0n) {
    return { success: true, theta: [[r, intToBin(0n)]] };
  }

  return { success: true, theta: [[r, intToBin((aInt * bInt) % nInt)]] };
}

/**
 * FFI for signextend256: EVM sign extension
 * signextend256(B, X, Y): sign-extend X at byte B, producing Y
 * Mode: + + -
 *
 * B is 0-based byte index. If B >= 31, Y = X unchanged.
 * Otherwise, bit (B*8+7) is the sign bit: if set, fill high bits with 1;
 * if clear, zero high bits above the extension point.
 */
function signextend256(args) {
  const [b, x, y] = args;

  if (!isGround(b) || !isGround(x)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const bInt = binToInt(b);
  const xInt = binToInt(x);

  if (bInt === null || xInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt >= 31n) {
    return { success: true, theta: [[y, intToBin(xInt & MOD_256)]] };
  }

  const bitPos = bInt * 8n + 7n;
  const signBit = (xInt >> bitPos) & 1n;

  if (signBit) {
    // Set all bits above bitPos to 1
    const highMask = MOD_256 ^ ((1n << (bitPos + 1n)) - 1n);
    return { success: true, theta: [[y, intToBin((xInt | highMask) & MOD_256)]] };
  } else {
    // Clear all bits above bitPos
    const lowMask = (1n << (bitPos + 1n)) - 1n;
    return { success: true, theta: [[y, intToBin(xInt & lowMask)]] };
  }
}

/**
 * FFI for bitwiseXor: bitwise XOR
 * xor(A, B, Z): Z = A ^ B
 * Mode: + + -
 */
function bitwiseXor(args) {
  const [a, b, z] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return { success: true, theta: [[z, intToBin(aInt ^ bInt)]] };
}

/**
 * FFI for byte256: EVM BYTE — extract Ith byte (big-endian) of 256-bit value
 * byte256(I, X, Z): Z = (X >> ((31-I)*8)) & 0xFF, or 0 if I >= 32
 * Mode: + + -
 */
function byte256(args) {
  const [i, x, z] = args;

  if (!isGround(i) || !isGround(x)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const iInt = binToInt(i);
  const xInt = binToInt(x);

  if (iInt === null || xInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (iInt >= 32n) {
    return { success: true, theta: [[z, intToBin(0n)]] };
  }

  const shift = (31n - iInt) * 8n;
  return { success: true, theta: [[z, intToBin((xInt >> shift) & 0xFFn)]] };
}

/**
 * FFI for sar256: EVM arithmetic right shift (sign-extending)
 * sar256(Shift, Value, Z): Z = Value >>_s Shift (256-bit two's complement)
 * Mode: + + -
 *
 * Positive values: identical to SHR.
 * Negative values (MSB=1): vacated high bits filled with 1s.
 * Shift >= 256: saturates to 0 (positive) or 2^256-1 (negative).
 */
function sar256(args) {
  const [shift, value, z] = args;

  if (!isGround(shift) || !isGround(value)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const shiftInt = binToInt(shift);
  const valInt = binToInt(value);

  if (shiftInt === null || valInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const isNegative = valInt >= SIGN_BIT;

  if (shiftInt >= 256n) {
    return { success: true, theta: [[z, intToBin(isNegative ? MOD_256 : 0n)]] };
  }

  // Convert to signed two's complement, shift (BigInt >> is arithmetic), convert back
  const signed = isNegative ? (valInt - MOD_2_256) : valInt;
  const result = signed >> shiftInt;
  const unsigned = ((result % MOD_2_256) + MOD_2_256) % MOD_2_256;
  return { success: true, theta: [[z, intToBin(unsigned)]] };
}

/**
 * FFI for checked_sub: guarded subtraction (fails when A < B)
 * checked_sub(A, B, C): C = A - B, only when A >= B
 * Mode: + + -
 *
 * Used by EVM gas model: checked_sub(GAS, Cost, GAS') fails → OOG.
 */
function checked_sub(args) {
  const [a, b, c] = args;
  if (!isGround(a) || !isGround(b)) return { success: false, reason: 'mode_mismatch' };
  const aInt = binToInt(a);
  const bInt = binToInt(b);
  if (aInt === null || bInt === null) return { success: false, reason: 'conversion_failed' };
  const result = computeArith('checked_sub', [aInt, bInt]);
  if (result === null) return { success: false, reason: 'underflow' };
  return { success: true, theta: [[c, intToBin(result)]] };
}

/**
 * FFI for byte_size256: count bytes in a 256-bit value
 * byte_size256(X, N): N = number of bytes needed to represent X
 * Mode: + -
 *
 * Used by EVM EXP gas: cost = 10 + 50 * byte_size(exponent).
 * byte_size(0) = 0.
 */
function byte_size256(args) {
  const [x, n] = args;

  if (!isGround(x)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const xInt = binToInt(x);
  if (xInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (xInt === 0n) {
    return { success: true, theta: [[n, intToBin(0n)]] };
  }

  let bytes = 0n;
  let v = xInt;
  while (v > 0n) { v >>= 8n; bytes++; }
  return { success: true, theta: [[n, intToBin(bytes)]] };
}

/**
 * FFI for sstore_gas: SSTORE gas cost per Yellow Paper
 * Mode: + + - (multiModal)
 * sstore_gas(OldVal, NewVal, Cost)
 * Cost = 20000 (Gsset) if OldVal == 0 && NewVal != 0, else 5000 (Gsreset)
 * For symbolic (non-ground) inputs, returns 5000 as conservative default.
 */
function sstore_gas(args) {
  const [oldVal, newVal, costSlot] = args;
  const old = binToInt(oldVal);
  const nw = binToInt(newVal);
  if (old === null || nw === null) {
    // Symbolic — default to Gsreset (5000). Concrete execution resolves exactly.
    return { success: true, theta: [[costSlot, intToBin(0x1388n)]] };
  }
  const cost = (old === 0n && nw !== 0n) ? 0x4e20n : 0x1388n;
  return { success: true, theta: [[costSlot, intToBin(cost)]] };
}

/**
 * FFI for is_push: opcode range check (0x60–0x7f)
 * is_push(Opcode, N): N = Opcode - 0x5f (1-based: push1→1, push32→32)
 * Mode: + -
 */
function is_push(args) {
  const [opcode, n] = args;
  const op = binToInt(opcode);
  if (op === null) return { success: false, reason: 'mode_mismatch' };
  if (op < 0x60n || op > 0x7fn) return { success: false, reason: 'out_of_range' };
  return { success: true, theta: [[n, intToBin(op - 0x5fn)]] };
}

/**
 * FFI for is_dup: opcode range check (0x80–0x8f)
 * is_dup(Opcode, N): N = Opcode - 0x80 (0-based: dup1→0, dup16→15)
 * Mode: + -
 */
function is_dup(args) {
  const [opcode, n] = args;
  const op = binToInt(opcode);
  if (op === null) return { success: false, reason: 'mode_mismatch' };
  if (op < 0x80n || op > 0x8fn) return { success: false, reason: 'out_of_range' };
  return { success: true, theta: [[n, intToBin(op - 0x80n)]] };
}

/**
 * FFI for is_swap: opcode range check (0x90–0x9f)
 * is_swap(Opcode, N): N = Opcode - 0x90 (0-based: swap1→0, swap16→15)
 * Mode: + -
 */
function is_swap(args) {
  const [opcode, n] = args;
  const op = binToInt(opcode);
  if (op === null) return { success: false, reason: 'mode_mismatch' };
  if (op < 0x90n || op > 0x9fn) return { success: false, reason: 'out_of_range' };
  return { success: true, theta: [[n, intToBin(op - 0x90n)]] };
}

/**
 * FFI for byte_replace: set byte at position in 256-bit value
 * byte_replace(Word, Pos, Byte, Result):
 *   Result = (Word & ~(0xFF << (31-Pos)*8)) | ((Byte & 0xFF) << (31-Pos)*8)
 * Mode: + + + -
 */
function byte_replace(args) {
  const [word, pos, byte_, result] = args;

  if (!isGround(word) || !isGround(pos) || !isGround(byte_)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const wordInt = binToInt(word);
  const posInt = binToInt(pos);
  const byteInt = binToInt(byte_);

  if (wordInt === null || posInt === null || byteInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (posInt >= 32n) {
    return { success: false, reason: 'out_of_bounds' };
  }

  const shift = (31n - posInt) * 8n;
  const mask = 0xFFn << shift;
  const cleared = wordInt & ~mask;
  const resultInt = cleared | ((byteInt & 0xFFn) << shift);
  return { success: true, theta: [[result, intToBin(resultInt)]] };
}

module.exports = {
  plus, inc, mul, sub, div, mod, lt, le, eq, eq_bool, neq,
  gt, bitwiseAnd, bitwiseOr, bitwiseNot, bitwiseXor, to256, shr, shl, slt,
  sub256, div256, mod256, exp256, trim,
  sdiv256, smod256, addmod256, mulmod256, signextend256,
  byte256, byte_replace, sar256, checked_sub, byte_size256,
  fixed_mul, fixed_div,
  string_concat, string_length,
  sstore_gas,
  is_push, is_dup, is_swap
};
