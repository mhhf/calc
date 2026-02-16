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

  if (!isGround(a)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  if (aInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const bInt = aInt + 1n;
  const bHash = intToBin(bInt);

  return {
    success: true,
    theta: [[b, bHash]]
  };
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

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const qInt = aInt / bInt;
  const qHash = intToBin(qInt);

  return {
    success: true,
    theta: [[q, qHash]]
  };
}

/**
 * FFI for mod: A % B = R
 * Mode: + + -
 */
function mod(args) {
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
    return { success: false, reason: 'division_by_zero' };
  }

  const rInt = aInt % bInt;
  const rHash = intToBin(rInt);

  return {
    success: true,
    theta: [[r, rHash]]
  };
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

  if (!isGround(a) || !isGround(b) || !isGround(carry)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);
  const cInt = binToInt(carry);

  if (aInt === null || bInt === null || cInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const result = aInt > bInt ? 1n : (aInt < bInt ? 0n : cInt);
  return { success: true, theta: [[z, intToBin(result)]] };
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

module.exports = {
  plus, inc, mul, sub, div, mod, lt, le, eq, neq,
  gt, bitwiseAnd, to256,
  fixed_mul, fixed_div,
  string_concat, string_length
};
