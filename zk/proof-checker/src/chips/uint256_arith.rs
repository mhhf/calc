//! Uint256ArithChip: 256-bit arithmetic verification via limb decomposition.
//!
//! Phase 6-6b: verifies arithmetic operations on values exceeding BabyBear range.
//! Uses 8-bit limbs (32 per 256-bit value) — products of 8-bit values fit in
//! BabyBear (max 255*255 = 65025 << 2^31).
//!
//! Preprocessed (width 99): [pred_hash, is_active, is_plus_256, is_inc_256,
//!                           a_limb_0..31, b_limb_0..31, c_limb_0..31]
//! Main trace (width 33):   [num_lookups, carry_0..31]
//!
//! Constraints (addition: is_plus_256=1):
//!   a[i] + b[i] + carry_in[i] - c[i] - carry_out[i] * 256 = 0
//!   carry_in[0] = 0 (no incoming carry for LSB)
//!   carry_out[31] = 0 (no overflow for 256-bit)
//!
//! Constraints (increment: is_inc_256=1):
//!   a[0] + 1 + carry_in[0] - c[0] - carry_out[0] * 256 = 0
//!   a[i] + carry_in[i] - c[i] - carry_out[i] * 256 = 0  (i > 0)
//!
//! Range checks: each limb looks up BYTE_CHECK_BUS.
//! Supplies PRED_BUS (same as PredicateRomAir).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{BYTE_CHECK_BUS, PRED_BUS};

/// Number of 8-bit limbs per 256-bit value.
pub const NUM_LIMBS: usize = 32;

/// Width of the main trace: [num_lookups, carry_0..31].
pub const WIDTH: usize = 1 + NUM_LIMBS; // 33

/// Width of the preprocessed trace:
/// [pred_hash, is_active, is_plus_256, is_inc_256, a_limb_0..31, b_limb_0..31, c_limb_0..31]
pub const PREP_WIDTH: usize = 4 + 3 * NUM_LIMBS; // 100

// Preprocessed column indices.
const P_PRED_HASH: usize = 0;
const P_IS_ACTIVE: usize = 1;
const P_IS_PLUS_256: usize = 2;
const P_IS_INC_256: usize = 3;
const P_A_LIMBS: usize = 4;               // 4..35
const P_B_LIMBS: usize = P_A_LIMBS + NUM_LIMBS;  // 36..67
const P_C_LIMBS: usize = P_B_LIMBS + NUM_LIMBS;  // 68..99

// Main column indices.
const M_NUM_LOOKUPS: usize = 0;
const M_CARRY: usize = 1; // 1..32

/// Uint256ArithChip with data committed at keygen.
pub struct Uint256ArithChip {
    pub entries: Vec<Vec<u32>>,  // each row is PREP_WIDTH wide
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for Uint256ArithChip {
    fn width(&self) -> usize {
        WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = self.entries.len().max(self.min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * PREP_WIDTH);
        for row in &self.entries {
            assert_eq!(row.len(), PREP_WIDTH, "uint256 arith row width mismatch");
            for &v in row {
                data.push(F::from_u32(v));
            }
        }
        for _ in self.entries.len()..n {
            for _ in 0..PREP_WIDTH {
                data.push(F::ZERO);
            }
        }
        Some(RowMajorMatrix::new(data, PREP_WIDTH))
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for Uint256ArithChip {}
impl<F: Field> PartitionedBaseAir<F> for Uint256ArithChip {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for Uint256ArithChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let pred_hash: AB::Expr = prep_local[P_PRED_HASH].clone().into();
        let is_active: AB::Expr = prep_local[P_IS_ACTIVE].clone().into();
        let is_plus_256: AB::Expr = prep_local[P_IS_PLUS_256].clone().into();
        let is_inc_256: AB::Expr = prep_local[P_IS_INC_256].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[M_NUM_LOOKUPS].clone().into();

        // Read limbs from preprocessed trace
        let mut a = Vec::with_capacity(NUM_LIMBS);
        let mut b = Vec::with_capacity(NUM_LIMBS);
        let mut c = Vec::with_capacity(NUM_LIMBS);
        for i in 0..NUM_LIMBS {
            a.push(prep_local[P_A_LIMBS + i].clone().into());
            b.push(prep_local[P_B_LIMBS + i].clone().into());
            c.push(prep_local[P_C_LIMBS + i].clone().into());
        }

        // Read carries from main trace
        let mut carry: Vec<AB::Expr> = Vec::with_capacity(NUM_LIMBS);
        for i in 0..NUM_LIMBS {
            carry.push(local[M_CARRY + i].clone().into());
        }

        // --- Boolean constraints for carries ---
        for i in 0..NUM_LIMBS {
            builder.assert_zero(
                is_active.clone() * carry[i].clone() * (carry[i].clone() - AB::Expr::ONE)
            );
        }

        // --- Addition constraints (is_plus_256=1): a[i] + b[i] + carry_in - c[i] - carry_out * 256 = 0 ---
        let two_56: AB::Expr = AB::Expr::from_u32(256);
        for i in 0..NUM_LIMBS {
            let carry_in: AB::Expr = if i == 0 {
                AB::Expr::ZERO
            } else {
                carry[i - 1].clone()
            };
            builder.assert_zero(
                is_plus_256.clone() * (
                    a[i].clone() + b[i].clone() + carry_in
                    - c[i].clone() - carry[i].clone() * two_56.clone()
                )
            );
        }
        // No overflow: carry_out[31] must be 0 for 256-bit addition
        builder.assert_zero(is_plus_256.clone() * carry[NUM_LIMBS - 1].clone());

        // --- Increment constraints (is_inc_256=1): a[0]+1+carry_in - c[0] - carry_out*256 = 0 ---
        // Limb 0: a[0] + 1 - c[0] - carry[0] * 256 = 0
        builder.assert_zero(
            is_inc_256.clone() * (
                a[0].clone() + AB::Expr::ONE
                - c[0].clone() - carry[0].clone() * two_56.clone()
            )
        );
        // Limbs 1..31: a[i] + carry_in - c[i] - carry[i] * 256 = 0
        for i in 1..NUM_LIMBS {
            builder.assert_zero(
                is_inc_256.clone() * (
                    a[i].clone() + carry[i - 1].clone()
                    - c[i].clone() - carry[i].clone() * two_56.clone()
                )
            );
        }
        // No overflow: carry_out[31] must be 0
        builder.assert_zero(is_inc_256.clone() * carry[NUM_LIMBS - 1].clone());

        // --- BYTE_CHECK_BUS: range-check all limbs ---
        // Each active row checks 3*32 = 96 limbs (a, b, c)
        for i in 0..NUM_LIMBS {
            BYTE_CHECK_BUS.lookup_key(builder, [a[i].clone()], is_active.clone());
            BYTE_CHECK_BUS.lookup_key(builder, [b[i].clone()], is_active.clone());
            BYTE_CHECK_BUS.lookup_key(builder, [c[i].clone()], is_active.clone());
        }

        // --- PRED_BUS: supply predicate verification entries ---
        PRED_BUS.add_key_with_lookups(builder, [pred_hash], is_active * num_lookups);
    }
}

/// Decompose a 256-bit value (as bytes, little-endian) into 32 limbs.
/// Input: 32 bytes, LSB first.
pub fn value_to_limbs(bytes: &[u8; 32]) -> [u32; NUM_LIMBS] {
    let mut limbs = [0u32; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        limbs[i] = bytes[i] as u32;
    }
    limbs
}

/// Build a preprocessed row for a plus_256 operation.
pub fn make_plus_256_row(pred_hash: u32, a: &[u8; 32], b: &[u8; 32], c: &[u8; 32]) -> Vec<u32> {
    let mut row = Vec::with_capacity(PREP_WIDTH);
    row.push(pred_hash);
    row.push(1); // is_active
    row.push(1); // is_plus_256
    row.push(0); // is_inc_256
    let a_limbs = value_to_limbs(a);
    let b_limbs = value_to_limbs(b);
    let c_limbs = value_to_limbs(c);
    row.extend_from_slice(&a_limbs);
    row.extend_from_slice(&b_limbs);
    row.extend_from_slice(&c_limbs);
    row
}

/// Build a preprocessed row for an inc_256 operation.
pub fn make_inc_256_row(pred_hash: u32, a: &[u8; 32], c: &[u8; 32]) -> Vec<u32> {
    let mut row = Vec::with_capacity(PREP_WIDTH);
    row.push(pred_hash);
    row.push(1); // is_active
    row.push(0); // is_plus_256
    row.push(1); // is_inc_256
    let a_limbs = value_to_limbs(a);
    let b_limbs = [0u32; NUM_LIMBS]; // unused for inc
    let c_limbs = value_to_limbs(c);
    row.extend_from_slice(&a_limbs);
    row.extend_from_slice(&b_limbs);
    row.extend_from_slice(&c_limbs);
    row
}

/// Compute carry chain for addition: a + b = c (mod 2^256).
/// Returns carry bits for each limb position.
pub fn compute_addition_carries(a: &[u8; 32], b: &[u8; 32]) -> Vec<u32> {
    let mut carries = vec![0u32; NUM_LIMBS];
    let mut carry: u32 = 0;
    for i in 0..NUM_LIMBS {
        let sum = a[i] as u32 + b[i] as u32 + carry;
        carries[i] = sum / 256;
        carry = carries[i];
    }
    carries
}

/// Compute carry chain for increment: a + 1 = c (mod 2^256).
pub fn compute_increment_carries(a: &[u8; 32]) -> Vec<u32> {
    let mut carries = vec![0u32; NUM_LIMBS];
    let sum0 = a[0] as u32 + 1;
    carries[0] = sum0 / 256;
    let mut carry = carries[0];
    for i in 1..NUM_LIMBS {
        let sum = a[i] as u32 + carry;
        carries[i] = sum / 256;
        carry = carries[i];
    }
    carries
}

/// Build main trace row: [num_lookups, carry_0..31].
pub fn make_main_row(num_lookups: u32, carries: &[u32]) -> Vec<u32> {
    let mut row = Vec::with_capacity(WIDTH);
    row.push(num_lookups);
    for i in 0..NUM_LIMBS {
        row.push(if i < carries.len() { carries[i] } else { 0 });
    }
    row
}
