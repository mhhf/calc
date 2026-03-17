//! Phase 6-6b: Uint256ArithChip standalone tests.
//!
//! Tests 256-bit addition, increment, and multiplication with synthetic data.
//! No JS pipeline needed — these are pure Rust unit tests.

use std::sync::Arc;

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::config::baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine};
use openvm_stark_sdk::engine::StarkFriEngine as _;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use proof_checker::buses::PRED_BUS;
use proof_checker::chips::byte_check_rom::ByteCheckRomAir;
use proof_checker::chips::uint256_arith::{
    self, Uint256ArithChip, NUM_LIMBS, WIDTH,
};

/// Dummy chip that demands pred_hash on PRED_BUS (standalone test counterpart).
/// Width 2: [pred_hash, is_active]. Each active row does one lookup.
struct PredDemandChip;

impl<F: Field> BaseAir<F> for PredDemandChip {
    fn width(&self) -> usize { 2 }
}
impl<F: Field> BaseAirWithPublicValues<F> for PredDemandChip {}
impl<F: Field> PartitionedBaseAir<F> for PredDemandChip {}

impl<AB: InteractionBuilder> Air<AB> for PredDemandChip
where AB::F: Field {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let pred_hash: AB::Expr = local[0].clone().into();
        let is_active: AB::Expr = local[1].clone().into();
        PRED_BUS.lookup_key(builder, [pred_hash], is_active);
    }
}

/// Build ByteCheckRomAir + trace (always needed alongside Uint256ArithChip).
fn make_byte_check(byte_lookup_counts: &[u32; 256], min_rows: usize) -> (
    AirRef<BabyBearPoseidon2Config>,
    RowMajorMatrix<BabyBear>,
) {
    let air = ByteCheckRomAir { min_rows };
    let n = 256usize.max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n);
    for i in 0..256 {
        data.push(BabyBear::from_u32(byte_lookup_counts[i]));
    }
    for _ in 256..n {
        data.push(BabyBear::ZERO);
    }
    (Arc::new(air) as AirRef<_>, RowMajorMatrix::new(data, 1))
}

/// Build Uint256ArithChip + trace from preprocessed entries and main rows.
fn make_uint256(
    prep_rows: Vec<Vec<u32>>,
    main_rows: Vec<Vec<u32>>,
    min_rows: usize,
) -> (
    AirRef<BabyBearPoseidon2Config>,
    RowMajorMatrix<BabyBear>,
) {
    let air = Uint256ArithChip { entries: prep_rows, min_rows };
    let n = main_rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * WIDTH);
    for row in &main_rows {
        for &v in row {
            data.push(BabyBear::from_u32(v));
        }
    }
    for _ in main_rows.len()..n {
        for _ in 0..WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    (Arc::new(air) as AirRef<_>, RowMajorMatrix::new(data, WIDTH))
}

/// Accumulate byte lookup counts from limbs.
fn accumulate_byte_lookups(counts: &mut [u32; 256], limbs: &[u32]) {
    for &limb in limbs {
        counts[limb as usize] += 1;
    }
}

/// Preprocessed column offset for a_limbs (after flags).
const PREP_A_OFF: usize = 5;

/// Run a standalone STARK test with ByteCheckRomAir + Uint256ArithChip + PredDemandChip.
fn prove_uint256(prep_rows: Vec<Vec<u32>>, main_rows: Vec<Vec<u32>>) {
    let min_rows = 256; // ByteCheckRomAir needs at least 256

    // Accumulate byte lookups from preprocessed data (a, b, c limbs)
    // AND from main trace (carry_lo, carry_hi)
    let mut byte_counts = [0u32; 256];
    for (prep, main) in prep_rows.iter().zip(main_rows.iter()) {
        if prep[1] == 1 { // is_active
            for i in 0..NUM_LIMBS {
                accumulate_byte_lookups(&mut byte_counts, &[prep[PREP_A_OFF + i]]);
                accumulate_byte_lookups(&mut byte_counts, &[prep[PREP_A_OFF + NUM_LIMBS + i]]);
                accumulate_byte_lookups(&mut byte_counts, &[prep[PREP_A_OFF + 2 * NUM_LIMBS + i]]);
                // carry_lo at main[1..32], carry_hi at main[33..64]
                accumulate_byte_lookups(&mut byte_counts, &[main[1 + i]]);
                accumulate_byte_lookups(&mut byte_counts, &[main[1 + NUM_LIMBS + i]]);
            }
        }
    }

    // Build PredDemandChip rows: one demand per active uint256 row
    let mut demand_rows: Vec<Vec<u32>> = Vec::new();
    for row in &prep_rows {
        if row[1] == 1 { // is_active
            demand_rows.push(vec![row[0], 1]); // [pred_hash, is_active]
        }
    }

    let (byte_air, byte_trace) = make_byte_check(&byte_counts, min_rows);
    let (uint_air, uint_trace) = make_uint256(prep_rows, main_rows, min_rows);

    // PredDemandChip
    let demand_air: AirRef<BabyBearPoseidon2Config> = Arc::new(PredDemandChip);
    let n = demand_rows.len().max(min_rows).next_power_of_two();
    let mut demand_data = Vec::with_capacity(n * 2);
    for row in &demand_rows {
        demand_data.push(BabyBear::from_u32(row[0]));
        demand_data.push(BabyBear::from_u32(row[1]));
    }
    for _ in demand_rows.len()..n {
        demand_data.push(BabyBear::ZERO);
        demand_data.push(BabyBear::ZERO);
    }
    let demand_trace = RowMajorMatrix::new(demand_data, 2);

    let airs = vec![byte_air, uint_air, demand_air];
    let traces = vec![byte_trace, uint_trace, demand_trace];
    let pis = vec![vec![], vec![], vec![]];

    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .expect("STARK verification should pass");
}

/// Zero carry_hi for add/inc operations.
const ZERO_HI: [u32; NUM_LIMBS] = [0; NUM_LIMBS];

// ===========================================================================
// Addition tests
// ===========================================================================

#[test]
fn p6_uint256_add_small() {
    let mut a = [0u8; 32]; a[0] = 3;
    let mut b = [0u8; 32]; b[0] = 5;
    let mut c = [0u8; 32]; c[0] = 8;

    let prep = uint256_arith::make_plus_256_row(100, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_add_carry() {
    let mut a = [0u8; 32]; a[0] = 200;
    let mut b = [0u8; 32]; b[0] = 100;
    let mut c = [0u8; 32]; c[0] = 44; c[1] = 1;

    let prep = uint256_arith::make_plus_256_row(101, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    assert_eq!(carries[0], 1);
    assert_eq!(carries[1], 0);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_add_multi_carry() {
    let mut a = [0u8; 32]; a[0] = 0xFF;
    let mut b = [0u8; 32]; b[0] = 0x01;
    let mut c = [0u8; 32]; c[0] = 0x00; c[1] = 0x01;

    let prep = uint256_arith::make_plus_256_row(102, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_add_large() {
    let mut a = [0u8; 32];
    a[0] = 0xFF; a[1] = 0xFF; a[2] = 0xFF; a[3] = 0xFF;
    let mut b = [0u8; 32]; b[0] = 1;
    let mut c = [0u8; 32]; c[4] = 1;

    let prep = uint256_arith::make_plus_256_row(103, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

// ===========================================================================
// Increment tests
// ===========================================================================

#[test]
fn p6_uint256_inc() {
    let mut a = [0u8; 32]; a[0] = 5;
    let mut c = [0u8; 32]; c[0] = 6;

    let prep = uint256_arith::make_inc_256_row(200, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_inc_carry() {
    let mut a = [0u8; 32]; a[0] = 255;
    let mut c = [0u8; 32]; c[0] = 0; c[1] = 1;

    let prep = uint256_arith::make_inc_256_row(201, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    assert_eq!(carries[0], 1);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

// ===========================================================================
// Multi-op test
// ===========================================================================

#[test]
fn p6_uint256_multi_ops() {
    let mut a1 = [0u8; 32]; a1[0] = 3;
    let mut b1 = [0u8; 32]; b1[0] = 5;
    let mut c1 = [0u8; 32]; c1[0] = 8;

    let mut a2 = [0u8; 32]; a2[0] = 10;
    let mut c2 = [0u8; 32]; c2[0] = 11;

    let prep1 = uint256_arith::make_plus_256_row(300, &a1, &b1, &c1);
    let prep2 = uint256_arith::make_inc_256_row(301, &a2, &c2);

    let carries1 = uint256_arith::compute_addition_carries(&a1, &b1);
    let carries2 = uint256_arith::compute_increment_carries(&a2);

    let main1 = uint256_arith::make_main_row(1, &carries1, &ZERO_HI);
    let main2 = uint256_arith::make_main_row(1, &carries2, &ZERO_HI);

    prove_uint256(vec![prep1, prep2], vec![main1, main2]);
}

// ===========================================================================
// Soundness: wrong results → STARK rejection
// ===========================================================================

#[test]
#[should_panic]
fn p6_uint256_add_wrong_result_fails() {
    let mut a = [0u8; 32]; a[0] = 3;
    let mut b = [0u8; 32]; b[0] = 5;
    let mut c = [0u8; 32]; c[0] = 99; // wrong!

    let prep = uint256_arith::make_plus_256_row(400, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
#[should_panic]
fn p6_uint256_inc_wrong_result_fails() {
    let mut a = [0u8; 32]; a[0] = 5;
    let mut c = [0u8; 32]; c[0] = 99; // wrong!

    let prep = uint256_arith::make_inc_256_row(401, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    let main = uint256_arith::make_main_row(1, &carries, &ZERO_HI);

    prove_uint256(vec![prep], vec![main]);
}

// ===========================================================================
// Multiplication tests
// ===========================================================================

#[test]
fn p6_uint256_mul_small() {
    // 3 * 5 = 15
    let mut a = [0u8; 32]; a[0] = 3;
    let mut b = [0u8; 32]; b[0] = 5;
    let mut c = [0u8; 32]; c[0] = 15;

    let prep = uint256_arith::make_mul_256_row(500, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_single_carry() {
    // 200 * 200 = 40000 = 0x9C40 → limb0=0x40, limb1=0x9C
    let mut a = [0u8; 32]; a[0] = 200;
    let mut b = [0u8; 32]; b[0] = 200;
    let mut c = [0u8; 32]; c[0] = 0x40; c[1] = 0x9C;

    let prep = uint256_arith::make_mul_256_row(501, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_multi_limb() {
    // 0x0100 * 0x0100 = 0x00010000
    // a = [0, 1, 0, ...], b = [0, 1, 0, ...], c = [0, 0, 1, 0, ...]
    let mut a = [0u8; 32]; a[1] = 1; // 256
    let mut b = [0u8; 32]; b[1] = 1; // 256
    let mut c = [0u8; 32]; c[2] = 1; // 65536

    let prep = uint256_arith::make_mul_256_row(502, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_large_carry() {
    // 255 * 255 = 65025 = 0xFE01 → limb0=0x01, limb1=0xFE
    // carry_out[0] = 65025 / 256 = 254 → carry_lo=254, carry_hi=0
    let mut a = [0u8; 32]; a[0] = 255;
    let mut b = [0u8; 32]; b[0] = 255;
    let mut c = [0u8; 32]; c[0] = 0x01; c[1] = 0xFE;

    let prep = uint256_arith::make_mul_256_row(503, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    assert_eq!(carries_lo[0], 254);
    assert_eq!(carries_hi[0], 0);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_multi_byte_carry() {
    // Multiple limbs with large values to produce carry_hi > 0.
    // a = [255, 255, 0, ...], b = [255, 255, 0, ...]
    // a * b = 0xFFFF * 0xFFFF = 0xFFFE0001
    // At position k=1: partial_sum = a[0]*b[1] + a[1]*b[0] = 2*255*255 = 130050
    //   + carry_in = 254 → total = 130304
    //   c[1] = 130304 % 256 = 0, carry_out = 130304/256 = 509
    //   carry_lo = 253, carry_hi = 1
    let mut a = [0u8; 32]; a[0] = 255; a[1] = 255;
    let mut b = [0u8; 32]; b[0] = 255; b[1] = 255;
    // 0xFFFF * 0xFFFF = 0xFFFE0001
    let mut c = [0u8; 32]; c[0] = 0x01; c[1] = 0x00; c[2] = 0xFE; c[3] = 0xFF;

    let prep = uint256_arith::make_mul_256_row(504, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    // Position 1 should have carry_hi > 0
    assert!(carries_lo[1] > 0 || carries_hi[1] > 0, "mul should produce multi-byte carry");
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_wrapping() {
    // Multiplication that wraps mod 2^256.
    // (2^128) * (2^128) = 2^256 ≡ 0 (mod 2^256)
    let mut a = [0u8; 32]; a[16] = 1; // 2^128
    let mut b = [0u8; 32]; b[16] = 1; // 2^128
    let c = [0u8; 32]; // 0 (wraps)

    let prep = uint256_arith::make_mul_256_row(505, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}

#[test]
fn p6_uint256_mul_mixed_ops() {
    // Mix add + mul in one proof
    let mut a1 = [0u8; 32]; a1[0] = 10;
    let mut b1 = [0u8; 32]; b1[0] = 20;
    let mut c1 = [0u8; 32]; c1[0] = 30;

    let mut a2 = [0u8; 32]; a2[0] = 7;
    let mut b2 = [0u8; 32]; b2[0] = 8;
    let mut c2 = [0u8; 32]; c2[0] = 56;

    let prep1 = uint256_arith::make_plus_256_row(600, &a1, &b1, &c1);
    let prep2 = uint256_arith::make_mul_256_row(601, &a2, &b2, &c2);

    let carries1 = uint256_arith::compute_addition_carries(&a1, &b1);
    let (carries2_lo, carries2_hi) = uint256_arith::compute_multiplication_carries(&a2, &b2);

    let main1 = uint256_arith::make_main_row(1, &carries1, &ZERO_HI);
    let main2 = uint256_arith::make_main_row(1, &carries2_lo, &carries2_hi);

    prove_uint256(vec![prep1, prep2], vec![main1, main2]);
}

// ===========================================================================
// Soundness: wrong multiplication → STARK rejection
// ===========================================================================

#[test]
#[should_panic]
fn p6_uint256_mul_wrong_result_fails() {
    let mut a = [0u8; 32]; a[0] = 3;
    let mut b = [0u8; 32]; b[0] = 5;
    let mut c = [0u8; 32]; c[0] = 99; // wrong! should be 15

    let prep = uint256_arith::make_mul_256_row(700, &a, &b, &c);
    let (carries_lo, carries_hi) = uint256_arith::compute_multiplication_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries_lo, &carries_hi);

    prove_uint256(vec![prep], vec![main]);
}
