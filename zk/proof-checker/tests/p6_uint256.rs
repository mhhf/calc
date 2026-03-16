//! Phase 6-6b: Uint256ArithChip standalone tests.
//!
//! Tests 256-bit addition and increment with synthetic data.
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

/// Run a standalone STARK test with ByteCheckRomAir + Uint256ArithChip + PredDemandChip.
fn prove_uint256(prep_rows: Vec<Vec<u32>>, main_rows: Vec<Vec<u32>>) {
    let min_rows = 256; // ByteCheckRomAir needs at least 256

    // Accumulate byte lookups from preprocessed data
    let mut byte_counts = [0u32; 256];
    for row in &prep_rows {
        if row[1] == 1 { // is_active
            for i in 0..NUM_LIMBS {
                accumulate_byte_lookups(&mut byte_counts, &[row[4 + i]]);
                accumulate_byte_lookups(&mut byte_counts, &[row[4 + NUM_LIMBS + i]]);
                accumulate_byte_lookups(&mut byte_counts, &[row[4 + 2 * NUM_LIMBS + i]]);
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

// ---------------------------------------------------------------------------
// Test: 256-bit addition (small values that fit in first limb)
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_add_small() {
    // 3 + 5 = 8 (trivial, all in limb 0)
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    let mut c = [0u8; 32];
    a[0] = 3;
    b[0] = 5;
    c[0] = 8;

    let prep = uint256_arith::make_plus_256_row(100, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: 256-bit addition with carry propagation
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_add_carry() {
    // 200 + 100 = 300 → limb0=44, carry to limb1=1
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    a[0] = 200;
    b[0] = 100;
    // 200 + 100 = 300 = 1*256 + 44
    let mut c = [0u8; 32];
    c[0] = 44;
    c[1] = 1;

    let prep = uint256_arith::make_plus_256_row(101, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    assert_eq!(carries[0], 1, "carry from limb 0");
    assert_eq!(carries[1], 0, "no carry from limb 1");
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: 256-bit addition with multi-limb carry chain
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_add_multi_carry() {
    // 0xFF + 0x01 = 0x100 (carry propagates through limb 0 to limb 1)
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    a[0] = 0xFF;
    b[0] = 0x01;
    let mut c = [0u8; 32];
    c[0] = 0x00;
    c[1] = 0x01;

    let prep = uint256_arith::make_plus_256_row(102, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: 256-bit addition with large values (multi-byte)
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_add_large() {
    // 0xFFFFFFFF + 1 = 0x100000000
    let mut a = [0u8; 32];
    a[0] = 0xFF; a[1] = 0xFF; a[2] = 0xFF; a[3] = 0xFF;
    let mut b = [0u8; 32];
    b[0] = 1;
    let mut c = [0u8; 32];
    c[4] = 1; // 0x100000000

    let prep = uint256_arith::make_plus_256_row(103, &a, &b, &c);
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: 256-bit increment
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_inc() {
    // inc(5) = 6
    let mut a = [0u8; 32];
    let mut c = [0u8; 32];
    a[0] = 5;
    c[0] = 6;

    let prep = uint256_arith::make_inc_256_row(200, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: 256-bit increment with carry
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_inc_carry() {
    // inc(255) = 256 → limb0=0, limb1=1
    let mut a = [0u8; 32];
    let mut c = [0u8; 32];
    a[0] = 255;
    c[0] = 0;
    c[1] = 1;

    let prep = uint256_arith::make_inc_256_row(201, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    assert_eq!(carries[0], 1);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Test: multiple operations in one proof
// ---------------------------------------------------------------------------

#[test]
fn p6_uint256_multi_ops() {
    // Two operations: 3+5=8 and inc(10)=11
    let mut a1 = [0u8; 32]; a1[0] = 3;
    let mut b1 = [0u8; 32]; b1[0] = 5;
    let mut c1 = [0u8; 32]; c1[0] = 8;

    let mut a2 = [0u8; 32]; a2[0] = 10;
    let mut c2 = [0u8; 32]; c2[0] = 11;

    let prep1 = uint256_arith::make_plus_256_row(300, &a1, &b1, &c1);
    let prep2 = uint256_arith::make_inc_256_row(301, &a2, &c2);

    let carries1 = uint256_arith::compute_addition_carries(&a1, &b1);
    let carries2 = uint256_arith::compute_increment_carries(&a2);

    let main1 = uint256_arith::make_main_row(1, &carries1);
    let main2 = uint256_arith::make_main_row(1, &carries2);

    prove_uint256(vec![prep1, prep2], vec![main1, main2]);
}

// ---------------------------------------------------------------------------
// Soundness: wrong addition result → STARK rejection
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_uint256_add_wrong_result_fails() {
    let mut a = [0u8; 32]; a[0] = 3;
    let mut b = [0u8; 32]; b[0] = 5;
    let mut c = [0u8; 32]; c[0] = 99; // wrong!

    let prep = uint256_arith::make_plus_256_row(400, &a, &b, &c);
    // Use the correct carries for the WRONG result — still should fail
    // because a+b+carry-c-carry_out*256 ≠ 0
    let carries = uint256_arith::compute_addition_carries(&a, &b);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}

// ---------------------------------------------------------------------------
// Soundness: wrong increment result → STARK rejection
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_uint256_inc_wrong_result_fails() {
    let mut a = [0u8; 32]; a[0] = 5;
    let mut c = [0u8; 32]; c[0] = 99; // wrong! should be 6

    let prep = uint256_arith::make_inc_256_row(401, &a, &c);
    let carries = uint256_arith::compute_increment_carries(&a);
    let main = uint256_arith::make_main_row(1, &carries);

    prove_uint256(vec![prep], vec![main]);
}
