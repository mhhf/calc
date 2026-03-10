//! Phase 2: Additive conjunction left rules (with_l1, with_l2).
//!
//! Tests left projection: extracting first or second component from A & B.

mod common;

use std::sync::Arc;

use proof_checker::{
    chips::{formula_rom::FormulaRomAir, init::InitChip},
    rule::RuleChip,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::padded_trace;

fn dyn_trace(rows: &[&[u32]], width: usize, min_rows: usize) -> openvm_stark_backend::p3_matrix::dense::RowMajorMatrix<p3_baby_bear::BabyBear> {
    use p3_field::PrimeCharacteristicRing;
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * width);
    for row in rows {
        assert_eq!(row.len(), width);
        for &v in *row { data.push(p3_baby_bear::BabyBear::from_u32(v)); }
    }
    for _ in rows.len()..n {
        for _ in 0..width { data.push(p3_baby_bear::BabyBear::ZERO); }
    }
    openvm_stark_backend::p3_matrix::dense::RowMajorMatrix::new(data, width)
}

const H_A: u32 = 42;
const H_B: u32 = 99;
const H_A_WITH_B: u32 = 300; // hash(A & B)

// ---------------------------------------------------------------------------
// with_l1: A & B ⊢ A (first projection)
// ---------------------------------------------------------------------------

#[test]
fn p2_with_l1_basic() {
    let (tags, specs) = common::load_test_specs();
    // A & B ⊢ A
    // Proof: with_l1(A&B, id(A))
    //   with_l1: ctx receive A&B, ctx send A (child0), formula lookup
    //   id:      oblig receive (0, A, 0), ctx receive A

    let with_l1_chip = RuleChip::new(specs["with_l1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // with_l1 layout: [active=0, hash=1, c0=2, c1=3] width=4
    assert_eq!(with_l1_chip.layout.width, 4);

    let init_trace = padded_trace(&[[H_A_WITH_B, 1, H_A, 1, 0, 0]], 4);

    // with_l1: [active, hash, c0, c1]
    let wl1_trace = dyn_trace(&[&[1, H_A_WITH_B, H_A, H_B]], 4, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // ROM: A & B
    let rom_trace = padded_trace(&[[H_A_WITH_B, tags["with"], H_A, H_B, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(with_l1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, wl1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("with_l1: A & B ⊢ A");
}

// ---------------------------------------------------------------------------
// with_l2: A & B ⊢ B (second projection)
// ---------------------------------------------------------------------------

#[test]
fn p2_with_l2_basic() {
    let (tags, specs) = common::load_test_specs();
    // A & B ⊢ B
    // Proof: with_l2(A&B, id(B))
    //   with_l2: ctx receive A&B, ctx send B (child1), formula lookup
    //   id:      oblig receive (0, B, 0), ctx receive B

    let with_l2_chip = RuleChip::new(specs["with_l2"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // with_l2 layout: [active=0, hash=1, c0=2, c1=3] width=4
    assert_eq!(with_l2_chip.layout.width, 4);

    let init_trace = padded_trace(&[[H_A_WITH_B, 1, H_B, 1, 0, 0]], 4);

    // with_l2: [active, hash, c0, c1]
    let wl2_trace = dyn_trace(&[&[1, H_A_WITH_B, H_A, H_B]], 4, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_B, 0, 0]], 4, 4);

    // ROM: A & B
    let rom_trace = padded_trace(&[[H_A_WITH_B, tags["with"], H_A, H_B, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(with_l2_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, wl2_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("with_l2: A & B ⊢ B");
}

// ---------------------------------------------------------------------------
// Failure: with_l1 sends wrong child
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_with_l1_wrong_projection_fails() {
    let (tags, specs) = common::load_test_specs();
    // with_l1 should send child0=A, but id expects B — bus imbalance
    let with_l1_chip = RuleChip::new(specs["with_l1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // Init: ctx=A&B, oblig=(0, B, 0) — expect B but with_l1 provides A
    let init_trace = padded_trace(&[[H_A_WITH_B, 1, H_B, 1, 0, 0]], 4);
    let wl1_trace = dyn_trace(&[&[1, H_A_WITH_B, H_A, H_B]], 4, 4);

    // id consumes A (what with_l1 provides), but obligation says B
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    let rom_trace = padded_trace(&[[H_A_WITH_B, tags["with"], H_A, H_B, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(with_l1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, wl1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: with_l1 wrong projection");
}
