//! Phase 2: Additive disjunction (oplus) tests.
//!
//! Tests oplus_r1, oplus_r2 (injection), and oplus_l (case analysis).
//! Validates: unary right rules with different child selection,
//! and left branching with context duplication + inherited goal.

mod common;

use std::sync::Arc;

use proof_checker::rule::RuleChip;
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::{make_init, make_formula_rom};

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
const H_A_OPLUS_B: u32 = 400;
const H_B_OPLUS_A: u32 = 401;

// ---------------------------------------------------------------------------
// A ⊕ B ⊢ B ⊕ A (full oplus_l + oplus_r1/r2 test)
// ---------------------------------------------------------------------------

#[test]
fn p2_oplus_swap() {
    let (tags, specs) = common::load_test_specs();
    let oplus_l_chip = RuleChip::new(specs["oplus_l"].clone());
    let oplus_r2_chip = RuleChip::new(specs["oplus_r2"].clone());
    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    assert_eq!(oplus_l_chip.layout.width, 9);
    assert_eq!(oplus_r1_chip.layout.width, 7);

    let (init_chip, init_trace) = make_init(
        &[[H_A_OPLUS_B, 1, H_B_OPLUS_A, 1, 0, 0]],
        4,
    );

    let oplus_l_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1, 2, H_B_OPLUS_A]],
        9, 4,
    );

    let oplus_r2_trace = dyn_trace(
        &[&[1, H_B_OPLUS_A, H_B, H_A, 1, 0, 3]],
        7, 4,
    );

    let oplus_r1_trace = dyn_trace(
        &[&[1, H_B_OPLUS_A, H_B, H_A, 2, 0, 4]],
        7, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_A, 3, 0], &[1, H_B, 4, 0]],
        4, 4,
    );

    // ROM: A⊕B and B⊕A (B⊕A looked up twice: by oplus_r2 and oplus_r1)
    let (rom_chip, rom_trace) = make_formula_rom(
        &[
            [H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1],
            [H_B_OPLUS_A, tags["oplus"], H_B, H_A, 1, 2], // looked up 2×
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(oplus_l_chip) as AirRef<_>,
            Arc::new(oplus_r2_chip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, oplus_l_trace, oplus_r2_trace, oplus_r1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("oplus: A ⊕ B ⊢ B ⊕ A");
}

// ---------------------------------------------------------------------------
// Simple injection: A ⊢ A ⊕ B
// ---------------------------------------------------------------------------

#[test]
fn p2_oplus_r1_simple() {
    let (tags, specs) = common::load_test_specs();
    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let (init_chip, init_trace) = make_init(&[[H_A, 1, H_A_OPLUS_B, 1, 0, 0]], 4);

    let oplus_r1_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1]],
        7, 4,
    );

    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, oplus_r1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("oplus_r1: A ⊢ A ⊕ B");
}

// ---------------------------------------------------------------------------
// Failure: oplus_r1 but trying to prove wrong child
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_oplus_r1_wrong_child_fails() {
    let (tags, specs) = common::load_test_specs();
    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let (init_chip, init_trace) = make_init(&[[H_B, 1, H_A_OPLUS_B, 1, 0, 0]], 4);

    let oplus_r1_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1]],
        7, 4,
    );

    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, oplus_r1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong injection in oplus_r1");
}
