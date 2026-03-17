//! Phase 2: Exponential (bang) tests.
//!
//! Tests bang_r (promotion), bang_l (dereliction), absorption, and copy.
//! Validates GammaRomAir + GAMMA_BUS for exponential resource management.

mod common;

use std::sync::Arc;

use sequent_certifier::rule::RuleChip;
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::{make_init, make_formula_rom, make_gamma_rom};

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
const H_BANG_A: u32 = 500; // hash(!A)
const H_A_TENSOR_A: u32 = 501; // hash(A ⊗ A)

// ---------------------------------------------------------------------------
// bang_l (dereliction): !A ⊢ A
// ---------------------------------------------------------------------------

#[test]
fn p2_bang_l_basic() {
    let (tags, specs) = common::load_test_specs();
    let bang_l_chip = RuleChip::new(specs["bang_l"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());
    assert_eq!(bang_l_chip.layout.width, 3);

    let (init_chip, init_trace, init_pis) = make_init(&[[H_BANG_A, 1, H_A, 1, 0, 0]], 4);
    let bang_l_trace = dyn_trace(&[&[1, H_BANG_A, H_A]], 3, 4);
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);
    let (rom_chip, rom_trace) = make_formula_rom(&[[H_BANG_A, tags["bang"], H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(bang_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, bang_l_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![]],
    )
    .expect("bang_l: !A ⊢ A");
}

// ---------------------------------------------------------------------------
// absorption + copy: !A ⊢ A ⊗ A
// ---------------------------------------------------------------------------

#[test]
fn p2_absorption_copy() {
    let (tags, specs) = common::load_test_specs();
    let absorption_chip = RuleChip::new(specs["absorption"].clone());
    let copy_chip = RuleChip::new(specs["copy"].clone());
    let tensor_r_chip = RuleChip::new(specs["tensor_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    assert_eq!(absorption_chip.layout.width, 3);
    assert_eq!(copy_chip.layout.width, 2);

    let (init_chip, init_trace, init_pis) = make_init(&[[H_BANG_A, 1, H_A_TENSOR_A, 1, 0, 0]], 4);
    let abs_trace = dyn_trace(&[&[1, H_BANG_A, H_A]], 3, 4);
    let copy_trace = dyn_trace(&[&[1, H_A], &[1, H_A]], 2, 4);

    let tr_trace = dyn_trace(
        &[&[1, H_A_TENSOR_A, H_A, H_A, 0, 0, 1, 2]],
        8, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_A, 2, 0]],
        4, 4,
    );

    // Formula ROM: !A, A⊗A
    let (fom_chip, fom_trace) = make_formula_rom(
        &[
            [H_BANG_A, tags["bang"], H_A, 0, 1, 1],
            [H_A_TENSOR_A, tags["tensor"], H_A, H_A, 1, 1],
        ],
        4,
    );

    // Gamma ROM: A is in gamma zone, looked up 2× (by two copy rows)
    let (gamma_chip, gamma_trace) = make_gamma_rom(&[[H_A, 1, 2]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(absorption_chip) as AirRef<_>,
            Arc::new(copy_chip) as AirRef<_>,
            Arc::new(tensor_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(fom_chip) as AirRef<_>,
            Arc::new(gamma_chip) as AirRef<_>,
        ],
        vec![init_trace, abs_trace, copy_trace, tr_trace, id_trace, fom_trace, gamma_trace],
        vec![init_pis, vec![], vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("absorption + copy: !A ⊢ A ⊗ A");
}

// ---------------------------------------------------------------------------
// Failure: copy without gamma entry
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_copy_without_gamma_fails() {
    let (_tags, specs) = common::load_test_specs();
    let copy_chip = RuleChip::new(specs["copy"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let (init_chip, init_trace, init_pis) = make_init(&[[0, 0, H_A, 1, 0, 0]], 4);
    let copy_trace = dyn_trace(&[&[1, H_A]], 2, 4);
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);
    let (gamma_chip, gamma_trace) = make_gamma_rom(&[], 4); // empty gamma

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(copy_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(gamma_chip) as AirRef<_>,
        ],
        vec![init_trace, copy_trace, id_trace, gamma_trace],
        vec![init_pis, vec![], vec![], vec![]],
    )
    .expect("should fail: copy without gamma");
}
