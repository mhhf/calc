//! Phase 2: Exponential (bang) tests.
//!
//! Tests bang_r (promotion), bang_l (dereliction), absorption, and copy.
//! Validates GammaRomAir + GAMMA_BUS for exponential resource management.

mod common;

use std::sync::Arc;

use proof_checker::{
    chips::{
        formula_rom::FormulaRomAir,
        gamma_rom::GammaRomAir,
        init::InitChip,
    },
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
const H_BANG_A: u32 = 500; // hash(!A)
const H_A_TENSOR_A: u32 = 501; // hash(A ⊗ A)

// ---------------------------------------------------------------------------
// bang_l (dereliction): !A ⊢ A
// ---------------------------------------------------------------------------

#[test]
fn p2_bang_l_basic() {
    let (tags, specs) = common::load_test_specs();
    // !A ⊢ A
    // Proof: bang_l(!A, id(A))
    //   bang_l: ctx receive !A, ctx send A, formula lookup
    //   id: oblig receive (0, A, 0), ctx receive A

    let bang_l_chip = RuleChip::new(specs["bang_l"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // bang_l layout: [active=0, hash=1, child0=2] width=3
    assert_eq!(bang_l_chip.layout.width, 3);

    let init_trace = padded_trace(&[[H_BANG_A, 1, H_A, 1, 0, 0]], 4);

    // bang_l: [active, hash, child0]
    let bang_l_trace = dyn_trace(&[&[1, H_BANG_A, H_A]], 3, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // ROM: !A
    let rom_trace = padded_trace(&[[H_BANG_A, tags["bang"], H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(bang_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, bang_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("bang_l: !A ⊢ A");
}

// ---------------------------------------------------------------------------
// absorption + copy: !A ⊢ A ⊗ A
// ---------------------------------------------------------------------------

#[test]
fn p2_absorption_copy() {
    let (tags, specs) = common::load_test_specs();
    // !A ⊢ A ⊗ A
    // Proof: absorption(!A), copy(A), copy(A), tensor_r(id(A), id(A))
    //
    // Bus flow:
    //   Init:       ctx=!A, oblig=(0, A⊗A, 0)
    //   absorption: ctx receive !A, formula lookup (!A, BANG, A, 0)
    //               [A goes to gamma zone — GammaRom provides]
    //   copy×2:     gamma lookup A, ctx send A (twice)
    //   tensor_r:   oblig receive (0, A⊗A, 0), oblig send (1, A, 0), (2, A, 0),
    //               formula lookup
    //   id×2:       consume obligations and context

    let absorption_chip = RuleChip::new(specs["absorption"].clone());
    let copy_chip = RuleChip::new(specs["copy"].clone());
    let tensor_r_chip = RuleChip::new(specs["tensor_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // absorption layout: [active=0, hash=1, child0=2] width=3
    assert_eq!(absorption_chip.layout.width, 3);
    // copy layout: [active=0, hash=1] width=2
    assert_eq!(copy_chip.layout.width, 2);

    let init_trace = padded_trace(&[[H_BANG_A, 1, H_A_TENSOR_A, 1, 0, 0]], 4);

    // absorption: [active, hash, child0]
    let abs_trace = dyn_trace(&[&[1, H_BANG_A, H_A]], 3, 4);

    // copy: [active, hash] — two copies of A
    let copy_trace = dyn_trace(&[&[1, H_A], &[1, H_A]], 2, 4);

    // tensor_r: [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1]
    let tr_trace = dyn_trace(
        &[&[1, H_A_TENSOR_A, H_A, H_A, 0, 0, 1, 2]],
        8, 4,
    );

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_A, 2, 0]],
        4, 4,
    );

    // Formula ROM: !A, A⊗A
    let fom_trace = padded_trace(
        &[
            [H_BANG_A, tags["bang"], H_A, 0, 1, 1],
            [H_A_TENSOR_A, tags["tensor"], H_A, H_A, 1, 1],
        ],
        4,
    );

    // Gamma ROM: A is in gamma zone, looked up 2× (by two copy rows)
    let gamma_trace = padded_trace(&[[H_A, 1, 2]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(absorption_chip) as AirRef<_>,
            Arc::new(copy_chip) as AirRef<_>,
            Arc::new(tensor_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
            Arc::new(GammaRomAir) as AirRef<_>,
        ],
        vec![init_trace, abs_trace, copy_trace, tr_trace, id_trace, fom_trace, gamma_trace],
        vec![vec![], vec![], vec![], vec![], vec![], vec![], vec![]],
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
    // Try to copy A without it being in gamma — GAMMA_BUS unbalanced
    let copy_chip = RuleChip::new(specs["copy"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // No absorption, no gamma entry, but try to copy
    let init_trace = padded_trace(&[[0, 0, H_A, 1, 0, 0]], 4);
    let copy_trace = dyn_trace(&[&[1, H_A]], 2, 4);
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);
    let gamma_trace = padded_trace::<3>(&[], 4); // empty gamma

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(copy_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(GammaRomAir) as AirRef<_>,
        ],
        vec![init_trace, copy_trace, id_trace, gamma_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: copy without gamma");
}
