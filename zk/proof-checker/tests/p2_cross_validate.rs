//! Phase 2 cross-validation: same proofs as Phase 1, using generic RuleChip.
//!
//! Proves the same sequents as p1b/p1c/p1d but with RuleChip instead of
//! hand-written chips. Validates that the generic chip produces identical
//! bus interactions.

mod common;

use std::sync::Arc;

use proof_checker::{
    chips::dup::DupChip,
    rule::RuleChip,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::{make_init, make_formula_rom};

// Hash constants
const H_A: u32 = 42;
const H_B: u32 = 99;
const H_A_TENSOR_B: u32 = 100;
const H_B_TENSOR_A: u32 = 200;
const H_A_WITH_A: u32 = 300;

/// Helper: build a dynamic-width trace from rows given as slices.
fn dyn_trace(rows: &[&[u32]], width: usize, min_rows: usize) -> openvm_stark_backend::p3_matrix::dense::RowMajorMatrix<p3_baby_bear::BabyBear> {
    use p3_field::PrimeCharacteristicRing;
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * width);
    for row in rows {
        assert_eq!(row.len(), width, "row width mismatch");
        for &v in *row {
            data.push(p3_baby_bear::BabyBear::from_u32(v));
        }
    }
    for _ in rows.len()..n {
        for _ in 0..width {
            data.push(p3_baby_bear::BabyBear::ZERO);
        }
    }
    openvm_stark_backend::p3_matrix::dense::RowMajorMatrix::new(data, width)
}

// ---------------------------------------------------------------------------
// Cross-validate: A ⊢ A (identity, same as p1b)
// ---------------------------------------------------------------------------

#[test]
fn p2_xval_identity() {
    let (_tags, specs) = common::load_test_specs();
    // A ⊢ A using generic RuleChip(ID)
    let id_chip = RuleChip::new(specs["id"].clone());
    let id_w = id_chip.layout.width;
    // Layout: [active=0, hash=1, nonce_in=2, lax=3]
    assert_eq!(id_w, 4);

    // InitChip: [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
    let (init_chip, init_trace, init_pis) = make_init(&[[H_A, 1, H_A, 1, 0, 0]], 4);

    // RuleChip(ID): [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], id_w, 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![init_pis, vec![]],
    )
    .expect("cross-validate: A ⊢ A with generic ID");
}

// ---------------------------------------------------------------------------
// Cross-validate: A, B ⊢ A ⊗ B (same as p1c)
// ---------------------------------------------------------------------------

#[test]
fn p2_xval_tensor_r() {
    let (tags, specs) = common::load_test_specs();
    let tr_chip = RuleChip::new(specs["tensor_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());
    // tensor_r layout: [active=0, hash=1, c0=2, c1=3, nonce_in=4, lax=5, nonce_out0=6, nonce_out1=7]
    assert_eq!(tr_chip.layout.width, 8);

    let (init_chip, init_trace, init_pis) = make_init(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    // RuleChip(TENSOR_R): [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1]
    let tr_trace = dyn_trace(
        &[&[1, H_A_TENSOR_B, H_A, H_B, 0, 0, 1, 2]],
        8, 4,
    );

    // RuleChip(ID): [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_B, 2, 0]],
        4, 4,
    );

    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_A_TENSOR_B, tags["tensor"], H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(tr_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, tr_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![]],
    )
    .expect("cross-validate: A, B ⊢ A ⊗ B with generic chips");
}

// ---------------------------------------------------------------------------
// Cross-validate: A ⊗ B ⊢ B ⊗ A (same as p1d)
// ---------------------------------------------------------------------------

#[test]
fn p2_xval_tensor_swap() {
    let (tags, specs) = common::load_test_specs();
    let tl_chip = RuleChip::new(specs["tensor_l"].clone());
    let tr_chip = RuleChip::new(specs["tensor_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // tensor_l layout: [active=0, hash=1, c0=2, c1=3] width=4
    assert_eq!(tl_chip.layout.width, 4);

    let (init_chip, init_trace, init_pis) = make_init(
        &[[H_A_TENSOR_B, 1, H_B_TENSOR_A, 1, 0, 0]],
        4,
    );

    // RuleChip(TENSOR_L): [active, hash, c0, c1]
    let tl_trace = dyn_trace(&[&[1, H_A_TENSOR_B, H_A, H_B]], 4, 4);

    // RuleChip(TENSOR_R): [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1]
    let tr_trace = dyn_trace(
        &[&[1, H_B_TENSOR_A, H_B, H_A, 0, 0, 1, 2]],
        8, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_B, 1, 0], &[1, H_A, 2, 0]],
        4, 4,
    );

    let (rom_chip, rom_trace) = make_formula_rom(
        &[
            [H_A_TENSOR_B, tags["tensor"], H_A, H_B, 1, 1],
            [H_B_TENSOR_A, tags["tensor"], H_B, H_A, 1, 1],
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(tl_chip) as AirRef<_>,
            Arc::new(tr_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, tl_trace, tr_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![], vec![]],
    )
    .expect("cross-validate: A ⊗ B ⊢ B ⊗ A with generic chips");
}

// ---------------------------------------------------------------------------
// Cross-validate: A ⊢ A & A (same as p1d)
// ---------------------------------------------------------------------------

#[test]
fn p2_xval_with_r() {
    let (tags, specs) = common::load_test_specs();
    let wr_chip = RuleChip::new(specs["with_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // with_r has same layout as tensor_r (both are binary right rules)
    assert_eq!(wr_chip.layout.width, 8);

    let (init_chip, init_trace, init_pis) = make_init(&[[H_A, 1, H_A_WITH_A, 1, 0, 0]], 4);
    let dup_trace = common::padded_trace(&[[H_A, 1]], 4);

    // RuleChip(WITH_R): [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1]
    let wr_trace = dyn_trace(
        &[&[1, H_A_WITH_A, H_A, H_A, 0, 0, 1, 2]],
        8, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_A, 2, 0]],
        4, 4,
    );

    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_A_WITH_A, tags["with"], H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(DupChip) as AirRef<_>,
            Arc::new(wr_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, dup_trace, wr_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![], vec![]],
    )
    .expect("cross-validate: A ⊢ A & A with generic chips");
}
