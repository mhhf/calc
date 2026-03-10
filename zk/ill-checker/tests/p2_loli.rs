//! Phase 2: Linear implication (loli) tests.
//!
//! Tests loli_r (right intro) and loli_l (left focus).
//! Validates context manipulation (loli_r adds to context) and
//! obligation splitting (loli_l creates two sub-obligations).

mod common;

use std::sync::Arc;

use ill_checker::{
    chips::{formula_rom::FormulaRomAir, init::InitChip},
    rule::{ill, RuleChip},
    tags,
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

// Hash constants
const H_A: u32 = 42;
const H_B: u32 = 99;
const H_A_LOLI_B: u32 = 150; // hash(A ⊸ B)

// ---------------------------------------------------------------------------
// loli_r: A ⊢ A ⊸ B is NOT provable (can't prove B from A alone)
// loli_r: B ⊢ A ⊸ B — adds A to context, prove B from A, B ... wait
// Actually: A ⊸ B, A ⊢ B is the standard test for loli_l
// And: A, B ⊢ A ⊸ B is not directly provable with loli_r...
//
// Let's use: B ⊢ A ⊸ B
// Proof: loli_r(id(B)) — consume oblig for A⊸B, add A to context, prove B
// Wait, loli_r adds child0 (A) to context and changes goal to child1 (B).
// So we need B in context to prove B. Starting context has B.
// After loli_r: context has B, A; goal is B. Then id(B) consumes B.
// But A is left unconsumed! Bus imbalance.
//
// Better test: ⊢ A ⊸ A
// Proof: loli_r(id(A)) — add A to context, prove A from A. Yes!
// ---------------------------------------------------------------------------

const H_A_LOLI_A: u32 = 160; // hash(A ⊸ A)

#[test]
fn p2_loli_r_basic() {
    // ⊢ A ⊸ A
    // Proof: loli_r(id(A))
    // loli_r: consume oblig (0, A⊸A, 0), add A to context, produce oblig (1, A, 0)
    // id: consume oblig (1, A, 0), consume A from context

    let loli_r_chip = RuleChip::new(ill::loli_r());
    let id_chip = RuleChip::new(ill::id());
    // loli_r layout: [active=0, hash=1, c0=2, c1=3, nonce_in=4, lax=5, nonce_out0=6]
    assert_eq!(loli_r_chip.layout.width, 7);

    // Init: no context, oblig=(0, A⊸A, 0)
    let init_trace = padded_trace(
        &[[0, 0, H_A_LOLI_A, 1, 0, 0]],
        4,
    );

    // loli_r: [active, hash, c0, c1, nonce_in, lax, nonce_out0]
    let loli_r_trace = dyn_trace(
        &[&[1, H_A_LOLI_A, H_A, H_A, 0, 0, 1]],
        7, 4,
    );

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    // ROM: A ⊸ A decomposes as (A, A)
    let rom_trace = padded_trace(
        &[[H_A_LOLI_A, tags::LOLI, H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(loli_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, loli_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("loli_r: ⊢ A ⊸ A");
}

// ---------------------------------------------------------------------------
// loli_l: A ⊸ B, A ⊢ B
// ---------------------------------------------------------------------------

#[test]
fn p2_loli_l_basic() {
    // A ⊸ B, A ⊢ B
    // Proof: loli_l(A⊸B, id(A), id(B))
    //
    // loli_l: consume oblig (0, B, 0), consume A⊸B from context,
    //         produce oblig (1, A, 0) (premise 0: prove A),
    //         add B to context,
    //         produce oblig (2, B, 0) (premise 1: prove B with B in context)
    // id(A): consume oblig (1, A, 0), consume A from context
    // id(B): consume oblig (2, B, 0), consume B from context

    let loli_l_chip = RuleChip::new(ill::loli_l());
    let id_chip = RuleChip::new(ill::id());

    // loli_l layout: [active=0, hash=1, c0=2, c1=3, nonce_in=4, lax=5, nonce_out0=6, nonce_out1=7, goal=8]
    assert_eq!(loli_l_chip.layout.width, 9);

    // Init: ctx = A⊸B, A; oblig = (0, B, 0)
    let init_trace = padded_trace(
        &[
            [H_A_LOLI_B, 1, H_B, 1, 0, 0], // ctx=A⊸B, oblig=(0, B, 0)
            [H_A, 1, 0, 0, 0, 0],            // ctx=A
        ],
        4,
    );

    // loli_l: [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1, goal]
    let loli_l_trace = dyn_trace(
        &[&[1, H_A_LOLI_B, H_A, H_B, 0, 0, 1, 2, H_B]],
        9, 4,
    );

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_B, 2, 0]],
        4, 4,
    );

    // ROM: A ⊸ B
    let rom_trace = padded_trace(
        &[[H_A_LOLI_B, tags::LOLI, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(loli_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, loli_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("loli_l: A ⊸ B, A ⊢ B");
}

#[test]
#[should_panic]
fn p2_loli_l_wrong_goal_fails() {
    // loli_l with mismatched goal — obligation type doesn't match
    let loli_l_chip = RuleChip::new(ill::loli_l());
    let id_chip = RuleChip::new(ill::id());

    let init_trace = padded_trace(
        &[
            [H_A_LOLI_B, 1, H_B, 1, 0, 0],
            [H_A, 1, 0, 0, 0, 0],
        ],
        4,
    );

    // WRONG: goal=H_A instead of H_B
    let loli_l_trace = dyn_trace(
        &[&[1, H_A_LOLI_B, H_A, H_B, 0, 0, 1, 2, H_A]],
        9, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_A, 1, 0], &[1, H_B, 2, 0]],
        4, 4,
    );

    let rom_trace = padded_trace(
        &[[H_A_LOLI_B, tags::LOLI, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(loli_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, loli_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong goal in loli_l");
}
