//! Phase 2: Unit and zero rule tests.
//!
//! Tests one_r (⊢ I), one_l (A ⊗ I ⊢ A), and zero_l (0 ⊢ B).
//! Validates nullary connective handling (arity=0, child0=child1=0 in ROM).
//! Also validates ZeroLChip + DiscardChip with DISCARD_BUS.

mod common;

use std::sync::Arc;

use ill_checker::{
    chips::{
        discard::DiscardChip,
        formula_rom::FormulaRomAir,
        init::InitChip,
        zero_l::ZeroLChip,
    },
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
const H_ONE: u32 = 1000;  // hash of the unit formula I
const H_ZERO: u32 = 2000; // hash of the zero formula 0
const H_A_TENSOR_ONE: u32 = 1001; // hash(A ⊗ I)

// ---------------------------------------------------------------------------
// one_r: ⊢ I
// ---------------------------------------------------------------------------

#[test]
fn p2_one_r_basic() {
    // ⊢ I
    // Proof: one_r
    // one_r: consume oblig (0, I, 0), formula lookup (I, ONE, 0, 0)

    let one_r_chip = RuleChip::new(ill::ONE_R);
    // one_r layout: [active=0, hash=1, nonce_in=2, lax=3]
    assert_eq!(one_r_chip.layout.width, 4);

    // Init: no context, oblig=(0, I, 0)
    let init_trace = padded_trace(&[[0, 0, H_ONE, 1, 0, 0]], 4);

    // one_r: [active, hash, nonce_in, lax]
    let one_r_trace = dyn_trace(&[&[1, H_ONE, 0, 0]], 4, 4);

    // ROM: I is a nullary connective (tag=ONE, children=0,0)
    let rom_trace = padded_trace(&[[H_ONE, tags::ONE, 0, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(one_r_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, one_r_trace, rom_trace],
        vec![vec![], vec![], vec![]],
    )
    .expect("one_r: ⊢ I");
}

// ---------------------------------------------------------------------------
// one_l + tensor_l: A ⊗ I ⊢ A
// ---------------------------------------------------------------------------

#[test]
fn p2_tensor_one_left() {
    // A ⊗ I ⊢ A
    // Proof: tensor_l(one_l, id(A))
    //   tensor_l: ctx receive A⊗I, ctx send A, ctx send I
    //   one_l:    ctx receive I (removed)
    //   id:       oblig receive (0, A, 0), ctx receive A

    let tensor_l_chip = RuleChip::new(ill::TENSOR_L);
    let one_l_chip = RuleChip::new(ill::ONE_L);
    let id_chip = RuleChip::new(ill::ID);

    // one_l layout: [active=0, hash=1] width=2
    assert_eq!(one_l_chip.layout.width, 2);

    // Init: ctx=A⊗I, oblig=(0, A, 0)
    let init_trace = padded_trace(&[[H_A_TENSOR_ONE, 1, H_A, 1, 0, 0]], 4);

    // tensor_l: [active, hash, c0, c1]
    let tl_trace = dyn_trace(&[&[1, H_A_TENSOR_ONE, H_A, H_ONE]], 4, 4);

    // one_l: [active, hash]
    let one_l_trace = dyn_trace(&[&[1, H_ONE]], 2, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // ROM: A⊗I and I
    let rom_trace = padded_trace(
        &[
            [H_A_TENSOR_ONE, tags::TENSOR, H_A, H_ONE, 1, 1],
            [H_ONE, tags::ONE, 0, 0, 1, 1],
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(tensor_l_chip) as AirRef<_>,
            Arc::new(one_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tl_trace, one_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("one_l: A ⊗ I ⊢ A");
}

// ---------------------------------------------------------------------------
// zero_l: 0 ⊢ B (no extra context to discard)
// ---------------------------------------------------------------------------

#[test]
fn p2_zero_l_simple() {
    // 0 ⊢ B
    // Proof: zero_l
    // zero_l: oblig receive (0, B, 0), ctx receive 0, formula lookup

    // Init: ctx=0, oblig=(0, B, 0)
    let init_trace = padded_trace(&[[H_ZERO, 1, H_B, 1, 0, 0]], 4);

    // ZeroLChip: [hash, is_active, nonce_in, lax, goal, num_discards]
    let zero_l_trace = padded_trace(
        &[[H_ZERO, 1, 0, 0, H_B, 0]], // num_discards=0
        4,
    );

    // ROM: 0 is a nullary connective
    let rom_trace = padded_trace(&[[H_ZERO, tags::ZERO, 0, 0, 1, 1]], 4);

    // No DiscardChip needed (no extra context)
    let discard_trace = padded_trace::<3>(&[], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(ZeroLChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
            Arc::new(DiscardChip) as AirRef<_>,
        ],
        vec![init_trace, zero_l_trace, rom_trace, discard_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("zero_l: 0 ⊢ B");
}

// ---------------------------------------------------------------------------
// zero_l: 0, A ⊢ B (discard A)
// ---------------------------------------------------------------------------

#[test]
fn p2_zero_l_with_discard() {
    // 0, A ⊢ B
    // Proof: zero_l (discards A)
    //   zero_l: oblig receive (0, B, 0), ctx receive 0, formula lookup,
    //           discard_bus provide nonce=0 with num_discards=1
    //   discard: ctx receive A, discard_bus lookup permit=0

    let init_trace = padded_trace(
        &[
            [H_ZERO, 1, H_B, 1, 0, 0], // ctx=0, oblig=(0, B, 0)
            [H_A, 1, 0, 0, 0, 0],       // ctx=A
        ],
        4,
    );

    // ZeroLChip: [hash, is_active, nonce_in, lax, goal, num_discards]
    let zero_l_trace = padded_trace(
        &[[H_ZERO, 1, 0, 0, H_B, 1]], // num_discards=1
        4,
    );

    // DiscardChip: [hash, is_active, permit]
    let discard_trace = padded_trace(
        &[[H_A, 1, 0]], // discard A, permit=0 (matches zero_l nonce)
        4,
    );

    let rom_trace = padded_trace(&[[H_ZERO, tags::ZERO, 0, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(ZeroLChip) as AirRef<_>,
            Arc::new(DiscardChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, zero_l_trace, discard_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("zero_l: 0, A ⊢ B with discard");
}

// ---------------------------------------------------------------------------
// Failure: discard without zero_l
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_discard_without_zero_l_fails() {
    // Try to discard A without zero_l — DISCARD_BUS unbalanced
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    let id_chip = RuleChip::new(ill::ID);
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // Try to discard B without any zero_l authorization
    let discard_trace = padded_trace(&[[H_B, 1, 99]], 4); // bogus permit

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(DiscardChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace, discard_trace],
        vec![vec![], vec![], vec![]],
    )
    .expect("should fail: unauthorized discard");
}

// ---------------------------------------------------------------------------
// Failure: one_r with non-empty context
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_one_r_nonempty_context_fails() {
    // A ⊢ I — should fail because A is unconsumed (bus imbalance)
    let one_r_chip = RuleChip::new(ill::ONE_R);

    let init_trace = padded_trace(
        &[[H_A, 1, H_ONE, 1, 0, 0]], // ctx=A, oblig=(0, I, 0)
        4,
    );

    let one_r_trace = dyn_trace(&[&[1, H_ONE, 0, 0]], 4, 4);
    let rom_trace = padded_trace(&[[H_ONE, tags::ONE, 0, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(one_r_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, one_r_trace, rom_trace],
        vec![vec![], vec![], vec![]],
    )
    .expect("should fail: one_r with non-empty context");
}
