//! Phase 2: Additive disjunction (oplus) tests.
//!
//! Tests oplus_r1, oplus_r2 (injection), and oplus_l (case analysis).
//! Validates: unary right rules with different child selection,
//! and left branching with context duplication + inherited goal.

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
const H_A_OPLUS_B: u32 = 400;
const H_B_OPLUS_A: u32 = 401;

// ---------------------------------------------------------------------------
// A ⊕ B ⊢ B ⊕ A (full oplus_l + oplus_r1/r2 test)
// ---------------------------------------------------------------------------

#[test]
fn p2_oplus_swap() {
    let (tags, specs) = common::load_test_specs();
    // A ⊕ B ⊢ B ⊕ A
    // Proof: oplus_l(A⊕B, oplus_r2(id(A)), oplus_r1(id(B)))
    //
    // Bus flow:
    //   Init:     ctx=A⊕B, oblig=(0, B⊕A, 0)
    //   Dup:      duplicate A⊕B (wait, no — oplus_l consumes A⊕B from ctx)
    //   oplus_l:  oblig receive (0, B⊕A, 0), ctx receive A⊕B,
    //             ctx send A (branch 1), ctx send B (branch 2),
    //             oblig send (1, B⊕A, 0), oblig send (2, B⊕A, 0),
    //             formula lookup
    //   oplus_r2: oblig receive (1, B⊕A, 0), oblig send (3, A, 0),
    //             formula lookup (B⊕A, OPLUS, B, A)
    //   oplus_r1: oblig receive (2, B⊕A, 0), oblig send (4, B, 0),
    //             formula lookup (B⊕A, OPLUS, B, A)
    //   id(A):    oblig receive (3, A, 0), ctx receive A
    //   id(B):    oblig receive (4, B, 0), ctx receive B

    let oplus_l_chip = RuleChip::new(specs["oplus_l"].clone());
    let oplus_r2_chip = RuleChip::new(specs["oplus_r2"].clone());
    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // oplus_l: [active=0, hash=1, c0=2, c1=3, nonce_in=4, lax=5, nonce_out0=6, nonce_out1=7, goal=8]
    assert_eq!(oplus_l_chip.layout.width, 9);
    // oplus_r1/r2: [active=0, hash=1, c0=2, c1=3, nonce_in=4, lax=5, nonce_out0=6]
    assert_eq!(oplus_r1_chip.layout.width, 7);

    let init_trace = padded_trace(
        &[[H_A_OPLUS_B, 1, H_B_OPLUS_A, 1, 0, 0]],
        4,
    );

    // oplus_l: [active, hash, c0, c1, nonce_in, lax, nonce_out0, nonce_out1, goal]
    let oplus_l_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1, 2, H_B_OPLUS_A]],
        9, 4,
    );

    // oplus_r2 (branch 1: prove B⊕A by injecting A): [active, hash, c0, c1, nonce_in, lax, nonce_out0]
    // oplus_r2 selects child1 (A in B⊕A) — wait, B⊕A has children (B, A).
    // oplus_r2 sends child1 = A.
    let oplus_r2_trace = dyn_trace(
        &[&[1, H_B_OPLUS_A, H_B, H_A, 1, 0, 3]],
        7, 4,
    );

    // oplus_r1 (branch 2: prove B⊕A by injecting B): sends child0 = B
    let oplus_r1_trace = dyn_trace(
        &[&[1, H_B_OPLUS_A, H_B, H_A, 2, 0, 4]],
        7, 4,
    );

    let id_trace = dyn_trace(
        &[&[1, H_A, 3, 0], &[1, H_B, 4, 0]],
        4, 4,
    );

    // ROM: A⊕B and B⊕A (B⊕A looked up twice: by oplus_r2 and oplus_r1)
    let rom_trace = padded_trace(
        &[
            [H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1],
            [H_B_OPLUS_A, tags["oplus"], H_B, H_A, 1, 2], // looked up 2×
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(oplus_l_chip) as AirRef<_>,
            Arc::new(oplus_r2_chip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
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
    // A ⊢ A ⊕ B
    // Proof: oplus_r1(id(A))

    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let init_trace = padded_trace(&[[H_A, 1, H_A_OPLUS_B, 1, 0, 0]], 4);

    // oplus_r1: [active, hash, c0, c1, nonce_in, lax, nonce_out0]
    let oplus_r1_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1]],
        7, 4,
    );

    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let rom_trace = padded_trace(
        &[[H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
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
    // Try to prove A ⊕ B by providing B (should use oplus_r2)
    let oplus_r1_chip = RuleChip::new(specs["oplus_r1"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let init_trace = padded_trace(&[[H_B, 1, H_A_OPLUS_B, 1, 0, 0]], 4);

    // oplus_r1 produces obligation for child0=A, but context has B
    let oplus_r1_trace = dyn_trace(
        &[&[1, H_A_OPLUS_B, H_A, H_B, 0, 0, 1]],
        7, 4,
    );

    // id tries to consume A but only B is available
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let rom_trace = padded_trace(
        &[[H_A_OPLUS_B, tags["oplus"], H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(oplus_r1_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, oplus_r1_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong injection in oplus_r1");
}
