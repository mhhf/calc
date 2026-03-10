//! Phase 1c: Multi-rule proof — A, B ⊢ A ⊗ B
//!
//! Validates: TensorR (BinaryRChip) + FormulaRomAir + FORMULA_BUS +
//! obligation bus with 2 produces per row + InitChip redesign.
//!
//! Proof term: tensor_r(id(A), id(B))
//!
//! Bus flow for A, B ⊢ A ⊗ B:
//!   InitChip: send A,B on CONTEXT; send (0, A⊗B, 0) on OBLIG
//!   TensorR:  receive (0, A⊗B, 0) on OBLIG; send (1,A,0), (2,B,0) on OBLIG;
//!             lookup (A⊗B, TENSOR, A, B) on FORMULA
//!   Identity: receive (1,A,0) on OBLIG, receive A on CONTEXT
//!   Identity: receive (2,B,0) on OBLIG, receive B on CONTEXT
//!   FormulaRom: provide (A⊗B, TENSOR, A, B) on FORMULA

mod common;

use std::sync::Arc;

use ill_checker::{
    chips::{
        binary_r::BinaryRChip,
        formula_rom::FormulaRomAir,
        identity::IdentityChip,
        init::InitChip,
    },
    tags,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::padded_trace;

// Hash constants for test formulas
const H_A: u32 = 42;
const H_B: u32 = 99;
const H_A_TENSOR_B: u32 = 100; // hash(A ⊗ B)
const H_NESTED: u32 = 300;     // hash((A ⊗ B) ⊗ C)
const H_C: u32 = 77;

// --- Happy path ---

#[test]
fn p1c_tensor_r_basic() {
    // A, B ⊢ A ⊗ B
    // Proof: tensor_r(id(A), id(B))

    // InitChip: [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0], // ctx=A, oblig=(0, A⊗B, 0)
            [H_B, 1, 0, 0, 0, 0],             // ctx=B, no obligation
        ],
        4,
    );

    // BinaryRChip (tensor_r): [hash, child0, child1, is_active, nonce_in, nonce_out0, nonce_out1, lax]
    let tensor_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1, 0, 1, 2, 0]],
        4,
    );

    // IdentityChip: [principal, is_active, nonce, lax]
    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0], // consume obligation (1, A, 0), consume A
            [H_B, 1, 2, 0], // consume obligation (2, B, 0), consume B
        ],
        4,
    );

    // FormulaRomAir: [hash, tag, child0, child1, is_active, num_lookups]
    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1c: A, B ⊢ A ⊗ B should succeed");
}

#[test]
fn p1c_tensor_r_nested() {
    // A, B, C ⊢ (A ⊗ B) ⊗ C
    // Proof: tensor_r(tensor_r(id(A), id(B)), id(C))
    //
    // Outer tensor_r: consume oblig (0, (A⊗B)⊗C), produce (1, A⊗B) and (2, C)
    // Inner tensor_r: consume oblig (1, A⊗B), produce (3, A) and (4, B)

    let init_trace = padded_trace(
        &[
            [H_A, 1, H_NESTED, 1, 0, 0], // ctx=A, oblig=(0, (A⊗B)⊗C, 0)
            [H_B, 1, 0, 0, 0, 0],         // ctx=B
            [H_C, 1, 0, 0, 0, 0],         // ctx=C
        ],
        4,
    );

    // Two tensor_r rows (both in same chip trace)
    let tensor_r_trace = padded_trace(
        &[
            [H_NESTED, H_A_TENSOR_B, H_C, 1, 0, 1, 2, 0],   // outer: (A⊗B)⊗C → A⊗B, C
            [H_A_TENSOR_B, H_A, H_B, 1, 1, 3, 4, 0],         // inner: A⊗B → A, B
        ],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 3, 0], // consume (3, A, 0)
            [H_B, 1, 4, 0], // consume (4, B, 0)
            [H_C, 1, 2, 0], // consume (2, C, 0)
        ],
        4,
    );

    // ROM: two formula entries
    let rom_trace = padded_trace(
        &[
            [H_NESTED, tags::TENSOR, H_A_TENSOR_B, H_C, 1, 1],   // (A⊗B)⊗C
            [H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1],         // A⊗B
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1c: A, B, C ⊢ (A ⊗ B) ⊗ C should succeed");
}

#[test]
fn p1c_single_element_tensor() {
    // Verify it works with lax=1
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 1], // lax=1
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    let tensor_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1, 0, 1, 2, 1]], // lax=1
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 1], // lax=1
            [H_B, 1, 2, 1], // lax=1
        ],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1c: tensor_r with lax=1");
}

// --- Failure cases ---

#[test]
#[should_panic]
fn p1c_wrong_decomposition_fails() {
    // TensorR claims A⊗B decomposes to (A, C) but ROM says (A, B)
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    // WRONG: child1 is H_C instead of H_B
    let tensor_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_C, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_C, 1, 2, 0],
        ],
        4,
    );

    // ROM has correct decomposition (A, B) — lookup will fail
    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong decomposition");
}

#[test]
#[should_panic]
fn p1c_wrong_tag_fails() {
    // Use WITH tag in BinaryRChip but ROM has TENSOR tag
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    let with_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_B, 1, 2, 0],
        ],
        4,
    );

    // ROM has TENSOR tag — WITH chip's lookup will mismatch
    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>, // WRONG tag
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, with_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong connective tag");
}

#[test]
#[should_panic]
fn p1c_missing_child_obligation_fails() {
    // TensorR produces obligations for A and B, but only A is consumed
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    let tensor_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1, 0, 1, 2, 0]],
        4,
    );

    // Only consume obligation for A, not B
    let id_trace = padded_trace(
        &[[H_A, 1, 1, 0]],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: unfulfilled child obligation");
}

#[test]
#[should_panic]
fn p1c_no_rom_entry_fails() {
    // TensorR looks up formula but ROM has no matching entry
    let init_trace = padded_trace(
        &[
            [H_A, 1, H_A_TENSOR_B, 1, 0, 0],
            [H_B, 1, 0, 0, 0, 0],
        ],
        4,
    );

    let tensor_r_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_B, 1, 2, 0],
        ],
        4,
    );

    // ROM is empty — no formula entries
    let rom_trace = padded_trace::<6>(&[], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: no ROM entry");
}
