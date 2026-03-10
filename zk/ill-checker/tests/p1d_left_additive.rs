//! Phase 1d: Left rules + additive — A ⊗ B ⊢ B ⊗ A and A ⊢ A & A
//!
//! Validates: TensorLChip (left decomposition on CONTEXT_BUS),
//! DupChip (additive context duplication), BinaryRChip with WITH tag.
//!
//! Proof terms:
//!   A ⊗ B ⊢ B ⊗ A  →  tensor_l(tensor_r(id(B), id(A)))
//!   A ⊢ A & A       →  with_r(id(A), id(A))

mod common;

use std::sync::Arc;

use ill_checker::{
    chips::{
        binary_r::BinaryRChip,
        dup::DupChip,
        formula_rom::FormulaRomAir,
        identity::IdentityChip,
        init::InitChip,
        tensor_l::TensorLChip,
    },
    tags,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::padded_trace;

// Hash constants
const H_A: u32 = 42;
const H_B: u32 = 99;
const H_A_TENSOR_B: u32 = 100; // hash(A ⊗ B)
const H_B_TENSOR_A: u32 = 200; // hash(B ⊗ A)
const H_A_WITH_A: u32 = 300;   // hash(A & A)

// ============================================================
// Phase 1d-1: Left rules — A ⊗ B ⊢ B ⊗ A
// ============================================================

#[test]
fn p1d_tensor_swap() {
    // A ⊗ B ⊢ B ⊗ A
    // Proof: tensor_l over A⊗B, then tensor_r(id(B), id(A))
    //
    // Bus flow:
    //   Init:     ctx=A⊗B, oblig=(0, B⊗A, 0)
    //   TensorL:  CONTEXT receive A⊗B, send A, send B; FORMULA lookup A⊗B
    //   TensorR:  OBLIG receive (0, B⊗A, 0), send (1, B, 0), (2, A, 0); FORMULA lookup B⊗A
    //   Id:       OBLIG receive (1, B, 0), CONTEXT receive B
    //   Id:       OBLIG receive (2, A, 0), CONTEXT receive A

    // InitChip: [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
    let init_trace = padded_trace(
        &[[H_A_TENSOR_B, 1, H_B_TENSOR_A, 1, 0, 0]],
        4,
    );

    // TensorLChip: [hash, child0, child1, is_active]
    let tensor_l_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1]],
        4,
    );

    // BinaryRChip (tensor_r): [hash, child0, child1, is_active, nonce_in, nonce_out0, nonce_out1, lax]
    let tensor_r_trace = padded_trace(
        &[[H_B_TENSOR_A, H_B, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    // IdentityChip: [principal, is_active, nonce, lax]
    let id_trace = padded_trace(
        &[
            [H_B, 1, 1, 0], // consume (1, B, 0), consume B
            [H_A, 1, 2, 0], // consume (2, A, 0), consume A
        ],
        4,
    );

    // FormulaRomAir: [hash, tag, child0, child1, is_active, num_lookups]
    let rom_trace = padded_trace(
        &[
            [H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1], // A ⊗ B (looked up by tensor_l)
            [H_B_TENSOR_A, tags::TENSOR, H_B, H_A, 1, 1], // B ⊗ A (looked up by tensor_r)
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(TensorLChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_l_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1d: A ⊗ B ⊢ B ⊗ A should succeed");
}

#[test]
fn p1d_tensor_l_decompose_only() {
    // A ⊗ B ⊢ — where both A and B are consumed by identity
    // This is really: A ⊗ B, with obligation for A and B separately
    // Simulates: tensor_l decomposes, then identities consume
    //
    // Context: {A⊗B}, Obligations: (0, A, 0) and (1, B, 0)
    // tensor_l: receive A⊗B from context, send A and B to context
    // id: receive A from context + obligation (0, A, 0)
    // id: receive B from context + obligation (1, B, 0)

    let init_trace = padded_trace(
        &[
            [H_A_TENSOR_B, 1, H_A, 1, 0, 0], // ctx=A⊗B, oblig=(0, A, 0)
            [0, 0, H_B, 1, 1, 0],             // no ctx, oblig=(1, B, 0)
        ],
        4,
    );

    let tensor_l_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 0, 0],
            [H_B, 1, 1, 0],
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
            Arc::new(TensorLChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1d: tensor_l decompose + identity consume");
}

// --- Left rule failure cases ---

#[test]
#[should_panic]
fn p1d_tensor_l_wrong_child_fails() {
    // TensorL claims A⊗B decomposes to (A, C) but ROM says (A, B)
    let init_trace = padded_trace(
        &[[H_A_TENSOR_B, 1, H_B_TENSOR_A, 1, 0, 0]],
        4,
    );

    // WRONG: child1 is 77 (H_C) instead of H_B
    let tensor_l_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, 77, 1]],
        4,
    );

    let tensor_r_trace = padded_trace(
        &[[H_B_TENSOR_A, H_B, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_B, 1, 1, 0],
            [H_A, 1, 2, 0],
        ],
        4,
    );

    let rom_trace = padded_trace(
        &[
            [H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1],
            [H_B_TENSOR_A, tags::TENSOR, H_B, H_A, 1, 1],
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(TensorLChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_l_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong child in tensor_l");
}

#[test]
#[should_panic]
fn p1d_tensor_l_unconsumed_child_fails() {
    // TensorL decomposes A⊗B into A, B but only A is consumed
    let init_trace = padded_trace(
        &[[H_A_TENSOR_B, 1, H_A, 1, 0, 0]],
        4,
    );

    let tensor_l_trace = padded_trace(
        &[[H_A_TENSOR_B, H_A, H_B, 1]],
        4,
    );

    // Only consume A, B is left on CONTEXT_BUS
    let id_trace = padded_trace(
        &[[H_A, 1, 0, 0]],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(TensorLChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, tensor_l_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: B unconsumed after tensor_l");
}

// ============================================================
// Phase 1d-2: Additive — A ⊢ A & A
// ============================================================

#[test]
fn p1d_with_r_basic() {
    // A ⊢ A & A
    // Proof: with_r(id(A), id(A))
    //
    // Bus flow:
    //   Init:  ctx=A, oblig=(0, A&A, 0)
    //   Dup:   CONTEXT receive A, send A, send A  (duplicate for 2 branches)
    //   WithR: OBLIG receive (0, A&A, 0), send (1, A, 0), (2, A, 0); FORMULA lookup
    //   Id:    OBLIG receive (1, A, 0), CONTEXT receive A  (branch 1)
    //   Id:    OBLIG receive (2, A, 0), CONTEXT receive A  (branch 2)

    let init_trace = padded_trace(
        &[[H_A, 1, H_A_WITH_A, 1, 0, 0]],
        4,
    );

    // DupChip: [hash, is_active]
    let dup_trace = padded_trace(
        &[[H_A, 1]], // duplicate A for two branches
        4,
    );

    // BinaryRChip (with_r): [hash, child0, child1, is_active, nonce_in, nonce_out0, nonce_out1, lax]
    let with_r_trace = padded_trace(
        &[[H_A_WITH_A, H_A, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0], // branch 1
            [H_A, 1, 2, 0], // branch 2
        ],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_WITH_A, tags::WITH, H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(DupChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, dup_trace, with_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1d: A ⊢ A & A should succeed");
}

#[test]
fn p1d_with_r_multi_context() {
    // A, B ⊢ (A ⊗ B) & (A ⊗ B)
    // Context has two elements, both need duplication.
    //
    // Bus flow:
    //   Init:     ctx=A, ctx=B, oblig=(0, (A⊗B)&(A⊗B), 0)
    //   Dup:      receive A, send A×2; receive B, send B×2
    //   WithR:    receive oblig, produce obligs for A⊗B and A⊗B
    //   TensorR₁: receive oblig for A⊗B, produce obligs for A, B (branch 1)
    //   TensorR₂: receive oblig for A⊗B, produce obligs for A, B (branch 2)
    //   Id×4:     consume all obligations + context resources

    let h_goal: u32 = 500; // hash((A⊗B) & (A⊗B))

    let init_trace = padded_trace(
        &[
            [H_A, 1, h_goal, 1, 0, 0], // ctx=A, oblig=(0, goal, 0)
            [H_B, 1, 0, 0, 0, 0],       // ctx=B
        ],
        4,
    );

    // Duplicate both A and B
    let dup_trace = padded_trace(
        &[
            [H_A, 1],
            [H_B, 1],
        ],
        4,
    );

    // WithR decomposes goal → A⊗B, A⊗B
    let with_r_trace = padded_trace(
        &[[h_goal, H_A_TENSOR_B, H_A_TENSOR_B, 1, 0, 1, 2, 0]],
        4,
    );

    // Two tensor_r applications (both in same chip)
    let tensor_r_trace = padded_trace(
        &[
            [H_A_TENSOR_B, H_A, H_B, 1, 1, 3, 4, 0], // branch 1: A⊗B → A, B
            [H_A_TENSOR_B, H_A, H_B, 1, 2, 5, 6, 0], // branch 2: A⊗B → A, B
        ],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 3, 0], // branch 1, A
            [H_B, 1, 4, 0], // branch 1, B
            [H_A, 1, 5, 0], // branch 2, A
            [H_B, 1, 6, 0], // branch 2, B
        ],
        4,
    );

    // ROM: goal formula + A⊗B (looked up twice)
    let rom_trace = padded_trace(
        &[
            [h_goal, tags::WITH, H_A_TENSOR_B, H_A_TENSOR_B, 1, 1],
            [H_A_TENSOR_B, tags::TENSOR, H_A, H_B, 1, 2], // looked up 2x
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(DupChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::TENSOR }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, dup_trace, with_r_trace, tensor_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("Phase 1d: A, B ⊢ (A ⊗ B) & (A ⊗ B) should succeed");
}

// --- Additive failure cases ---

#[test]
#[should_panic]
fn p1d_with_r_no_dup_fails() {
    // A ⊢ A & A without DupChip — CONTEXT_BUS unbalanced
    // Init sends A once, but two identities try to receive A twice
    let init_trace = padded_trace(
        &[[H_A, 1, H_A_WITH_A, 1, 0, 0]],
        4,
    );

    // NO DupChip — skip it entirely

    let with_r_trace = padded_trace(
        &[[H_A_WITH_A, H_A, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_A, 1, 2, 0], // tries to receive A again — unbalanced
        ],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_WITH_A, tags::WITH, H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, with_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: no dup for additive");
}

#[test]
#[should_panic]
fn p1d_dup_wrong_hash_fails() {
    // DupChip duplicates B instead of A — CONTEXT_BUS unbalanced
    let init_trace = padded_trace(
        &[[H_A, 1, H_A_WITH_A, 1, 0, 0]],
        4,
    );

    // Dup the wrong hash
    let dup_trace = padded_trace(
        &[[H_B, 1]], // duplicates B, but context only has A
        4,
    );

    let with_r_trace = padded_trace(
        &[[H_A_WITH_A, H_A, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_A, 1, 2, 0],
        ],
        4,
    );

    let rom_trace = padded_trace(
        &[[H_A_WITH_A, tags::WITH, H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(DupChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, dup_trace, with_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: dup wrong hash");
}

#[test]
#[should_panic]
fn p1d_with_r_wrong_formula_fails() {
    // WithR looks up with WITH tag but ROM has TENSOR tag for that hash
    let init_trace = padded_trace(
        &[[H_A, 1, H_A_WITH_A, 1, 0, 0]],
        4,
    );

    let dup_trace = padded_trace(
        &[[H_A, 1]],
        4,
    );

    let with_r_trace = padded_trace(
        &[[H_A_WITH_A, H_A, H_A, 1, 0, 1, 2, 0]],
        4,
    );

    let id_trace = padded_trace(
        &[
            [H_A, 1, 1, 0],
            [H_A, 1, 2, 0],
        ],
        4,
    );

    // ROM has TENSOR tag instead of WITH — lookup mismatch
    let rom_trace = padded_trace(
        &[[H_A_WITH_A, tags::TENSOR, H_A, H_A, 1, 1]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(DupChip) as AirRef<_>,
            Arc::new(BinaryRChip { tag: tags::WITH }) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, dup_trace, with_r_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: wrong formula tag in ROM");
}
