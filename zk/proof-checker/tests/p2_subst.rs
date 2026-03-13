//! Phase 2: SubstChip dedicated tests.
//!
//! Tests the substitution bridge chip in isolation using
//! FlatInitChip/FlatFinalChip for CONTEXT_BUS balance.
//!
//! Happy path: root+internal+freevar, two freevars, unwrap leaf.
//! Adversarial: c0_eq lie, root/freevar mutual exclusion,
//!   is_internal cheating, stray non-root row, freevar wrong ground,
//!   unwrap wrong c0.

mod common;

use std::sync::Arc;

use proof_checker::chips::{
    flat_final::FlatFinalChip,
    flat_init::FlatInitChip,
    subst::SubstChip,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::{make_formula_rom, make_freevar_rom, padded_trace};

// Tag constants (from identity.json fixture)
const TAG_TENSOR: u32 = 1;
const TAG_LOLI: u32 = 2;
const TAG_BANG: u32 = 7;
const TAG_FREEVAR: u32 = 11;

// Hash constants (arbitrary, must be self-consistent within each test)
const H_A: u32 = 42;
const H_B: u32 = 99;
const H_BODY: u32 = 200;
const H_FV_X: u32 = 300;      // freevar(1)
const H_FV_Y: u32 = 301;      // freevar(2)
const H_TENSOR_XA: u32 = 400;  // tensor(fv_X, A)
const H_TENSOR_BA: u32 = 401;  // tensor(B, A)
const H_LOLI_OLD: u32 = 500;   // loli(tensor_XA, body)
const H_LOLI_NEW: u32 = 501;   // loli(tensor_BA, body)
const H_BANG_A: u32 = 600;     // bang(A)
const H_TENSOR_XY: u32 = 700;  // tensor(fv_X, fv_Y)
const H_TENSOR_AB: u32 = 701;  // tensor(A, B)
const H_LOLI_OLD2: u32 = 800;  // loli(tensor_XY, body)
const H_LOLI_NEW2: u32 = 801;  // loli(tensor_AB, body)
const H_LOLI3: u32 = 900;      // loli(A, body)
const H_LOLI3_NEW: u32 = 901;  // loli(bang_A, body)

const MIN: usize = 4;

/// Run SubstChip with CONTEXT_BUS balance (FlatInit sends old, FlatFinal receives new)
/// and FORMULA_BUS + optional FREEVAR_BUS.
fn run_subst_test(
    subst_rows: &[[u32; 16]],
    ctx_old: u32,
    ctx_new: u32,
    formula_rom: &[[u32; 6]],
    freevar_rom: &[[u32; 5]],
) {
    let init = FlatInitChip { ctx_hashes: vec![ctx_old], min_rows: MIN };
    let init_trace = padded_trace::<1>(&[[0]], MIN); // dummy main trace

    let final_trace = padded_trace::<2>(&[[1, ctx_new]], MIN);

    let subst_trace = padded_trace::<16>(subst_rows, MIN);

    let (rom_chip, rom_trace) = make_formula_rom(formula_rom, MIN);

    let mut airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip),
        Arc::new(SubstChip),
        Arc::new(rom_chip),
    ];
    let mut traces = vec![init_trace, final_trace, subst_trace, rom_trace];
    let mut pis = vec![vec![], vec![], vec![], vec![]];

    if !freevar_rom.is_empty() {
        let (fv_chip, fv_trace) = make_freevar_rom(freevar_rom, MIN);
        airs.push(Arc::new(fv_chip));
        traces.push(fv_trace);
        pis.push(vec![]);
    }

    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .expect("SubstChip test");
}

// ---------------------------------------------------------------------------
// Happy path: root + internal + freevar
// Tree: loli(tensor(fv_X, A), body) → loli(tensor(B, A), body)
// ---------------------------------------------------------------------------

#[test]
fn p2_subst_root_internal_freevar() {
    let subst_rows: [[u32; 16]; 3] = [
        // Root (loli): old=500, new=501, c0_old=tensor_XA, c1_old=body, c0_new=tensor_BA, c1_new=body
        [1, H_LOLI_OLD, H_LOLI_NEW, 1, 0, 1, TAG_LOLI, H_TENSOR_XA, H_BODY, H_TENSOR_BA, H_BODY, 0, 1, 1, 0, 0],
        // Internal (tensor): old=400, new=401, c0_old=fv_X, c1_old=A, c0_new=B, c1_new=A
        [1, H_TENSOR_XA, H_TENSOR_BA, 0, 0, 1, TAG_TENSOR, H_FV_X, H_A, H_B, H_A, 0, 1, 1, 1, 0],
        // Freevar leaf: old=fv_X(300), new=B(99)
        [1, H_FV_X, H_B, 0, 1, 1, TAG_FREEVAR, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 5] = [
        [H_LOLI_OLD, TAG_LOLI, H_TENSOR_XA, H_BODY, 1, 1],
        [H_LOLI_NEW, TAG_LOLI, H_TENSOR_BA, H_BODY, 1, 1],
        [H_TENSOR_XA, TAG_TENSOR, H_FV_X, H_A, 1, 1],
        [H_TENSOR_BA, TAG_TENSOR, H_B, H_A, 1, 1],
        [H_FV_X, TAG_FREEVAR, 1, 0, 1, 1],
    ];

    let freevar_rom: [[u32; 5]; 1] = [
        [1, H_FV_X, H_B, 1, 1], // subst_id=1, fv_X → B
    ];

    run_subst_test(&subst_rows, H_LOLI_OLD, H_LOLI_NEW, &formula_rom, &freevar_rom);
}

// ---------------------------------------------------------------------------
// Happy path: root + internal + two freevar leaves (c0 and c1 both differ)
// Tree: loli(tensor(fv_X, fv_Y), body) → loli(tensor(A, B), body)
// ---------------------------------------------------------------------------

#[test]
fn p2_subst_root_two_freevars() {
    let subst_rows: [[u32; 16]; 4] = [
        // Root (loli): old=800, new=801
        [1, H_LOLI_OLD2, H_LOLI_NEW2, 1, 0, 1, TAG_LOLI, H_TENSOR_XY, H_BODY, H_TENSOR_AB, H_BODY, 0, 1, 1, 0, 0],
        // Internal (tensor): old=700, new=701, both children differ
        [1, H_TENSOR_XY, H_TENSOR_AB, 0, 0, 1, TAG_TENSOR, H_FV_X, H_FV_Y, H_A, H_B, 0, 0, 1, 1, 0],
        // Freevar X: old=300 → new=42
        [1, H_FV_X, H_A, 0, 1, 1, TAG_FREEVAR, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        // Freevar Y: old=301 → new=99
        [1, H_FV_Y, H_B, 0, 1, 1, TAG_FREEVAR, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 6] = [
        [H_LOLI_OLD2, TAG_LOLI, H_TENSOR_XY, H_BODY, 1, 1],
        [H_LOLI_NEW2, TAG_LOLI, H_TENSOR_AB, H_BODY, 1, 1],
        [H_TENSOR_XY, TAG_TENSOR, H_FV_X, H_FV_Y, 1, 1],
        [H_TENSOR_AB, TAG_TENSOR, H_A, H_B, 1, 1],
        [H_FV_X, TAG_FREEVAR, 1, 0, 1, 1],
        [H_FV_Y, TAG_FREEVAR, 2, 0, 1, 1],
    ];

    let freevar_rom: [[u32; 5]; 2] = [
        [1, H_FV_X, H_A, 1, 1],
        [1, H_FV_Y, H_B, 1, 1],
    ];

    run_subst_test(&subst_rows, H_LOLI_OLD2, H_LOLI_NEW2, &formula_rom, &freevar_rom);
}

// ---------------------------------------------------------------------------
// Happy path: root + unwrap leaf (tag mismatch, new wraps old)
// Tree: loli(A, body) → loli(bang(A), body)
// Unwrap: old=A, new=bang(A), new.c0=A=old
// ---------------------------------------------------------------------------

#[test]
fn p2_subst_unwrap_basic() {
    let subst_rows: [[u32; 16]; 2] = [
        // Root (loli): old=900, new=901, c0_old=A, c0_new=bang(A)
        [1, H_LOLI3, H_LOLI3_NEW, 1, 0, 1, TAG_LOLI, H_A, H_BODY, H_BANG_A, H_BODY, 0, 1, 1, 0, 0],
        // Unwrap: old=A(42), new=bang(A)(600), tag=bang, c0_new=42=hash_old ✓
        [1, H_A, H_BANG_A, 0, 0, 1, TAG_BANG, 0, 0, H_A, 0, 0, 0, 0, 0, 1],
    ];

    let formula_rom: [[u32; 6]; 3] = [
        [H_LOLI3, TAG_LOLI, H_A, H_BODY, 1, 1],
        [H_LOLI3_NEW, TAG_LOLI, H_BANG_A, H_BODY, 1, 1],
        [H_BANG_A, TAG_BANG, H_A, 0, 1, 1],
    ];

    run_subst_test(&subst_rows, H_LOLI3, H_LOLI3_NEW, &formula_rom, &[]);
}

// ---------------------------------------------------------------------------
// Adversarial: c0_eq=1 lie (claim children equal when they differ)
// Constraint: is_internal * c0_eq * (c0_old - c0_new) must be zero
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_c0_eq_lie_fails() {
    let subst_rows: [[u32; 16]; 2] = [
        // Root: same as test 1
        [1, H_LOLI_OLD, H_LOLI_NEW, 1, 0, 1, TAG_LOLI, H_TENSOR_XA, H_BODY, H_TENSOR_BA, H_BODY, 0, 1, 1, 0, 0],
        // Internal: c0_eq=1 LIE (c0_old=300 ≠ c0_new=99)
        [1, H_TENSOR_XA, H_TENSOR_BA, 0, 0, 1, TAG_TENSOR, H_FV_X, H_A, H_B, H_A, 1, 1, 1, 1, 0],
    ];

    let formula_rom: [[u32; 6]; 4] = [
        [H_LOLI_OLD, TAG_LOLI, H_TENSOR_XA, H_BODY, 1, 1],
        [H_LOLI_NEW, TAG_LOLI, H_TENSOR_BA, H_BODY, 1, 1],
        [H_TENSOR_XA, TAG_TENSOR, H_FV_X, H_A, 1, 1],
        [H_TENSOR_BA, TAG_TENSOR, H_B, H_A, 1, 1],
    ];

    run_subst_test(&subst_rows, H_LOLI_OLD, H_LOLI_NEW, &formula_rom, &[]);
}

// ---------------------------------------------------------------------------
// Adversarial: c1_eq=1 lie on non-root internal node
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_c1_eq_lie_fails() {
    // Internal tensor with c1_old=301(fv_Y) ≠ c1_new=99(B), but c1_eq=1
    let subst_rows: [[u32; 16]; 3] = [
        [1, H_LOLI_OLD2, H_LOLI_NEW2, 1, 0, 1, TAG_LOLI, H_TENSOR_XY, H_BODY, H_TENSOR_AB, H_BODY, 0, 1, 1, 0, 0],
        // Internal: c0_eq=0 correct, c1_eq=1 LIE (c1_old=301 ≠ c1_new=99)
        [1, H_TENSOR_XY, H_TENSOR_AB, 0, 0, 1, TAG_TENSOR, H_FV_X, H_FV_Y, H_A, H_B, 0, 1, 1, 1, 0],
        // Freevar X to satisfy c0 child demand
        [1, H_FV_X, H_A, 0, 1, 1, TAG_FREEVAR, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 5] = [
        [H_LOLI_OLD2, TAG_LOLI, H_TENSOR_XY, H_BODY, 1, 1],
        [H_LOLI_NEW2, TAG_LOLI, H_TENSOR_AB, H_BODY, 1, 1],
        [H_TENSOR_XY, TAG_TENSOR, H_FV_X, H_FV_Y, 1, 1],
        [H_TENSOR_AB, TAG_TENSOR, H_A, H_B, 1, 1],
        [H_FV_X, TAG_FREEVAR, 1, 0, 1, 1],
    ];

    let freevar_rom: [[u32; 5]; 1] = [[1, H_FV_X, H_A, 1, 1]];

    run_subst_test(&subst_rows, H_LOLI_OLD2, H_LOLI_NEW2, &formula_rom, &freevar_rom);
}

// ---------------------------------------------------------------------------
// Adversarial: is_root=1 AND is_freevar=1 (mutual exclusion violation)
// Constraint: is_root * is_freevar = 0
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_root_freevar_exclusion_fails() {
    // Row with both is_root=1 and is_freevar=1
    let subst_rows: [[u32; 16]; 1] = [
        [1, H_LOLI_OLD, H_LOLI_NEW, 1, 1, 1, TAG_FREEVAR, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 1] = [
        [H_LOLI_OLD, TAG_FREEVAR, 1, 0, 1, 1],
    ];

    let freevar_rom: [[u32; 5]; 1] = [[1, H_LOLI_OLD, H_LOLI_NEW, 1, 1]];

    run_subst_test(&subst_rows, H_LOLI_OLD, H_LOLI_NEW, &formula_rom, &freevar_rom);
}

// ---------------------------------------------------------------------------
// Adversarial: is_internal=0 when it should be 1 (skip FORMULA_BUS demand)
// Constraint: is_internal = is_active * (1 - is_freevar) * (1 - is_unwrap)
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_is_internal_lie_fails() {
    let subst_rows: [[u32; 16]; 2] = [
        [1, H_LOLI_OLD, H_LOLI_NEW, 1, 0, 1, TAG_LOLI, H_TENSOR_XA, H_BODY, H_TENSOR_BA, H_BODY, 0, 1, 1, 0, 0],
        // Internal row with is_internal=0 LIE, non_root_int=0 LIE
        [1, H_TENSOR_XA, H_TENSOR_BA, 0, 0, 1, TAG_TENSOR, H_FV_X, H_A, H_B, H_A, 0, 1, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 2] = [
        [H_LOLI_OLD, TAG_LOLI, H_TENSOR_XA, H_BODY, 1, 1],
        [H_LOLI_NEW, TAG_LOLI, H_TENSOR_BA, H_BODY, 1, 1],
    ];

    run_subst_test(&subst_rows, H_LOLI_OLD, H_LOLI_NEW, &formula_rom, &[]);
}

// ---------------------------------------------------------------------------
// Adversarial: stray non-root row (SUBST_TREE_BUS has unmatched receive)
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_stray_row_fails() {
    // Single non-root internal row with no parent — SUBST_TREE_BUS unbalanced
    let subst_rows: [[u32; 16]; 1] = [
        [1, H_TENSOR_XA, H_TENSOR_BA, 0, 0, 1, TAG_TENSOR, H_FV_X, H_A, H_B, H_A, 0, 1, 1, 1, 0],
    ];

    let formula_rom: [[u32; 6]; 2] = [
        [H_TENSOR_XA, TAG_TENSOR, H_FV_X, H_A, 1, 1],
        [H_TENSOR_BA, TAG_TENSOR, H_B, H_A, 1, 1],
    ];

    // No FlatInit/FlatFinal needed (no root → no CONTEXT_BUS interaction)
    // But we still need the chips for the engine — use empty init
    let init = FlatInitChip { ctx_hashes: vec![], min_rows: MIN };
    let init_trace = padded_trace::<1>(&[], MIN);
    let final_trace = padded_trace::<2>(&[], MIN);
    let subst_trace = padded_trace::<16>(&subst_rows, MIN);
    let (rom_chip, rom_trace) = make_formula_rom(&formula_rom, MIN);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init) as AirRef<_>,
            Arc::new(FlatFinalChip) as AirRef<_>,
            Arc::new(SubstChip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, final_trace, subst_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: stray non-root row");
}

// ---------------------------------------------------------------------------
// Adversarial: freevar ROM has wrong ground value (FREEVAR_BUS mismatch)
// SubstChip demands (1, 300, 99) but ROM provides (1, 300, 42)
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_freevar_wrong_ground_fails() {
    let subst_rows: [[u32; 16]; 3] = [
        [1, H_LOLI_OLD, H_LOLI_NEW, 1, 0, 1, TAG_LOLI, H_TENSOR_XA, H_BODY, H_TENSOR_BA, H_BODY, 0, 1, 1, 0, 0],
        [1, H_TENSOR_XA, H_TENSOR_BA, 0, 0, 1, TAG_TENSOR, H_FV_X, H_A, H_B, H_A, 0, 1, 1, 1, 0],
        [1, H_FV_X, H_B, 0, 1, 1, TAG_FREEVAR, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let formula_rom: [[u32; 6]; 5] = [
        [H_LOLI_OLD, TAG_LOLI, H_TENSOR_XA, H_BODY, 1, 1],
        [H_LOLI_NEW, TAG_LOLI, H_TENSOR_BA, H_BODY, 1, 1],
        [H_TENSOR_XA, TAG_TENSOR, H_FV_X, H_A, 1, 1],
        [H_TENSOR_BA, TAG_TENSOR, H_B, H_A, 1, 1],
        [H_FV_X, TAG_FREEVAR, 1, 0, 1, 1],
    ];

    // WRONG: ground=42 instead of 99
    let freevar_rom: [[u32; 5]; 1] = [[1, H_FV_X, H_A, 1, 1]];

    run_subst_test(&subst_rows, H_LOLI_OLD, H_LOLI_NEW, &formula_rom, &freevar_rom);
}

// ---------------------------------------------------------------------------
// Adversarial: unwrap row with wrong c0_new (c0_new ≠ hash_old)
// Constraint: is_active * is_unwrap * (c0_new - hash_old) = 0
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_subst_unwrap_wrong_c0_fails() {
    let subst_rows: [[u32; 16]; 2] = [
        [1, H_LOLI3, H_LOLI3_NEW, 1, 0, 1, TAG_LOLI, H_A, H_BODY, H_BANG_A, H_BODY, 0, 1, 1, 0, 0],
        // Unwrap: c0_new=99 instead of 42 (hash_old=42)
        [1, H_A, H_BANG_A, 0, 0, 1, TAG_BANG, 0, 0, H_B, 0, 0, 0, 0, 0, 1],
    ];

    let formula_rom: [[u32; 6]; 3] = [
        [H_LOLI3, TAG_LOLI, H_A, H_BODY, 1, 1],
        [H_LOLI3_NEW, TAG_LOLI, H_BANG_A, H_BODY, 1, 1],
        // ROM has the real decomposition bang(A)=(7, 42, 0)
        // but unwrap row claims c0_new=99, which won't match ROM either
        [H_BANG_A, TAG_BANG, H_A, 0, 1, 1],
    ];

    run_subst_test(&subst_rows, H_LOLI3, H_LOLI3_NEW, &formula_rom, &[]);
}
