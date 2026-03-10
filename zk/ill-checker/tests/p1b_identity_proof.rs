//! Phase 1b: Identity proof — A ⊢ A
//!
//! First real multi-chip proof using the per-rule chip architecture.
//! Validates: InitChip + IdentityChip + OBLIG_BUS + CONTEXT_BUS.
//!
//! This is the simplest proof term: `id(A)` proves A ⊢ A.

mod common;

use std::sync::Arc;

use ill_checker::chips::{identity::IdentityChip, init::InitChip};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::padded_trace;

// --- Happy path ---

#[test]
fn p1b_a_proves_a() {
    let h_a = 42u32;

    // InitChip (width 6): [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
    let init_trace = padded_trace(&[[h_a, 1, h_a, 1, 0, 0]], 4);

    // IdentityChip (width 4): [principal, is_active, nonce, lax]
    let id_trace = padded_trace(&[[h_a, 1, 0, 0]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("Phase 1b: A ⊢ A should succeed");
}

#[test]
fn p1b_multiple_context_elements() {
    // A, B ⊢ — with two identity leaves
    let h_a = 42u32;
    let h_b = 99u32;

    let init_trace = padded_trace(
        &[
            [h_a, 1, h_a, 1, 0, 0], // introduce A, obligation (0, A, 0)
            [h_b, 1, h_b, 1, 1, 0], // introduce B, obligation (1, B, 0)
        ],
        4,
    );

    let id_trace = padded_trace(
        &[
            [h_a, 1, 0, 0], // consume obligation (0, A, 0), consume A
            [h_b, 1, 1, 0], // consume obligation (1, B, 0), consume B
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("Phase 1b: A, B ⊢ A, B (two identities) should succeed");
}

#[test]
fn p1b_different_hashes() {
    let h = 1234567u32;

    let init_trace = padded_trace(&[[h, 1, h, 1, 0, 0]], 4);
    let id_trace = padded_trace(&[[h, 1, 0, 0]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("Phase 1b: identity with large hash value");
}

#[test]
fn p1b_lax_flag_propagation() {
    let h_a = 42u32;

    let init_trace = padded_trace(&[[h_a, 1, h_a, 1, 0, 1]], 4); // lax=1
    let id_trace = padded_trace(&[[h_a, 1, 0, 1]], 4);            // lax=1

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("Phase 1b: identity with lax=1 should succeed");
}

// --- Failure cases ---

#[test]
#[should_panic]
fn p1b_wrong_type_fails() {
    let init_trace = padded_trace(&[[42, 1, 42, 1, 0, 0]], 4);
    let id_trace = padded_trace(&[[99, 1, 0, 0]], 4); // wrong principal

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: wrong type");
}

#[test]
#[should_panic]
fn p1b_wrong_nonce_fails() {
    let h_a = 42u32;
    let init_trace = padded_trace(&[[h_a, 1, h_a, 1, 0, 0]], 4); // nonce=0
    let id_trace = padded_trace(&[[h_a, 1, 5, 0]], 4);            // nonce=5

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: wrong nonce");
}

#[test]
#[should_panic]
fn p1b_lax_mismatch_fails() {
    let h_a = 42u32;
    let init_trace = padded_trace(&[[h_a, 1, h_a, 1, 0, 0]], 4); // lax=0
    let id_trace = padded_trace(&[[h_a, 1, 0, 1]], 4);            // lax=1

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: lax mismatch");
}

#[test]
#[should_panic]
fn p1b_unfulfilled_obligation_fails() {
    let init_trace = padded_trace(&[[42, 1, 42, 1, 0, 0]], 4);
    let id_trace = padded_trace::<4>(&[], 4); // no active rows

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: unfulfilled obligation");
}

#[test]
#[should_panic]
fn p1b_unconsumed_resource_fails() {
    let init_trace = padded_trace(
        &[
            [42, 1, 42, 1, 0, 0],
            [99, 1, 99, 1, 1, 0],
        ],
        4,
    );
    let id_trace = padded_trace(&[[42, 1, 0, 0]], 4); // only consume A

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: unconsumed resource");
}

#[test]
#[should_panic]
fn p1b_double_consume_fails() {
    let h_a = 42u32;
    let init_trace = padded_trace(&[[h_a, 1, h_a, 1, 0, 0]], 4);
    let id_trace = padded_trace(
        &[
            [h_a, 1, 0, 0],
            [h_a, 1, 0, 0], // try to consume A again
        ],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(IdentityChip) as AirRef<_>,
        ],
        vec![init_trace, id_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: double consumption");
}
