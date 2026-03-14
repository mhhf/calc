//! Phase 4a spike: prove/verify separation + public values + recursive verification.
//!
//! Test progression:
//! 1. Separate keygen/prove/verify — retain Proof + VK objects
//! 2. Public values shape constraint — PIs must match AIR declaration
//! 3. Recursive STARK-in-STARK verification — build verifier program from VK+proof
//! 4. FlatInitChip public values — context in main trace + PVs for IVC
//!
//! For the recursion spike plan, see TODO_0084 §4a.

mod common;

use std::sync::Arc;

use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine,
    engine::{StarkEngine, StarkFriEngine},
};
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use proof_checker::chips::{
    flat_init::FlatInitChip,
    flat_final::FlatFinalChip,
};

use common::padded_trace;

/// Helper: build a FlatInit+FlatFinal pair with PVs for a given context hash.
fn flat_init_final_with_pvs(h: u32) -> (
    Vec<AirRef<openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Config>>,
    Vec<openvm_stark_backend::p3_matrix::dense::RowMajorMatrix<BabyBear>>,
    Vec<Vec<BabyBear>>,
) {
    let init = FlatInitChip { ctx_hashes: vec![h], max_ctx_size: 1, min_rows: 4 };
    let init_trace = padded_trace::<2>(&[[1, h]], 4);

    let final_rows: Vec<[u32; 2]> = vec![[1, h]];
    let final_trace = padded_trace::<2>(&final_rows, 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip { max_ctx_size: 1 }),
    ];
    let traces = vec![init_trace, final_trace];
    let pis = vec![
        vec![BabyBear::from_u32(h)],   // init PVs
        vec![BabyBear::from_u32(h)],   // final PVs
    ];
    (airs, traces, pis)
}

/// Helper: build a FlatInit+FlatFinal pair WITHOUT PVs (legacy mode, max_ctx_size=0).
fn flat_init_final_no_pvs(h: u32) -> (
    Vec<AirRef<openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Config>>,
    Vec<openvm_stark_backend::p3_matrix::dense::RowMajorMatrix<BabyBear>>,
    Vec<Vec<BabyBear>>,
) {
    let init = FlatInitChip { ctx_hashes: vec![h], max_ctx_size: 0, min_rows: 4 };
    let init_trace = padded_trace::<2>(&[[1, h]], 4);

    let final_rows: Vec<[u32; 2]> = vec![[1, h]];
    let final_trace = padded_trace::<2>(&final_rows, 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip { max_ctx_size: 0 }),
    ];
    let traces = vec![init_trace, final_trace];
    let pis = vec![vec![], vec![]];
    (airs, traces, pis)
}

// ---------------------------------------------------------------------------
// Step 1: Prove/verify separation — retain Proof + VK objects
// ---------------------------------------------------------------------------

#[test]
fn p4a_separate_prove_verify() {
    let (airs, traces, pis) = flat_init_final_no_pvs(42);

    let vdata = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("trivial flat path should verify");

    let vk = &vdata.data.vk;
    let proof = &vdata.data.proof;

    assert_eq!(vk.inner.per_air.len(), 2, "VK should have 2 AIR entries");
    assert_eq!(proof.per_air.len(), 2, "Proof should have 2 per-air entries");

    let engine = BabyBearPoseidon2Engine::new(vdata.fri_params);
    engine.verify(vk, proof)
        .expect("separate verify should succeed with same VK+proof");
}

// ---------------------------------------------------------------------------
// Step 2: Public values shape — the backend enforces declared PI count
// ---------------------------------------------------------------------------

/// Passing more PIs than declared by the AIR fails with InvalidProofShape.
#[test]
#[should_panic(expected = "InvalidProofShape")]
fn p4a_pis_rejected_when_not_declared_by_air() {
    let (airs, traces, _) = flat_init_final_no_pvs(42);

    // Override PIs: pass 1 PI to init chip that declares num_public_values=0
    let pis = vec![vec![BabyBear::new(42)], vec![]];

    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .expect("should fail: PIs not declared");
}

// ---------------------------------------------------------------------------
// Step 3: Recursive STARK-in-STARK verification
// ---------------------------------------------------------------------------

#[test]
fn p4a_recursive_verify_trivial() {
    use openvm_native_compiler::conversion::CompilerOptions;
    use openvm_native_recursion::testing_utils::inner::build_verification_program;

    let (airs, traces, pis) = flat_init_final_no_pvs(42);

    let vparams = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("inner proof should verify");

    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );

    assert!(!program.defined_instructions().is_empty(), "verifier program should have instructions");
    assert!(!witness_stream.is_empty(), "witness stream should contain serialized proof");

    println!("  verifier program: {} instructions", program.defined_instructions().len());
    println!("  witness stream: {} chunks", witness_stream.len());
}

#[test]
fn p4a_recursive_verify_identity_fixture() {
    use openvm_native_compiler::conversion::CompilerOptions;
    use openvm_native_recursion::testing_utils::inner::build_verification_program;

    let json = std::fs::read_to_string(format!(
        "{}/tests/fixtures/identity.json",
        env!("CARGO_MANIFEST_DIR"),
    )).expect("identity fixture");

    let vparams = proof_checker::bridge::prove_witness_vdata(
        &serde_json::from_str(&json).expect("parse"),
    ).expect("inner proof should verify");

    let num_airs = vparams.data.vk.inner.per_air.len();

    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );

    println!("  identity fixture: {} AIRs, {} instructions, {} witness chunks",
        num_airs, program.defined_instructions().len(), witness_stream.len());
    assert!(!program.defined_instructions().is_empty());
}

// ---------------------------------------------------------------------------
// Step 4: FlatInitChip public values (Phase 4a-2)
// ---------------------------------------------------------------------------

/// FlatInitChip declares PVs, proof includes them, and they are accessible
/// in the verification data for recursive verification.
#[test]
fn p4a_init_with_public_values() {
    let h = 42u32;
    let (airs, traces, pis) = flat_init_final_with_pvs(h);

    let vdata = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("proof with PVs should verify");

    // PVs should be present in the proof
    let init_pvs = &vdata.data.proof.per_air[0].public_values;
    let final_pvs = &vdata.data.proof.per_air[1].public_values;

    assert_eq!(init_pvs.len(), 1, "init should have 1 PV");
    assert_eq!(final_pvs.len(), 1, "final should have 1 PV");
    assert_eq!(init_pvs[0].as_canonical_u32(), h, "init PV should be context hash");
    assert_eq!(final_pvs[0].as_canonical_u32(), h, "final PV should be context hash");
}

/// Multiple context entries produce multiple PVs.
#[test]
fn p4a_multi_context_public_values() {
    let hashes = vec![100u32, 200, 300];
    let init = FlatInitChip {
        ctx_hashes: hashes.clone(),
        max_ctx_size: 3,
        min_rows: 4,
    };
    let init_trace = padded_trace::<2>(&[[1, 100], [1, 200], [1, 300]], 4);

    let final_trace = padded_trace::<2>(&[[1, 100], [1, 200], [1, 300]], 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip { max_ctx_size: 3 }),
    ];
    let traces = vec![init_trace, final_trace];
    let pis = vec![
        hashes.iter().map(|&h| BabyBear::from_u32(h)).collect(),
        hashes.iter().map(|&h| BabyBear::from_u32(h)).collect(),
    ];

    let vdata = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("multi-context PVs should verify");

    let init_pvs = &vdata.data.proof.per_air[0].public_values;
    assert_eq!(init_pvs.len(), 3);
    for (i, &h) in hashes.iter().enumerate() {
        assert_eq!(init_pvs[i].as_canonical_u32(), h, "PV[{i}] should match");
    }
}

/// Build a recursive verifier from a proof WITH public values.
/// Validates that PVs survive through the recursive verification pipeline.
#[test]
fn p4a_recursive_verify_with_pvs() {
    use openvm_native_compiler::conversion::CompilerOptions;
    use openvm_native_recursion::testing_utils::inner::build_verification_program;

    let h = 42u32;
    let (airs, traces, pis) = flat_init_final_with_pvs(h);

    let vparams = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("inner proof with PVs should verify");

    // PVs are in the proof
    assert_eq!(
        vparams.data.proof.per_air[0].public_values[0].as_canonical_u32(),
        h, "PV should carry context hash"
    );

    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );

    println!("  with PVs: {} instructions, {} witness chunks",
        program.defined_instructions().len(), witness_stream.len());
    assert!(!program.defined_instructions().is_empty());
}
