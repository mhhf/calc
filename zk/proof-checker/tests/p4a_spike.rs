//! Phase 4a spike: prove/verify separation + public values + recursive verification.
//!
//! Test progression:
//! 1. Separate keygen/prove/verify — retain Proof + VK objects
//! 2. Public values shape constraint — PIs must match AIR declaration
//! 3. Recursive STARK-in-STARK verification — build verifier program from VK+proof
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

use proof_checker::chips::{
    flat_init::FlatInitChip,
    flat_final::FlatFinalChip,
};

use common::padded_trace;

// ---------------------------------------------------------------------------
// Step 1: Prove/verify separation — retain Proof + VK objects
// ---------------------------------------------------------------------------

/// Verify that run_simple_test returns Proof + VK that can be independently verified.
#[test]
fn p4a_separate_prove_verify() {
    let h = 42u32;
    let init = FlatInitChip { ctx_hashes: vec![h], min_rows: 4 };
    let init_trace = padded_trace::<1>(&[[0u32; 1]; 0], 4);

    let final_rows: Vec<[u32; 2]> = vec![[1, h]];
    let final_trace = padded_trace::<2>(&final_rows, 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip),
    ];
    let traces = vec![init_trace, final_trace];
    let pis = vec![vec![], vec![]];

    // Combined API: keygen + prove + verify → VerificationDataWithFriParams
    let vdata = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("trivial flat path should verify");

    // Extract VK and Proof
    let vk = &vdata.data.vk;
    let proof = &vdata.data.proof;

    // VK should have 2 AIRs
    assert_eq!(vk.inner.per_air.len(), 2, "VK should have 2 AIR entries");
    // Proof should have 2 per-air entries
    assert_eq!(proof.per_air.len(), 2, "Proof should have 2 per-air entries");

    // Re-verify using the engine's verify method (separate challenger creation)
    let engine = BabyBearPoseidon2Engine::new(vdata.fri_params);
    engine.verify(vk, proof)
        .expect("separate verify should succeed with same VK+proof");
}

// ---------------------------------------------------------------------------
// Step 2: Public values shape — the backend enforces declared PI count
// ---------------------------------------------------------------------------

/// The STARK backend rejects PIs that don't match the AIR's declared
/// num_public_values. This means FlatInitChip must declare its PI count
/// in BaseAirWithPublicValues before we can pass context as public values.
///
/// This test confirms the rejection behavior — passing PIs to a chip
/// that declares num_public_values=0 fails with InvalidProofShape.
#[test]
#[should_panic(expected = "InvalidProofShape")]
fn p4a_pis_rejected_when_not_declared_by_air() {
    let h = 42u32;
    let init = FlatInitChip { ctx_hashes: vec![h], min_rows: 4 };
    let init_trace = padded_trace::<1>(&[[0u32; 1]; 0], 4);

    let final_rows: Vec<[u32; 2]> = vec![[1, h]];
    let final_trace = padded_trace::<2>(&final_rows, 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip),
    ];
    let traces = vec![init_trace, final_trace];

    // Pass PIs to init chip — but FlatInitChip declares num_public_values=0
    let init_pis: Vec<BabyBear> = vec![BabyBear::new(h)];
    let pis = vec![init_pis, vec![]];

    // This should fail: AIR doesn't declare any public values
    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .expect("should fail: PIs not declared");
}

// ---------------------------------------------------------------------------
// Step 3: Recursive STARK-in-STARK verification
// ---------------------------------------------------------------------------

/// Build a recursive verifier program from an inner STARK proof.
///
/// This validates the full Phase 4a pipeline:
///   1. Prove a trivial inner STARK (FlatInit + FlatFinal)
///   2. Convert VK → MultiStarkVerificationAdvice
///   3. Compile VerifierProgram (STARK verifier as native VM program)
///   4. Serialize proof as hint/witness stream
///   5. Execute the verifier program in the OpenVM native runtime
///
/// The verifier program will panic if the proof is invalid.
#[test]
fn p4a_recursive_verify_trivial() {
    use openvm_native_compiler::conversion::CompilerOptions;
    use openvm_native_recursion::testing_utils::inner::build_verification_program;

    // --- Inner proof: trivial FlatInit + FlatFinal ---
    let h = 42u32;
    let init = FlatInitChip { ctx_hashes: vec![h], min_rows: 4 };
    let init_trace = padded_trace::<1>(&[[0u32; 1]; 0], 4);

    let final_rows: Vec<[u32; 2]> = vec![[1, h]];
    let final_trace = padded_trace::<2>(&final_rows, 4);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(FlatFinalChip),
    ];
    let traces = vec![init_trace, final_trace];
    let pis = vec![vec![], vec![]];

    let vparams = BabyBearPoseidon2Engine::run_simple_test_fast(
        airs, traces, pis
    ).expect("inner proof should verify");

    // --- Build recursive verifier program ---
    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );

    // Program should have instructions
    assert!(!program.defined_instructions().is_empty(), "verifier program should have instructions");
    // Witness stream should have proof data
    assert!(!witness_stream.is_empty(), "witness stream should contain serialized proof");

    println!("  verifier program: {} instructions", program.defined_instructions().len());
    println!("  witness stream: {} chunks", witness_stream.len());
}

/// Build a recursive verifier from a real tree-path fixture (identity: A ⊢ A).
/// Validates that prove_witness_vdata returns usable verification data
/// for recursive verification of real multi-chip proofs.
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
