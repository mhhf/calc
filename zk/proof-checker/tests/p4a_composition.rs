//! Phase 4a-6: Single-advice recursive composition.
//!
//! Builds a recursive verifier program (openvm-native-recursion DSL) that:
//! 1. Verifies N chunk proofs using ONE shared MultiStarkVerificationAdvice
//! 2. Checks PV continuity: chunk[i].final_pvs == chunk[i+1].init_pvs
//! 3. Executes the program to validate correctness
//!
//! This is the core IVC composition test — proves that a single VK suffices
//! for verifying arbitrary chunk counts from the same program.

use openvm_native_compiler::{conversion::CompilerOptions, prelude::*};
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
    fri::TwoAdicFriPcsVariable,
    hints::Hintable,
    stark::StarkVerifier,
    types::{new_from_inner_multi_vk, InnerConfig},
    utils::const_fri_config,
    vars::StarkProofVariable,
};
use openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Config;
use openvm_stark_backend::proof::Proof;
use p3_baby_bear::BabyBear;

use proof_checker::bridge::{prove_chunked_flat_witness, FlatWitnessJson};

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

/// Build a composition program that verifies N proofs with one shared advice
/// and checks PV continuity between adjacent chunks.
///
/// AIR layout (8 AIRs per chunk):
///   0 = FlatInitChip  (PVs = initial context hashes)
///   2 = FlatFinalChip (PVs = final context hashes)
///
/// Continuity: chunk[i].final_pvs[k] == chunk[i+1].init_pvs[k] for all k.
#[test]
fn p4a_composition_verify_and_continuity() {
    // --- 1. Prove all chunks ---
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");
    println!("  proving {} chunks...", chunks.len());

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();

    // Confirm shared VK (Phase 4a-5 invariant)
    for (i, r) in results.iter().enumerate().skip(1) {
        assert_eq!(vk.pre_hash, r.data.vk.pre_hash, "VK mismatch at chunk {i}");
    }

    // Number of PVs per AIR (same across all chunks after normalization)
    let n_init_pvs = results[0].data.proof.per_air[0].public_values.len();
    let n_final_pvs = results[0].data.proof.per_air[2].public_values.len();
    println!("  init PVs: {n_init_pvs}, final PVs: {n_final_pvs}");

    // --- 2. Build composition program ---
    let m_advice = new_from_inner_multi_vk(vk);
    let mut builder = Builder::<InnerConfig>::default();

    let pcs = TwoAdicFriPcsVariable {
        config: const_fri_config(&mut builder, &fri_params),
    };

    // Read Vec<Proof> from hint stream
    let proof_vars: Array<InnerConfig, StarkProofVariable<InnerConfig>> =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::read(&mut builder);
    builder.assert_nonzero(&proof_vars.len());

    // Carry-forward state: previous chunk's final PVs
    // Allocated once, updated each iteration
    let prev_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(n_final_pvs);

    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);

        // Verify this chunk's proof against the shared advice
        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );

        // Extract PVs: init from AIR 0, final from AIR 2
        let init_air = builder.get(&proof.per_air, RVar::from(0));
        let final_air = builder.get(&proof.per_air, RVar::from(2));

        // PV continuity: for i > 0, assert prev_final[k] == init[k]
        builder.if_eq(i, RVar::zero()).then_or_else(
            |_builder| {
                // First proof: nothing to compare yet
            },
            |builder| {
                // Assert: prev chunk's final PVs == this chunk's init PVs
                builder.range(0, init_air.public_values.len()).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_final, k);
                    let init_val = builder.get(&init_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });
            },
        );

        // Update carry-forward: save this chunk's final PVs
        builder.range(0, final_air.public_values.len()).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let val = builder.get(&final_air.public_values, k);
            builder.set(&prev_final, k, val);
        });
    });

    builder.halt();

    let program = builder.compile_isa_with_options(CompilerOptions::default());
    let n_instructions = program.defined_instructions().len();
    println!("  composition program: {n_instructions} instructions");

    // --- 3. Execute the composition program ---
    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);
    println!("  witness stream: {} chunks", input_stream.len());

    openvm_native_circuit::execute_program(program, input_stream);
    println!("  composition executed successfully — {} proofs verified with shared VK", proofs.len());
}
