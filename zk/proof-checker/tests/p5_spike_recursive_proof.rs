//! Phase 5 spike: actually generate a recursive STARK proof (not just execute).
//!
//! Phase 4a-6 `execute_program` validates DSL logic but produces NO proof.
//! This test calls `air_test_impl` to keygen → prove → verify the verifier program,
//! producing a real recursive STARK proof of the composition.

use openvm_circuit::utils::air_test_impl;
use openvm_native_circuit::{test_native_config, NativeCpuBuilder};
use openvm_native_compiler::conversion::CompilerOptions;
use openvm_native_recursion::testing_utils::inner::build_verification_program;
use openvm_stark_sdk::config::{
    baby_bear_poseidon2::BabyBearPoseidon2Engine,
    FriParameters,
};

use proof_checker::bridge::{prove_flat_witness_vdata, FlatWitnessJson};

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

/// Spike: recursive proof of the composition program (multi-proof, PV continuity).
/// This proves the Phase 4a-6 composition program itself, not just a single inner proof.
/// Expected to be ~3x slower than single chunk due to ~20K instructions × 3 proofs.
#[test]
#[ignore] // ~2-5 min expected — run with: cargo test --release -- --ignored
fn p5_recursive_proof_composition() {
    use openvm_native_compiler::prelude::*;
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

    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse");

    println!("  step 1: proving {} chunks...", chunks.len());
    let results = prove_chunked_flat_witness(&chunks).expect("chunk proving");
    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone()).collect();

    println!("  step 2: building composition program...");
    let n_init_pvs = results[0].data.proof.per_air[0].public_values.len();
    let n_final_pvs = results[0].data.proof.per_air[2].public_values.len();

    let m_advice = new_from_inner_multi_vk(vk);
    let mut builder = Builder::<InnerConfig>::default();
    let pcs = TwoAdicFriPcsVariable {
        config: const_fri_config(&mut builder, &fri_params),
    };
    let proof_vars: Array<InnerConfig, StarkProofVariable<InnerConfig>> =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::read(&mut builder);
    builder.assert_nonzero(&proof_vars.len());
    let prev_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(n_final_pvs);

    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);
        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );
        let init_air = builder.get(&proof.per_air, RVar::from(0));
        let final_air = builder.get(&proof.per_air, RVar::from(2));
        builder.if_eq(i, RVar::zero()).then_or_else(
            |_builder| {},
            |builder| {
                builder.range(0, init_air.public_values.len()).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_final, k);
                    let init_val = builder.get(&init_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });
            },
        );
        builder.range(0, final_air.public_values.len()).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let val = builder.get(&final_air.public_values, k);
            builder.set(&prev_final, k, val);
        });
    });
    builder.halt();

    let program = builder.compile_isa_with_options(CompilerOptions::default());
    let n_instructions = program.defined_instructions().len();
    println!("    {} instructions", n_instructions);

    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);
    println!("    {} witness chunks", input_stream.len());

    // Step 3: Prove the composition program (recursive STARK proof!)
    println!("  step 3: generating recursive STARK proof of composition...");
    let rec_fri = FriParameters::new_for_testing(3);
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        rec_fri,
        NativeCpuBuilder,
        test_native_config(),
        program,
        input_stream,
        1,
        true,
    ).expect("recursive composition proof should succeed");

    println!("  recursive composition proof OK! {} segments", vdata_vec.len());
    for (i, vd) in vdata_vec.iter().enumerate() {
        println!("    segment {i}: {} VK AIRs, {} proof AIRs",
            vd.data.vk.inner.per_air.len(),
            vd.data.proof.per_air.len());
    }
}

/// Spike: generate a recursive STARK proof for a single-chunk flat witness.
/// This is the minimal test: prove a flat witness, build a verifier program,
/// then prove the verifier program itself (= recursive STARK proof).
#[test]
fn p5_recursive_proof_single_chunk() {
    // Step 1: Prove a flat witness (inner proof)
    let json = load_fixture("solc_flat");
    let witness: FlatWitnessJson = serde_json::from_str(&json).expect("parse flat fixture");

    println!("  proving inner flat witness...");
    let vparams = prove_flat_witness_vdata(&witness)
        .expect("inner flat proof should succeed");

    let n_airs = vparams.data.vk.inner.per_air.len();
    println!("  inner proof: {} AIRs", n_airs);

    // Step 2: Build verifier program from the proof + VK
    println!("  building verifier program...");
    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );
    println!("  verifier program: {} instructions, {} witness chunks",
        program.defined_instructions().len(), witness_stream.len());

    // Step 3: Actually prove the verifier program (recursive STARK proof!)
    // This is what Phase 4a was missing — execute_program only runs, doesn't prove.
    // air_test_impl does: keygen → segmented execution → prove → verify
    println!("  generating recursive STARK proof...");
    let fri_params = FriParameters::new_for_testing(3);

    let result = air_test_impl::<BabyBearPoseidon2Engine, _>(
        fri_params,
        NativeCpuBuilder,
        test_native_config(),
        program,
        witness_stream,
        1,    // min_segments
        true, // debug
    );

    match result {
        Ok((memory_image, vdata_vec)) => {
            println!("  recursive proof generated successfully!");
            println!("  segments: {}", vdata_vec.len());
            for (i, vdata) in vdata_vec.iter().enumerate() {
                let n_airs = vdata.data.vk.inner.per_air.len();
                let n_proof_airs = vdata.data.proof.per_air.len();
                println!("  segment {i}: {n_airs} AIRs, {n_proof_airs} proof AIRs");
            }
            println!("  memory image present: {}", memory_image.is_some());
        }
        Err(e) => {
            // Log the error details for research — don't panic yet
            println!("  recursive proof FAILED: {e:?}");
            panic!("recursive proof generation failed: {e}");
        }
    }
}
