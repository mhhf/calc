//! Phase 5: Recursive STARK proof generation + public value commitment.
//!
//! Phase 4a-6 `execute_program` validates DSL logic but produces NO proof.
//! These tests use `air_test_impl` to generate real recursive STARK proofs.
//!
//! Test progression:
//! 1. p5_recursive_proof_single_chunk — prove a single-proof verifier program
//! 2. p5_recursive_proof_composition — prove the multi-chunk composition program
//! 3. p5_composition_full_commitment — full commitment: init PVs + final PVs + VK identity (Phase 5-2)

use openvm_circuit::utils::air_test_impl;
use openvm_native_circuit::{test_native_config, NativeConfig, NativeCpuBuilder};
use openvm_native_compiler::{conversion::CompilerOptions, prelude::*};
use openvm_native_compiler::ir::DIGEST_SIZE;
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
    fri::TwoAdicFriPcsVariable,
    hints::Hintable,
    stark::StarkVerifier,
    testing_utils::inner::build_verification_program,
    types::{new_from_inner_multi_vk, InnerConfig},
    utils::const_fri_config,
    vars::StarkProofVariable,
};
use openvm_stark_backend::proof::Proof;
use openvm_stark_sdk::config::{
    baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
    FriParameters,
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;

use proof_checker::bridge::{
    prove_chunked_flat_witness, prove_flat_witness_vdata, FlatWitnessJson,
};

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

/// Build the composition program with committed public values.
///
/// The program:
/// 1. Verifies N chunk proofs with one shared MultiStarkVerificationAdvice
/// 2. Checks PV continuity: chunk[i].final_pvs == chunk[i+1].init_pvs
/// 3. Commits chunk[0].init_pvs as public values (initial context)
/// 4. Commits chunk[N-1].final_pvs as public values (final context)
/// 5. Commits VK pre_hash (DIGEST_SIZE=8 elements) as program identity
///
/// PV layout: [init_pvs..., final_pvs..., vk_pre_hash[0..8]]
///
/// Returns (program, witness_stream, n_committed_pvs).
fn build_composition_with_pvs(
    results: &[openvm_stark_sdk::engine::VerificationDataWithFriParams<BabyBearPoseidon2Config>],
) -> (openvm_circuit::arch::instructions::program::Program<BabyBear>, Vec<Vec<BabyBear>>, usize) {
    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone()).collect();

    let n_init_pvs = results[0].data.proof.per_air[0].public_values.len();
    let n_final_pvs = results[0].data.proof.per_air[2].public_values.len();
    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();
    let n_committed = n_init_pvs + n_final_pvs + DIGEST_SIZE;

    let m_advice = new_from_inner_multi_vk(vk);
    let mut builder = Builder::<InnerConfig>::default();
    let pcs = TwoAdicFriPcsVariable {
        config: const_fri_config(&mut builder, &fri_params),
    };

    // Read all proofs from hint stream
    let proof_vars: Array<InnerConfig, StarkProofVariable<InnerConfig>> =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::read(&mut builder);
    builder.assert_nonzero(&proof_vars.len());

    // Carry-forward state
    let prev_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(n_final_pvs);
    let first_init: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(n_init_pvs);

    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);

        // Verify this chunk's proof against the shared advice
        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );

        let init_air = builder.get(&proof.per_air, RVar::from(0));
        let final_air = builder.get(&proof.per_air, RVar::from(2));

        builder.if_eq(i, RVar::zero()).then_or_else(
            |builder| {
                // First proof: save init PVs for later commitment
                builder.range(0, init_air.public_values.len()).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let val = builder.get(&init_air.public_values, k);
                    builder.set(&first_init, k, val);
                });
            },
            |builder| {
                // Subsequent proofs: assert PV continuity
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

    // --- Commit public values ---
    // Initial context (chunk[0]'s init PVs)
    builder.commit_public_values(&first_init);
    // Final context (last chunk's final PVs)
    builder.commit_public_values(&prev_final);
    // Program identity (VK pre_hash — 8 BabyBear field elements)
    for &h in &vk_hash {
        let val: Felt<BabyBear> = builder.constant(h);
        builder.commit_public_value(val);
    }

    builder.halt();

    let program = builder.compile_isa_with_options(CompilerOptions::default());
    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);

    (program, input_stream, n_committed)
}

// ---------------------------------------------------------------------------
// Phase 5-0: Recursive STARK proof spike (no PV commitment)
// ---------------------------------------------------------------------------

/// Spike: generate a recursive STARK proof for a single-chunk flat witness.
#[test]
fn p5_recursive_proof_single_chunk() {
    let json = load_fixture("solc_flat");
    let witness: FlatWitnessJson = serde_json::from_str(&json).expect("parse flat fixture");

    println!("  proving inner flat witness...");
    let vparams = prove_flat_witness_vdata(&witness)
        .expect("inner flat proof should succeed");
    println!("  inner proof: {} AIRs", vparams.data.vk.inner.per_air.len());

    println!("  building verifier program...");
    let (program, witness_stream) = build_verification_program(
        vparams,
        CompilerOptions::default(),
    );
    println!("  verifier program: {} instructions, {} witness chunks",
        program.defined_instructions().len(), witness_stream.len());

    println!("  generating recursive STARK proof...");
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
        NativeCpuBuilder,
        test_native_config(),
        program,
        witness_stream,
        1,
        true,
    ).expect("recursive proof should succeed");

    println!("  recursive proof OK! {} segments", vdata_vec.len());
    for (i, vd) in vdata_vec.iter().enumerate() {
        println!("    segment {i}: {} VK AIRs, {} proof AIRs",
            vd.data.vk.inner.per_air.len(),
            vd.data.proof.per_air.len());
    }
}

/// Recursive proof of the composition program (no PV commitment).
#[test]
#[ignore] // ~2-5 min — run with: cargo test --release -- --ignored
fn p5_recursive_proof_composition() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse");

    println!("  step 1: proving {} chunks...", chunks.len());
    let results = prove_chunked_flat_witness(&chunks).expect("chunk proving");
    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone()).collect();

    println!("  step 2: building composition program (no PV commitment)...");
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
    println!("    {} instructions", program.defined_instructions().len());
    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);
    println!("    {} witness chunks", input_stream.len());

    println!("  step 3: generating recursive STARK proof...");
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
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

// ---------------------------------------------------------------------------
// Phase 5-2: Full commitment — init PVs + final PVs + VK pre_hash
// ---------------------------------------------------------------------------

/// Composition with full commitment: the recursive proof carries:
/// - chunk[0].init_pvs (initial context)
/// - chunk[N-1].final_pvs (final context)
/// - VK pre_hash[0..8] (program identity)
///
/// PV layout: [init_pvs..., final_pvs..., vk_pre_hash[0..8]]
///
/// An external verifier can check:
///   "this proof certifies ctx_in → ctx_out under program P"
/// where P = VK pre_hash identifies the specific ILL program.
#[test]
#[ignore] // ~2-5 min — run with: cargo test --release -- --ignored p5_composition_full_commitment
fn p5_composition_full_commitment() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse");

    println!("  step 1: proving {} chunks...", chunks.len());
    let results = prove_chunked_flat_witness(&chunks).expect("chunk proving");

    // Expected PV values from inner proofs
    let expected_init: Vec<u32> = results[0].data.proof.per_air[0].public_values
        .iter().map(|v| v.as_canonical_u32()).collect();
    let expected_final: Vec<u32> = results.last().unwrap().data.proof.per_air[2].public_values
        .iter().map(|v| v.as_canonical_u32()).collect();
    let vk_hash: [BabyBear; DIGEST_SIZE] = results[0].data.vk.pre_hash.clone().into();
    let expected_vk: Vec<u32> = vk_hash.iter().map(|v| v.as_canonical_u32()).collect();
    let n_init = expected_init.len();
    let n_final = expected_final.len();
    println!("  init PVs: {n_init}, final PVs: {n_final}, VK hash: {DIGEST_SIZE} elements");

    // Step 2: Build composition program with full commitment
    println!("  step 2: building composition with full commitment...");
    let (program, input_stream, n_committed) = build_composition_with_pvs(&results);
    println!("    {} instructions, {} committed PVs", program.defined_instructions().len(), n_committed);
    assert_eq!(n_committed, n_init + n_final + DIGEST_SIZE);

    // Step 3: Generate recursive STARK proof with PV-aware config
    println!("  step 3: generating recursive STARK proof...");
    let config = NativeConfig::aggregation(n_committed, 3);
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
        NativeCpuBuilder,
        config,
        program,
        input_stream,
        1,
        true,
    ).expect("recursive proof with full commitment should succeed");

    // Step 4: Verify all committed PVs in the recursive proof
    assert_eq!(vdata_vec.len(), 1, "single segment expected");
    let vdata = &vdata_vec[0];

    // Find the PublicValues AIR by matching expected PV count
    let pv_counts: Vec<usize> = vdata.data.proof.per_air.iter()
        .map(|a| a.public_values.len()).collect();
    println!("  AIR PV counts: {:?}", pv_counts);

    let pv_air_idx = pv_counts.iter().position(|&n| n == n_committed)
        .unwrap_or_else(|| panic!(
            "no AIR with {} PVs found; counts: {:?}", n_committed, pv_counts
        ));
    let pvs = &vdata.data.proof.per_air[pv_air_idx].public_values;
    println!("  PV AIR at index {pv_air_idx}, {} public values", pvs.len());

    // Check init PVs (first n_init entries)
    for (k, &expected) in expected_init.iter().enumerate() {
        let actual = pvs[k].as_canonical_u32();
        assert_eq!(actual, expected, "init PV[{k}] mismatch: {actual} != {expected}");
    }

    // Check final PVs (next n_final entries)
    for (k, &expected) in expected_final.iter().enumerate() {
        let actual = pvs[n_init + k].as_canonical_u32();
        assert_eq!(actual, expected, "final PV[{k}] mismatch: {actual} != {expected}");
    }

    // Check VK pre_hash (last DIGEST_SIZE entries)
    let vk_offset = n_init + n_final;
    for (k, &expected) in expected_vk.iter().enumerate() {
        let actual = pvs[vk_offset + k].as_canonical_u32();
        assert_eq!(actual, expected, "VK hash[{k}] mismatch: {actual} != {expected}");
    }

    println!("  all {} committed PVs verified!", n_committed);
    println!("    init context: {n_init} PVs");
    println!("    final context: {n_final} PVs");
    println!("    program identity: {DIGEST_SIZE} PVs (VK pre_hash)");
    println!("  recursive proof externally verifiable: ctx_in → ctx_out under program P");
}
