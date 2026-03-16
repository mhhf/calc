//! Phase 6-7+ → Phase 5: Recursive STARK proof for tree path composition.
//!
//! Closes the `execute_program` → `air_test_impl` gap for tree path.
//! Generates a real recursive STARK proof of the composition program,
//! producing a verifiable proof artifact (not just constraint checking).
//!
//! The composition program:
//! 1. Verifies N tree chunk proofs with shared VK
//! 2. Checks PV continuity (ObligBoundary + CtxBoundary)
//! 3. Enforces init_active_count == 0 for non-first chunks (soundness)
//! 4. Commits init/final PVs + VK hash as public values

use openvm_circuit::utils::air_test_impl;
use openvm_native_circuit::{NativeConfig, NativeCpuBuilder};
use openvm_native_compiler::{conversion::CompilerOptions, prelude::*};
use openvm_native_compiler::ir::DIGEST_SIZE;
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
    fri::TwoAdicFriPcsVariable,
    hints::Hintable,
    stark::StarkVerifier,
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
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use proof_checker::bridge::{prove_chunked_tree_witness, WitnessJson};

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

/// Full recursive STARK proof for tree path composition with committed PVs.
///
/// Proves: "these N tree chunks form a valid proof of Γ ⊢ A, verified under program VK."
///
/// Committed PVs:
///   [init_ctx_hashes..., succedent, lax, init_active_count,
///    final_oblig_pvs..., final_ctx_pvs..., vk_pre_hash[0..8]]
///
/// This is the tree-path analog of `p5_composition_full_commitment`.
#[test]
#[ignore] // ~2-5 min — run with: cargo test --release -- --ignored p6_tree_recursive
fn p6_tree_recursive_proof_full_commitment() {
    // --- 1. Prove all chunks ---
    let json = load_fixture("solc_chunked_tree");
    let chunks: Vec<WitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");
    println!("  step 1: proving {} tree chunks...", chunks.len());

    let max_oblig = chunks[0].max_oblig_count.unwrap_or(1);
    let max_ctx = chunks[0].max_boundary_ctx_size.unwrap_or(0);

    let results = prove_chunked_tree_witness(&chunks)
        .expect("all chunks should prove and verify");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();

    let n_airs = vk.inner.per_air.len();
    let init_air_idx = 0;
    let oblig_air_idx = n_airs - 2;
    let ctx_air_idx = n_airs - 1;
    let n_init_pvs = results[0].data.proof.per_air[init_air_idx].public_values.len();
    let n_oblig_pvs = results[0].data.proof.per_air[oblig_air_idx].public_values.len();
    let n_ctx_pvs = results[0].data.proof.per_air[ctx_air_idx].public_values.len();

    // PV commitment layout: init PVs + final oblig PVs + final ctx PVs + VK hash
    let n_final_oblig = max_oblig * 2; // final half of oblig PVs
    let n_final_ctx = max_ctx;          // final half of ctx PVs
    let n_committed = n_init_pvs + n_final_oblig + n_final_ctx + DIGEST_SIZE;
    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();

    // Expected values for verification
    let expected_init: Vec<u32> = results[0].data.proof.per_air[init_air_idx].public_values
        .iter().map(|v| v.as_canonical_u32()).collect();
    let expected_final_oblig: Vec<u32> = results.last().unwrap()
        .data.proof.per_air[oblig_air_idx].public_values[n_final_oblig..]
        .iter().map(|v| v.as_canonical_u32()).collect();
    let expected_final_ctx: Vec<u32> = results.last().unwrap()
        .data.proof.per_air[ctx_air_idx].public_values[n_final_ctx..]
        .iter().map(|v| v.as_canonical_u32()).collect();
    let expected_vk: Vec<u32> = vk_hash.iter().map(|v| v.as_canonical_u32()).collect();

    println!("  init PVs: {n_init_pvs}, final oblig: {n_final_oblig}, final ctx: {n_final_ctx}");
    println!("  committed PVs: {n_committed} (+ {DIGEST_SIZE} VK hash)");

    // --- 2. Build composition program with full commitment ---
    println!("  step 2: building composition with full commitment...");
    let m_advice = new_from_inner_multi_vk(vk);
    let mut builder = Builder::<InnerConfig>::default();
    let pcs = TwoAdicFriPcsVariable {
        config: const_fri_config(&mut builder, &fri_params),
    };

    let proof_vars: Array<InnerConfig, StarkProofVariable<InnerConfig>> =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::read(&mut builder);
    builder.assert_nonzero(&proof_vars.len());

    let prev_oblig_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(max_oblig * 2);
    let prev_ctx_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(max_ctx);
    let first_init: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(n_init_pvs);

    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);

        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );

        let init_air = builder.get(&proof.per_air, RVar::from(init_air_idx));
        let oblig_air = builder.get(&proof.per_air, RVar::from(oblig_air_idx));
        let ctx_air = builder.get(&proof.per_air, RVar::from(ctx_air_idx));

        builder.if_eq(i, RVar::zero()).then_or_else(
            |builder| {
                // First chunk: save init PVs for commitment
                builder.range(0, init_air.public_values.len()).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let val = builder.get(&init_air.public_values, k);
                    builder.set(&first_init, k, val);
                });
            },
            |builder| {
                // Soundness: init_active_count == 0 (last PV of InitChip)
                let init_active_count = builder.get(
                    &init_air.public_values,
                    RVar::from(n_init_pvs - 1),
                );
                let zero: Felt<BabyBear> = builder.constant(BabyBear::ZERO);
                builder.assert_felt_eq(init_active_count, zero);

                // ObligBoundary continuity
                builder.range(0, RVar::from(max_oblig * 2)).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_oblig_final, k);
                    let init_val = builder.get(&oblig_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });

                // CtxBoundary continuity
                builder.range(0, RVar::from(max_ctx)).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_ctx_final, k);
                    let init_val = builder.get(&ctx_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });
            },
        );

        // Update carry-forward
        builder.range(0, RVar::from(max_oblig * 2)).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let offset: Var<_> = builder.eval(k + RVar::from(max_oblig * 2));
            let val = builder.get(&oblig_air.public_values, RVar::Val(offset));
            builder.set(&prev_oblig_final, k, val);
        });
        builder.range(0, RVar::from(max_ctx)).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let offset: Var<_> = builder.eval(k + RVar::from(max_ctx));
            let val = builder.get(&ctx_air.public_values, RVar::Val(offset));
            builder.set(&prev_ctx_final, k, val);
        });
    });

    // --- Commit public values ---
    // Initial sequent identity (chunk[0]'s init PVs including ctx hashes + succedent + lax + active_count)
    builder.commit_public_values(&first_init);
    // Final obligation boundary (last chunk's final oblig PVs)
    builder.commit_public_values(&prev_oblig_final);
    // Final context boundary (last chunk's final ctx PVs)
    builder.commit_public_values(&prev_ctx_final);
    // Program identity (VK pre_hash — DIGEST_SIZE field elements)
    for &h in &vk_hash {
        let val: Felt<BabyBear> = builder.constant(h);
        builder.commit_public_value(val);
    }

    builder.halt();

    let program = builder.compile_isa_with_options(CompilerOptions::default());
    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);
    println!("    {} instructions, {} committed PVs", program.defined_instructions().len(), n_committed);

    // --- 3. Generate recursive STARK proof ---
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
    ).expect("tree recursive proof with full commitment should succeed");

    // --- 4. Verify committed PVs in the recursive proof ---
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

    // Check init PVs (first n_init_pvs entries)
    let mut offset = 0;
    for (k, &expected) in expected_init.iter().enumerate() {
        let actual = pvs[offset + k].as_canonical_u32();
        assert_eq!(actual, expected, "init PV[{k}] mismatch: {actual} != {expected}");
    }
    offset += n_init_pvs;

    // Check final oblig PVs
    for (k, &expected) in expected_final_oblig.iter().enumerate() {
        let actual = pvs[offset + k].as_canonical_u32();
        assert_eq!(actual, expected, "final oblig PV[{k}] mismatch");
    }
    offset += n_final_oblig;

    // Check final ctx PVs
    for (k, &expected) in expected_final_ctx.iter().enumerate() {
        let actual = pvs[offset + k].as_canonical_u32();
        assert_eq!(actual, expected, "final ctx PV[{k}] mismatch");
    }
    offset += n_final_ctx;

    // Check VK pre_hash
    for (k, &expected) in expected_vk.iter().enumerate() {
        let actual = pvs[offset + k].as_canonical_u32();
        assert_eq!(actual, expected, "VK hash[{k}] mismatch");
    }

    println!("  all {} committed PVs verified!", n_committed);
    println!("    init sequent: {n_init_pvs} PVs");
    println!("    final obligs: {n_final_oblig} PVs");
    println!("    final context: {n_final_ctx} PVs");
    println!("    program identity: {DIGEST_SIZE} PVs (VK pre_hash)");
    println!("  tree recursive proof externally verifiable!");
}
