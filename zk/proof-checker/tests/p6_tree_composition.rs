//! Phase 6-7+: Single-advice recursive composition for tree path chunks.
//!
//! Analogous to p4a_composition (flat path), builds a recursive verifier program
//! that verifies N tree chunk proofs using ONE shared MultiStarkVerificationAdvice
//! and checks PV continuity for ObligBoundaryChip and CtxBoundaryChip.

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

/// Recursive composition for tree path chunks.
///
/// ObligBoundaryChip and CtxBoundaryChip are the last two AIRs (in that order).
/// PV layout:
///   ObligBoundary: [init_goal_0, init_lax_0, ..., final_goal_0, final_lax_0, ...]
///   CtxBoundary:   [init_hash_0, ..., init_hash_N, final_hash_0, ..., final_hash_N]
///
/// Continuity:
///   chunk[i].ObligBoundary.final == chunk[i+1].ObligBoundary.init
///   chunk[i].CtxBoundary.final  == chunk[i+1].CtxBoundary.init
#[test]
fn p6_tree_composition_verify_and_continuity() {
    // --- 1. Prove all chunks ---
    let json = load_fixture("solc_chunked_tree");
    let chunks: Vec<WitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");
    println!("  proving {} tree chunks...", chunks.len());

    let max_oblig = chunks[0].max_oblig_count.unwrap_or(1);
    let max_ctx = chunks[0].max_boundary_ctx_size.unwrap_or(0);

    let results = prove_chunked_tree_witness(&chunks)
        .expect("all chunks should prove and verify");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();

    // Confirm shared VK (constant VK invariant)
    for (i, r) in results.iter().enumerate().skip(1) {
        assert_eq!(vk.pre_hash, r.data.vk.pre_hash, "VK mismatch at chunk {i}");
    }

    let n_airs = results[0].data.vk.inner.per_air.len();
    println!("  {n_airs} AIRs, max_oblig={max_oblig}, max_ctx={max_ctx}");

    // Boundary chip AIR indices: ObligBoundary is second-to-last, CtxBoundary is last
    let oblig_air_idx = n_airs - 2;
    let ctx_air_idx = n_airs - 1;
    let n_oblig_pvs = max_oblig * 4; // [init_goal, init_lax] * N + [final_goal, final_lax] * N
    let n_ctx_pvs = max_ctx * 2;     // [init_hash] * N + [final_hash] * N

    // Verify PV sizes match expectations
    assert_eq!(results[0].data.proof.per_air[oblig_air_idx].public_values.len(), n_oblig_pvs,
        "ObligBoundary PV count mismatch");
    assert_eq!(results[0].data.proof.per_air[ctx_air_idx].public_values.len(), n_ctx_pvs,
        "CtxBoundary PV count mismatch");

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

    // Carry-forward: previous chunk's final PVs for both boundary chips
    let prev_oblig_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(max_oblig * 2);
    let prev_ctx_final: Array<InnerConfig, Felt<BabyBear>> = builder.dyn_array(max_ctx);

    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);

        // Verify this chunk's proof against the shared advice
        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );

        // Extract boundary chip AIR data
        let oblig_air = builder.get(&proof.per_air, RVar::from(oblig_air_idx));
        let ctx_air = builder.get(&proof.per_air, RVar::from(ctx_air_idx));

        // PV continuity: for i > 0, check prev final == current init
        builder.if_eq(i, RVar::zero()).then_or_else(
            |_builder| {
                // First chunk: nothing to compare yet
            },
            |builder| {
                // ObligBoundary: prev_final[k] == init[k] for k in 0..max_oblig*2
                builder.range(0, RVar::from(max_oblig * 2)).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_oblig_final, k);
                    let init_val = builder.get(&oblig_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });

                // CtxBoundary: prev_final[k] == init[k] for k in 0..max_ctx
                builder.range(0, RVar::from(max_ctx)).for_each(|k_vec, builder| {
                    let k = k_vec[0];
                    let prev_val = builder.get(&prev_ctx_final, k);
                    let init_val = builder.get(&ctx_air.public_values, k);
                    builder.assert_felt_eq(prev_val, init_val);
                });
            },
        );

        // Update carry-forward: save this chunk's final PVs
        // ObligBoundary final = pvs[max_oblig*2 .. max_oblig*4]
        builder.range(0, RVar::from(max_oblig * 2)).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let offset: Var<_> = builder.eval(k + RVar::from(max_oblig * 2));
            let val = builder.get(&oblig_air.public_values, RVar::Val(offset));
            builder.set(&prev_oblig_final, k, val);
        });

        // CtxBoundary final = pvs[max_ctx .. max_ctx*2]
        builder.range(0, RVar::from(max_ctx)).for_each(|k_vec, builder| {
            let k = k_vec[0];
            let offset: Var<_> = builder.eval(k + RVar::from(max_ctx));
            let val = builder.get(&ctx_air.public_values, RVar::Val(offset));
            builder.set(&prev_ctx_final, k, val);
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
    println!("  composition executed — {} tree proofs verified with shared VK", proofs.len());
}
