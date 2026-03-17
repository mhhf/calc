//! Phase 6-7+: Single-advice recursive composition for tree path chunks.
//!
//! Analogous to p4a_composition (flat path), builds a recursive verifier program
//! that verifies N tree chunk proofs using ONE shared MultiStarkVerificationAdvice
//! and checks PV continuity for ObligBoundaryChip and CtxBoundaryChip.
//!
//! Soundness: also verifies InitChip's `init_active_count` PV == 0 for chunks > 0,
//! preventing re-injection of the initial context/obligations.

use openvm_native_circuit::NativeCpuBuilder;
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
use openvm_stark_sdk::config::baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine};
use openvm_stark_backend::proof::Proof;
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

/// Recursive composition for tree path chunks.
///
/// InitChip is AIR 0. Its last PV is `init_active_count` — constrained by the AIR
/// running-sum to equal sum(is_active). The recursive verifier checks this == 0
/// for all chunks after the first, preventing re-injection of context/obligations.
///
/// ObligBoundaryChip and CtxBoundaryChip are the last two AIRs (in that order).
/// PV layout:
///   InitChip:      [...ctx_hashes, succedent, lax, init_active_count]
///   ObligBoundary: [init_goal_0, init_lax_0, ..., final_goal_0, final_lax_0, ...]
///   CtxBoundary:   [init_hash_0, ..., init_hash_N, final_hash_0, ..., final_hash_N]
///
/// Continuity:
///   chunk[i].ObligBoundary.final == chunk[i+1].ObligBoundary.init
///   chunk[i].CtxBoundary.final  == chunk[i+1].CtxBoundary.init
/// Soundness:
///   chunk[i>0].InitChip.init_active_count == 0
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

    // AIR indices
    let init_air_idx = 0;
    let oblig_air_idx = n_airs - 2;
    let ctx_air_idx = n_airs - 1;
    let n_init_pvs = results[0].data.proof.per_air[init_air_idx].public_values.len();
    let n_oblig_pvs = max_oblig * 4 + 2;
    let n_ctx_pvs = max_ctx * 2 + 2;

    // Verify PV sizes match expectations
    assert_eq!(results[0].data.proof.per_air[oblig_air_idx].public_values.len(), n_oblig_pvs,
        "ObligBoundary PV count mismatch");
    assert_eq!(results[0].data.proof.per_air[ctx_air_idx].public_values.len(), n_ctx_pvs,
        "CtxBoundary PV count mismatch");

    // Verify init_active_count is correct for each chunk
    for (i, r) in results.iter().enumerate() {
        let init_pvs = &r.data.proof.per_air[init_air_idx].public_values;
        let active_count = init_pvs.last().unwrap().as_canonical_u32();
        if i == 0 {
            assert!(active_count > 0, "chunk 0 should have active init rows");
        } else {
            assert_eq!(active_count, 0, "chunk {i} should have init_active_count=0");
        }
    }

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

        // Extract AIR data
        let init_air = builder.get(&proof.per_air, RVar::from(init_air_idx));
        let oblig_air = builder.get(&proof.per_air, RVar::from(oblig_air_idx));
        let ctx_air = builder.get(&proof.per_air, RVar::from(ctx_air_idx));

        // Soundness check: for i > 0, InitChip's init_active_count must be 0.
        // This prevents re-injection of context/obligations from the initial sequent.
        // The AIR's running-sum constraint ensures PV == sum(is_active), so
        // PV == 0 ⟹ every is_active == 0 ⟹ no bus sends fire.
        builder.if_eq(i, RVar::zero()).then_or_else(
            |_builder| {
                // First chunk: init is active, nothing to compare for boundary PVs
            },
            |builder| {
                // Assert init_active_count == 0 (last PV of InitChip)
                let init_active_count = builder.get(
                    &init_air.public_values,
                    RVar::from(n_init_pvs - 1),
                );
                let zero: Felt<BabyBear> = builder.constant(BabyBear::ZERO);
                builder.assert_felt_eq(init_active_count, zero);

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

    // Run the composition program via metered interpreter.
    // Uses NativeConfig::aggregation to avoid OpenVM debug_assert bug in metered memory:
    // test_native_config() allocates PUBLIC_VALUES_AS with num_cells>0 (U8 space, align_bits=2),
    // but chunk_bits=0 from initial_block_size=1. apply_height_updates passes chunk_bits as
    // size_bits → debug_assert!(2 <= 0) fails. aggregation() only allocates NATIVE_AS (align_bits=0).
    {
        use openvm_stark_sdk::{config::FriParameters, engine::StarkFriEngine};
        use openvm_circuit::arch::{instructions::exe::VmExe, Streams, VirtualMachine};

        let config = openvm_native_circuit::NativeConfig::aggregation(4, 3);
        let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(1));
        let exe = VmExe::new(program);
        let (vm, _) = VirtualMachine::<_, NativeCpuBuilder>::new_with_keygen(
            engine, NativeCpuBuilder, config,
        ).unwrap();
        let ctx = vm.build_metered_ctx(&exe);
        let (segments, _) = vm
            .metered_interpreter(&exe).unwrap()
            .execute_metered(Streams::from(input_stream), ctx).unwrap();
        println!("  composition executed in {} segment(s) — {} tree proofs verified with shared VK",
            segments.len(), proofs.len());
    }
}

/// Soundness tamper test: set is_active=1 on a non-first chunk's init rows.
///
/// Defense-in-depth: two layers catch this attack.
///
/// Layer 1 (bus balance): When is_active=1, InitChip fires CONTEXT_BUS and
/// OBLIG_BUS sends. On non-first chunks these sends have no matching receives,
/// causing LogUp multiset equality failure at the individual chunk STARK level.
///
/// Layer 2 (recursive verifier): Even if bus balance somehow passed (e.g.
/// accidental send/receive match), the running-sum PV constraint ensures
/// init_active_count > 0, which the recursive verifier explicitly rejects.
///
/// This test verifies Layer 1: prove_chunked_tree_witness panics on bus imbalance.
#[test]
#[should_panic(expected = "LogUp multiset equality check failed")]
fn p6_tree_composition_tampered_is_active_rejected() {
    let json = load_fixture("solc_chunked_tree");
    let mut chunks: Vec<WitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    // Tamper: set is_active=1 on chunk 1's init rows (re-inject context/obligations)
    let init_rows = chunks[1].chips.get_mut("init").expect("init chip in chunk 1");
    for row in init_rows.iter_mut() {
        if row.len() >= 7 {
            row[6] = 1; // is_active = 1 (was 0)
        }
    }

    // Bus balance catches this: InitChip sends on CONTEXT_BUS/OBLIG_BUS
    // have no matching receives on non-first chunks → LogUp failure
    prove_chunked_tree_witness(&chunks)
        .expect("should not reach here — STARK proving panics on bus imbalance");
}
