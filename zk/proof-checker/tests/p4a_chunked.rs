//! Phase 4a: Per-chunk proving, context continuity, and constant VK verification.
//!
//! Tests:
//! 1. Load chunked fixture (3 chunks from multisig workload)
//! 2. Prove each chunk independently
//! 3. Verify each proof with its own VK
//! 4. Check context continuity: chunk[i].final_pvs == chunk[i+1].init_pvs
//! 5. Assert VK identity: all chunks produce the same verifier key (constant VK)
//! 6. PV value tampering caught by FLAT_PV_BIND_BUS (init + final)

use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use openvm_stark_sdk::{
    config::{baby_bear_poseidon2::BabyBearPoseidon2Engine, FriParameters},
    engine::StarkFriEngine,
};

use proof_checker::bridge::{build_flat_witness_inputs, prove_chunked_flat_witness, FlatWitnessJson};

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

#[test]
fn p4a_chunked_prove_each_chunk() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    assert!(chunks.len() >= 3, "expected >= 3 chunks, got {}", chunks.len());
    println!("  loaded {} chunks", chunks.len());

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    assert_eq!(results.len(), chunks.len());
    for (i, vdata) in results.iter().enumerate() {
        let n_airs = vdata.data.vk.inner.per_air.len();
        println!("  chunk {i}: {n_airs} AIRs");
        // All chunks should have 8 AIRs (FreevarRomAir + CanonConsRomAir always included)
        assert_eq!(n_airs, 8, "chunk {i} should have 8 AIRs");
    }
}

#[test]
fn p4a_chunked_context_continuity() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    // Check context continuity: chunk[i] final PVs == chunk[i+1] init PVs
    // Init PVs are in per_air[0] (FlatInitChip), final PVs in per_air[2] (FlatFinalChip)
    for i in 0..results.len() - 1 {
        let final_pvs: Vec<u32> = results[i].data.proof.per_air[2].public_values
            .iter()
            .map(|v| v.as_canonical_u32())
            .collect();
        let init_pvs: Vec<u32> = results[i + 1].data.proof.per_air[0].public_values
            .iter()
            .map(|v| v.as_canonical_u32())
            .collect();

        // Sort for comparison (context is a multiset)
        let mut final_sorted = final_pvs.clone();
        final_sorted.sort();
        let mut init_sorted = init_pvs.clone();
        init_sorted.sort();

        assert_eq!(
            final_sorted, init_sorted,
            "chunk {} final PVs should equal chunk {} init PVs",
            i, i + 1
        );
        println!(
            "  chunk {i}→{}: context continuity OK ({} facts)",
            i + 1,
            final_pvs.len()
        );
    }
}

#[test]
fn p4a_chunked_pvs_normalized() {
    // After PV normalization: all chunks have identical PV counts
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    // Init PV counts (per_air[0] = FlatInitChip) should all be the same
    let init_pv_counts: Vec<usize> = results.iter()
        .map(|r| r.data.proof.per_air[0].public_values.len())
        .collect();
    println!("  init PV counts: {:?}", init_pv_counts);
    assert!(init_pv_counts.windows(2).all(|w| w[0] == w[1]),
        "all chunks should have same init PV count after normalization");

    // Final PV counts (per_air[2] = FlatFinalChip) should all be the same
    let final_pv_counts: Vec<usize> = results.iter()
        .map(|r| r.data.proof.per_air[2].public_values.len())
        .collect();
    println!("  final PV counts: {:?}", final_pv_counts);
    assert!(final_pv_counts.windows(2).all(|w| w[0] == w[1]),
        "all chunks should have same final PV count after normalization");

    // Init and final should have the same max_ctx_size
    assert_eq!(init_pv_counts[0], final_pv_counts[0],
        "init and final PV counts should match (same max_ctx_size)");
}

#[test]
fn p4a_chunked_constant_vk() {
    // Phase 4a-5 payoff: all chunks produce identical verifier keys.
    // pre_hash is a Poseidon2 Merkle commitment to the entire VK structure
    // (all per-AIR symbolic constraints, preprocessed commitments, params).
    // Equal pre_hash ⟹ identical VK ⟹ single MultiStarkVerificationAdvice for IVC.
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    let vk0 = &results[0].data.vk;
    for (i, vdata) in results.iter().enumerate().skip(1) {
        assert_eq!(
            vk0.pre_hash, vdata.data.vk.pre_hash,
            "chunk {i} VK pre_hash should equal chunk 0 VK pre_hash"
        );
        println!("  chunk 0 == chunk {i}: VK pre_hash match");
    }
    println!("  pre_hash: {:?}", vk0.pre_hash);
}

// ---------------------------------------------------------------------------
// Forgery: tamper FlatInit hash PV → FLAT_PV_BIND_BUS rejection
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p4a_chunked_tamper_flat_init_pv_fails() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse fixture");

    // Use chunk 0 (always has init context)
    let chunk = &chunks[0];
    let (airs, traces, mut pis) = build_flat_witness_inputs(chunk)
        .expect("build_flat_witness_inputs should succeed");

    // FlatInitChip is AIR index 0, PVs = [hash_0, ..., hash_{max-1}, active_count]
    assert!(!pis[0].is_empty(), "FlatInitChip should have PVs");

    // Tamper hash_0 (first context hash PV) — breaks FLAT_PV_BIND_BUS multiset equality
    pis[0][0] = BabyBear::from_u32(77777);

    let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(2));
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .expect("should not reach — STARK should reject tampered init PV");
}

// ---------------------------------------------------------------------------
// Forgery: tamper FlatFinal hash PV → FLAT_PV_BIND_BUS rejection
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p4a_chunked_tamper_flat_final_pv_fails() {
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse fixture");

    // Use last chunk (always has final context to absorb)
    let chunk = chunks.last().unwrap();
    let (airs, traces, mut pis) = build_flat_witness_inputs(chunk)
        .expect("build_flat_witness_inputs should succeed");

    // FlatFinalChip is AIR index 2, PVs = [hash_0, ..., hash_{max-1}, active_count]
    assert!(!pis[2].is_empty(), "FlatFinalChip should have PVs");

    // Tamper hash_0 (first context hash PV) — breaks FLAT_PV_BIND_BUS multiset equality
    pis[2][0] = BabyBear::from_u32(66666);

    let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(2));
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .expect("should not reach — STARK should reject tampered final PV");
}
