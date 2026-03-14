//! Phase 4a-4: Per-chunk proving + context continuity verification.
//!
//! Tests:
//! 1. Load chunked fixture (3 chunks from multisig workload)
//! 2. Prove each chunk independently
//! 3. Verify each proof with its own VK
//! 4. Check context continuity: chunk[i].final_pvs == chunk[i+1].init_pvs

use p3_field::PrimeField32;

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
        println!("  chunk {i}: {} AIRs", vdata.data.vk.inner.per_air.len());
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
fn p4a_chunked_vks_differ() {
    // Verify that VKs actually differ across chunks (variable context size)
    let json = load_fixture("multisig_chunked");
    let chunks: Vec<FlatWitnessJson> = serde_json::from_str(&json).expect("parse chunked fixture");

    let results = prove_chunked_flat_witness(&chunks)
        .expect("all chunks should prove and verify");

    // Init PV counts should differ (context grows: 18 → 126 → 220)
    let pv_counts: Vec<usize> = results.iter()
        .map(|r| r.data.proof.per_air[0].public_values.len())
        .collect();
    println!("  init PV counts: {:?}", pv_counts);

    // At least two chunks should have different PV counts
    let all_same = pv_counts.windows(2).all(|w| w[0] == w[1]);
    assert!(!all_same, "VKs should differ due to variable context sizes");
}
