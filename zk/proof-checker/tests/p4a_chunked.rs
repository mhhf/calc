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
        let n_airs = vdata.data.vk.inner.per_air.len();
        println!("  chunk {i}: {n_airs} AIRs");
        // All chunks should have 7 AIRs (FreevarRomAir always included)
        assert_eq!(n_airs, 7, "chunk {i} should have 7 AIRs");
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
