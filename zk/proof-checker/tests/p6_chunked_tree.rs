//! Phase 6-7: chunked tree path tests.
//!
//! Validates that:
//! 1. Each chunk proves independently via STARK verification
//! 2. PV continuity holds across chunk boundaries (obligation + context)

use p3_field::PrimeField32;

use proof_checker::bridge::{prove_chunked_tree_witness, WitnessJson};

fn load_chunked_fixture() -> Vec<WitnessJson> {
    let path = format!(
        "{}/tests/fixtures/solc_chunked_tree.json",
        env!("CARGO_MANIFEST_DIR"),
    );
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture not found at {path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse chunked fixture: {e}"))
}

// ---------------------------------------------------------------------------
// Test: each chunk proves independently
// ---------------------------------------------------------------------------

#[test]
fn p6_chunked_tree_prove_each_chunk() {
    let chunks = load_chunked_fixture();
    assert!(chunks.len() >= 2, "expected >= 2 chunks, got {}", chunks.len());

    let results = prove_chunked_tree_witness(&chunks)
        .expect("all chunks should verify");

    assert_eq!(results.len(), chunks.len());
    for (i, vdata) in results.iter().enumerate() {
        let num_airs = vdata.data.vk.inner.per_air.len();
        println!("  chunk {i}: {num_airs} AIRs");
    }
}

// ---------------------------------------------------------------------------
// Test: obligation PV continuity across boundaries
// ---------------------------------------------------------------------------

#[test]
fn p6_chunked_tree_oblig_continuity() {
    let chunks = load_chunked_fixture();
    let results = prove_chunked_tree_witness(&chunks)
        .expect("all chunks should verify");

    // Find ObligBoundaryChip PVs by expected PV length.
    // max_oblig_count=1 → 4 PVs: [init_goal, init_lax, final_goal, final_lax]
    let max_oblig = chunks[0].max_oblig_count.unwrap_or(1);
    let expected_pv_len = max_oblig * 4;

    for i in 0..results.len() - 1 {
        let cur_oblig_pvs = results[i].data.proof.per_air.iter()
            .find(|a| a.public_values.len() == expected_pv_len);
        let next_oblig_pvs = results[i + 1].data.proof.per_air.iter()
            .find(|a| a.public_values.len() == expected_pv_len);

        if let (Some(cur), Some(next)) = (cur_oblig_pvs, next_oblig_pvs) {
            // cur final obligs = [max_oblig*2 .. max_oblig*4]
            // next init obligs = [0 .. max_oblig*2]
            let cur_final: Vec<u32> = cur.public_values[max_oblig * 2..max_oblig * 4]
                .iter().map(|f| f.as_canonical_u32()).collect();
            let next_init: Vec<u32> = next.public_values[0..max_oblig * 2]
                .iter().map(|f| f.as_canonical_u32()).collect();

            assert_eq!(cur_final, next_init,
                "chunk {i}→{}: obligation PV continuity failed", i + 1);
            println!("  chunk {i}→{}: oblig continuity OK", i + 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Test: context PV continuity across boundaries (multiset comparison)
// ---------------------------------------------------------------------------

#[test]
fn p6_chunked_tree_ctx_continuity() {
    let chunks = load_chunked_fixture();
    let results = prove_chunked_tree_witness(&chunks)
        .expect("all chunks should verify");

    let max_ctx = chunks[0].max_boundary_ctx_size.unwrap_or(0);
    if max_ctx == 0 { return; }
    let expected_pv_len = max_ctx * 2;

    for i in 0..results.len() - 1 {
        let cur_ctx_pvs = results[i].data.proof.per_air.iter()
            .find(|a| a.public_values.len() == expected_pv_len);
        let next_ctx_pvs = results[i + 1].data.proof.per_air.iter()
            .find(|a| a.public_values.len() == expected_pv_len);

        if let (Some(cur), Some(next)) = (cur_ctx_pvs, next_ctx_pvs) {
            let mut cur_final: Vec<u32> = cur.public_values[max_ctx..max_ctx * 2]
                .iter()
                .map(|f| f.as_canonical_u32())
                .filter(|v| *v != 0)
                .collect();
            let mut next_init: Vec<u32> = next.public_values[0..max_ctx]
                .iter()
                .map(|f| f.as_canonical_u32())
                .filter(|v| *v != 0)
                .collect();

            cur_final.sort();
            next_init.sort();

            assert_eq!(cur_final, next_init,
                "chunk {i}→{}: context PV continuity failed", i + 1);
            println!("  chunk {i}→{}: ctx continuity OK ({} facts)", i + 1, cur_final.len());
        }
    }
}
