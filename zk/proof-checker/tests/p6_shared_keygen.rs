//! Tests for ROM normalization + shared keygen proving.
//!
//! Validates that `normalize_tree_witnesses` + `prove_witnesses_shared_keygen`
//! produce valid STARK proofs with identical VKs across all witnesses.
//!
//! Run: `cargo test --test p6_shared_keygen --release`

use proof_checker::bridge::{
    normalize_tree_witnesses, prove_witnesses_shared_keygen, WitnessJson,
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

fn parse_witness(json: &str) -> WitnessJson {
    serde_json::from_str(json).expect("parse WitnessJson")
}

/// Normalize 3 fixtures and prove with shared keygen.
/// Verifies: all proofs succeed, all VKs identical.
#[test]
fn p6_shared_keygen_3_fixtures() {
    let jsons: Vec<String> = (0..3)
        .map(|i| load_fixture(&format!("solc_symbolic_{i:03}")))
        .collect();
    let mut witnesses: Vec<WitnessJson> = jsons.iter().map(|j| parse_witness(j)).collect();

    let t0 = std::time::Instant::now();
    normalize_tree_witnesses(&mut witnesses);
    eprintln!("  normalization: {:.2}s", t0.elapsed().as_secs_f64());

    let t1 = std::time::Instant::now();
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");
    eprintln!("  shared keygen prove (3 fixtures): {:.2}s", t1.elapsed().as_secs_f64());

    assert_eq!(results.len(), 3);

    // All VKs must be identical (the whole point of normalization)
    // VK doesn't implement Debug, so serialize to bytes for comparison
    let vk0_bytes = serde_json::to_vec(&results[0].data.vk).unwrap();
    for (i, r) in results.iter().enumerate().skip(1) {
        let vki_bytes = serde_json::to_vec(&r.data.vk).unwrap();
        assert_eq!(vk0_bytes, vki_bytes, "VK mismatch: witness 0 vs witness {i}");
    }
    eprintln!("  VK identity verified across 3 fixtures");
}

/// Normalize all 31 fixtures and prove with shared keygen.
/// This is the full symbolic exploration — the primary benchmark target.
#[test]
fn p6_shared_keygen_all_31() {
    let jsons: Vec<String> = (0..31)
        .map(|i| load_fixture(&format!("solc_symbolic_{i:03}")))
        .collect();
    let mut witnesses: Vec<WitnessJson> = jsons.iter().map(|j| parse_witness(j)).collect();

    let t0 = std::time::Instant::now();
    normalize_tree_witnesses(&mut witnesses);
    eprintln!("  normalization: {:.2}s", t0.elapsed().as_secs_f64());

    let t1 = std::time::Instant::now();
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");
    let elapsed = t1.elapsed().as_secs_f64();
    eprintln!("  shared keygen prove (31 fixtures): {:.2}s", elapsed);

    assert_eq!(results.len(), 31);

    // All VKs identical
    let vk0_bytes = serde_json::to_vec(&results[0].data.vk).unwrap();
    for (i, r) in results.iter().enumerate().skip(1) {
        let vki_bytes = serde_json::to_vec(&r.data.vk).unwrap();
        assert_eq!(vk0_bytes, vki_bytes, "VK mismatch: witness 0 vs witness {i}");
    }
    eprintln!("  VK identity verified across 31 fixtures");
    eprintln!("  avg per fixture: {:.2}s", elapsed / 31.0);
}
