//! Phase 1f: End-to-end JS → Rust integration tests.
//!
//! Reads JSON fixture files produced by `tests/zk-witness.test.js`,
//! deserializes into trace matrices, and runs the full STARK prover
//! + verifier pipeline. This validates that the JS witness generator
//! produces valid traces for the Rust AIR chips.

use ill_checker::bridge::prove_json;

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
fn e2e_identity() {
    prove_json(&load_fixture("identity")).expect("identity: A ⊢ A");
}

#[test]
fn e2e_tensor_r() {
    prove_json(&load_fixture("tensor_r")).expect("tensor_r: A, B ⊢ A ⊗ B");
}

#[test]
fn e2e_tensor_swap() {
    prove_json(&load_fixture("tensor_swap")).expect("tensor_swap: A ⊗ B ⊢ B ⊗ A");
}

#[test]
fn e2e_loli_r() {
    prove_json(&load_fixture("loli_r")).expect("loli_r: ⊢ A ⊸ A");
}

#[test]
fn e2e_with_r() {
    prove_json(&load_fixture("with_r")).expect("with_r: A ⊢ A & A");
}

#[test]
fn e2e_one_r() {
    prove_json(&load_fixture("one_r")).expect("one_r: ⊢ I");
}
