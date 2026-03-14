//! Phase 1f: End-to-end JS → Rust integration tests.
//!
//! Reads JSON fixture files produced by `tests/zk-witness.test.js`,
//! deserializes into trace matrices, and runs the full STARK prover
//! + verifier pipeline. This validates that the JS witness generator
//! produces valid traces for the Rust AIR chips.

use proof_checker::bridge::prove_json;

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

#[test]
fn e2e_loli_l() {
    prove_json(&load_fixture("loli_l")).expect("loli_l: P, P ⊸ Q ⊢ Q");
}

#[test]
fn e2e_oplus_r1() {
    prove_json(&load_fixture("oplus_r1")).expect("oplus_r1: A ⊢ A ⊕ B");
}

#[test]
fn e2e_with_l1() {
    prove_json(&load_fixture("with_l1")).expect("with_l1: A & B ⊢ A");
}

#[test]
fn e2e_one_l() {
    prove_json(&load_fixture("one_l")).expect("one_l: I, A ⊢ A");
}

#[test]
fn e2e_zero_l() {
    prove_json(&load_fixture("zero_l")).expect("zero_l: 0 ⊢ C");
}

#[test]
fn e2e_bang_dereliction() {
    prove_json(&load_fixture("bang_dereliction")).expect("bang_l: !A ⊢ A");
}

#[test]
fn e2e_copy() {
    prove_json(&load_fixture("copy")).expect("copy: ; A ⊢ A");
}

#[test]
fn e2e_nested_loli_tensor() {
    prove_json(&load_fixture("nested_loli_tensor")).expect("nested: (A⊗B)⊸C, A, B ⊢ C");
}

#[test]
fn e2e_solc_forward() {
    prove_json(&load_fixture("solc_forward")).expect("solc_forward: 279-step EVM symbolic execution");
}

#[test]
fn e2e_solc_flat() {
    prove_json(&load_fixture("solc_flat")).expect("solc_flat: 279-step flat rewriting certificate");
}

#[test]
fn e2e_copy_tensor() {
    prove_json(&load_fixture("copy_tensor")).expect("copy_tensor: ; A ⊢ A ⊗ A");
}

#[test]
fn e2e_bang_r_promotion() {
    prove_json(&load_fixture("bang_r_promotion")).expect("bang_r: ; A ⊢ !A");
}

// Phase 6-1: noFFI clause proof — copy/loli_l/monad_l chains from clause resolution
#[test]
fn e2e_clause_copy_loli() {
    prove_json(&load_fixture("clause_copy_loli"))
        .expect("clause_copy_loli: noFFI 2-step forward execution with inc clause resolution");
}
