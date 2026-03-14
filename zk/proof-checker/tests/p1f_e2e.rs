//! Phase 1f: End-to-end JS → Rust integration tests.
//!
//! Reads JSON fixture files produced by `tests/zk-witness.test.js`,
//! deserializes into trace matrices, and runs the full STARK prover
//! + verifier pipeline. This validates that the JS witness generator
//! produces valid traces for the Rust AIR chips.

use proof_checker::bridge::{prove_json, prove_witness_vdata, WitnessJson};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

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

// Phase 6-3: pure linear forward execution (no clause resolution, no persistent preconditions)
#[test]
fn e2e_pure_linear() {
    prove_json(&load_fixture("pure_linear"))
        .expect("pure_linear: 2-step forward execution, zero clause resolution");
}

// Phase 6-2: verify sequent identity is exposed as public values on InitChip (AIR 0)
#[test]
fn e2e_identity_public_values() {
    let json = load_fixture("identity");
    let witness: WitnessJson = serde_json::from_str(&json).unwrap();

    // Extract expected PVs from init rows
    let init_rows = witness.chips.get("init").unwrap();
    let mut expected_ctx: Vec<u32> = Vec::new();
    let mut expected_succedent: u32 = 0;
    let mut expected_lax: u32 = 0;
    for row in init_rows {
        // [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
        if row[1] == 1 { expected_ctx.push(row[0]); }
        if row[3] == 1 { expected_succedent = row[2]; expected_lax = row[5]; }
    }

    // Prove and get verification data
    let vdata = prove_witness_vdata(&witness)
        .expect("identity proof should succeed");

    // InitChip is AIR index 0 — its PVs should be [ctx_hash_1..n, succedent_hash, lax]
    let init_pvs = &vdata.data.proof.per_air[0].public_values;
    let num_pvs = expected_ctx.len() + 2;
    assert_eq!(init_pvs.len(), num_pvs, "PV count mismatch");

    // Verify ctx hashes
    for (i, &ctx_hash) in expected_ctx.iter().enumerate() {
        assert_eq!(init_pvs[i], BabyBear::from_u32(ctx_hash),
            "ctx_hash[{i}] mismatch");
    }
    // Verify succedent hash
    assert_eq!(init_pvs[num_pvs - 2], BabyBear::from_u32(expected_succedent),
        "succedent_hash mismatch");
    // Verify lax flag
    assert_eq!(init_pvs[num_pvs - 1], BabyBear::from_u32(expected_lax),
        "lax_flag mismatch");
}

// Phase 6-2: verify PVs on a multi-context proof (loli_l: P, P⊸Q ⊢ Q — 2 ctx entries)
#[test]
fn e2e_loli_l_public_values() {
    let json = load_fixture("loli_l");
    let witness: WitnessJson = serde_json::from_str(&json).unwrap();

    let init_rows = witness.chips.get("init").unwrap();
    let mut expected_ctx: Vec<u32> = Vec::new();
    let mut expected_succedent: u32 = 0;
    let mut expected_lax: u32 = 0;
    for row in init_rows {
        if row[1] == 1 { expected_ctx.push(row[0]); }
        if row[3] == 1 { expected_succedent = row[2]; expected_lax = row[5]; }
    }
    assert!(expected_ctx.len() >= 2, "loli_l should have at least 2 context entries");

    let vdata = prove_witness_vdata(&witness)
        .expect("loli_l proof should succeed");

    let init_pvs = &vdata.data.proof.per_air[0].public_values;
    let num_pvs = expected_ctx.len() + 2;
    assert_eq!(init_pvs.len(), num_pvs);

    for (i, &ctx_hash) in expected_ctx.iter().enumerate() {
        assert_eq!(init_pvs[i], BabyBear::from_u32(ctx_hash));
    }
    assert_eq!(init_pvs[num_pvs - 2], BabyBear::from_u32(expected_succedent));
    assert_eq!(init_pvs[num_pvs - 1], BabyBear::from_u32(expected_lax));
}
