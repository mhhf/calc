//! Phase 6-3: Soundness validation tests.
//!
//! Validates that:
//! 1. NoFFI witnesses (clause proof chains) reject tampering
//! 2. Pure linear witnesses (no clause resolution) prove and verify
//! 3. Forgery vectors from Phase 3 apply to noFFI witnesses
//! 4. Sequent PVs reject tampering on noFFI witnesses

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

fn tamper_fixture(name: &str, modify: impl FnOnce(&mut serde_json::Value)) -> String {
    let json = load_fixture(name);
    let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
    modify(&mut v);
    serde_json::to_string(&v).unwrap()
}

// ---------------------------------------------------------------------------
// Baseline: noFFI and pure linear fixtures pass
// ---------------------------------------------------------------------------

#[test]
fn p6_clause_copy_loli_baseline() {
    prove_json(&load_fixture("clause_copy_loli"))
        .expect("clause_copy_loli baseline should pass");
}

#[test]
fn p6_pure_linear_baseline() {
    prove_json(&load_fixture("pure_linear"))
        .expect("pure_linear baseline should pass");
}

// ---------------------------------------------------------------------------
// Pure linear: PV verification (sequent identity readable from proof)
// ---------------------------------------------------------------------------

#[test]
fn p6_pure_linear_public_values() {
    let json = load_fixture("pure_linear");
    let witness: WitnessJson = serde_json::from_str(&json).unwrap();

    let init_rows = witness.chips.get("init").unwrap();
    let mut expected_ctx: Vec<u32> = Vec::new();
    let mut expected_succedent: u32 = 0;
    let mut expected_lax: u32 = 0;
    for row in init_rows {
        if row[1] == 1 { expected_ctx.push(row[0]); }
        if row[3] == 1 { expected_succedent = row[2]; expected_lax = row[5]; }
    }

    let vdata = prove_witness_vdata(&witness)
        .expect("pure_linear proof should succeed");

    let init_pvs = &vdata.data.proof.per_air[0].public_values;
    let num_pvs = expected_ctx.len() + 3; // +3: succedent + lax + init_active_count
    assert_eq!(init_pvs.len(), num_pvs, "PV count mismatch");

    for (i, &ctx_hash) in expected_ctx.iter().enumerate() {
        assert_eq!(init_pvs[i], BabyBear::from_u32(ctx_hash));
    }
    assert_eq!(init_pvs[num_pvs - 3], BabyBear::from_u32(expected_succedent));
    assert_eq!(init_pvs[num_pvs - 2], BabyBear::from_u32(expected_lax));
}

// ---------------------------------------------------------------------------
// Forgery: tamper gamma_rom hash → GAMMA_BUS imbalance
// Copy nodes reference gamma entries; wrong hash → unbalanced bus
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_gamma_hash_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        // gamma_rom[0] = [hash, is_active, num_lookups] — tamper the hash
        v["gamma_rom"][0][0] = serde_json::json!(999);
    });
    prove_json(&json).expect("should fail: tampered gamma_rom hash");
}

// ---------------------------------------------------------------------------
// Forgery: tamper formula_rom hash → FORMULA_BUS imbalance
// Clause proofs use formula decomposition; wrong hash → bus mismatch
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_formula_hash_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        // formula_rom[0] = [hash, tag, c0, c1, is_active, num_lookups] — tamper hash
        v["formula_rom"][0][0] = serde_json::json!(888);
    });
    prove_json(&json).expect("should fail: tampered formula_rom hash");
}

// ---------------------------------------------------------------------------
// Forgery: tamper init ctx_hash on noFFI witness → CONTEXT_BUS imbalance
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_ctx_hash_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        v["chips"]["init"][0][0] = serde_json::json!(777);
    });
    prove_json(&json).expect("should fail: tampered ctx_hash");
}

// ---------------------------------------------------------------------------
// Forgery: tamper init oblig_hash on noFFI witness → OBLIG_BUS imbalance
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_oblig_hash_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        v["chips"]["init"][0][2] = serde_json::json!(666);
    });
    prove_json(&json).expect("should fail: tampered oblig_hash");
}

// ---------------------------------------------------------------------------
// Forgery: flip lax on noFFI witness → OBLIG_BUS tuple mismatch
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_lax_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        v["chips"]["init"][0][5] = serde_json::json!(1);
    });
    prove_json(&json).expect("should fail: lax flip");
}

// ---------------------------------------------------------------------------
// Forgery: remove a copy chip row → CONTEXT_BUS/GAMMA_BUS imbalance
// The copy node sends on CONTEXT_BUS and receives from GAMMA_BUS;
// removing a row leaves an unmatched obligation
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_remove_copy_row_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        let rows = v["chips"]["copy"].as_array_mut().unwrap();
        rows.remove(0);
    });
    prove_json(&json).expect("should fail: removed copy row");
}

// ---------------------------------------------------------------------------
// Forgery: tamper a loli_l chip row principal → OBLIG_BUS imbalance
// loli_l sends Inherited obligation with specific hash; wrong hash → mismatch
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_loli_l_principal_fails() {
    let json = tamper_fixture("clause_copy_loli", |v| {
        // loli_l row format depends on the rule spec, but column 1 is typically
        // the principal hash (after is_active at column 0)
        let rows = v["chips"]["loli_l"].as_array_mut().unwrap();
        if let Some(row) = rows.first_mut() {
            let arr = row.as_array_mut().unwrap();
            if arr.len() > 1 {
                arr[1] = serde_json::json!(555);
            }
        }
    });
    prove_json(&json).expect("should fail: tampered loli_l principal");
}

// ---------------------------------------------------------------------------
// Forgery: tamper PVs (succedent hash) on noFFI witness
// PVs are derived from init rows; tampering the sequent should fail verification
// because the prover reads PVs from init rows and they must be consistent
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_clause_tamper_init_for_pv_mismatch_fails() {
    // Tamper BOTH the init row AND add an inconsistency:
    // change oblig_hash but not the rule chip data → OBLIG_BUS mismatch
    let json = tamper_fixture("clause_copy_loli", |v| {
        v["chips"]["init"][0][2] = serde_json::json!(444); // wrong succedent
    });
    prove_json(&json).expect("should fail: PV/data inconsistency");
}

// ---------------------------------------------------------------------------
// Forgery: pure linear — same vectors apply
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_pure_linear_tamper_ctx_hash_fails() {
    let json = tamper_fixture("pure_linear", |v| {
        v["chips"]["init"][0][0] = serde_json::json!(999);
    });
    prove_json(&json).expect("should fail: tampered ctx_hash on pure_linear");
}

#[test]
#[should_panic]
fn p6_pure_linear_tamper_formula_hash_fails() {
    let json = tamper_fixture("pure_linear", |v| {
        v["formula_rom"][0][0] = serde_json::json!(888);
    });
    prove_json(&json).expect("should fail: tampered formula_rom on pure_linear");
}
