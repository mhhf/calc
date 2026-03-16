//! Phase 6-4: Custom chip tests.
//!
//! Validates that:
//! 1. Witnesses with fact_axiom rows (custom chip optimization) prove and verify
//! 2. Fact ROM tampering is caught (FACT_BUS imbalance)
//! 3. fact_axiom row tampering is caught

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

fn tamper_fixture(name: &str, modify: impl FnOnce(&mut serde_json::Value)) -> String {
    let json = load_fixture(name);
    let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
    modify(&mut v);
    serde_json::to_string(&v).unwrap()
}

// ---------------------------------------------------------------------------
// Baseline: custom chip fixture passes
// ---------------------------------------------------------------------------

#[test]
fn p6_custom_chip_inc_baseline() {
    prove_json(&load_fixture("custom_chip_inc"))
        .expect("custom_chip_inc baseline should pass");
}

// ---------------------------------------------------------------------------
// Solc-scale: custom chips for all EVM predicates
// ---------------------------------------------------------------------------

#[test]
fn p6_custom_chip_solc_baseline() {
    prove_json(&load_fixture("solc_custom_chips"))
        .expect("solc_custom_chips baseline should pass");
}

// ---------------------------------------------------------------------------
// Forgery: tamper fact_rom goal_hash → FACT_BUS imbalance
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_custom_chip_tamper_fact_rom_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        // fact_rom[0] = [goal_hash, is_active, num_lookups] — tamper the hash
        v["fact_rom"][0][0] = serde_json::json!(999);
    });
    prove_json(&json).expect("should fail: tampered fact_rom hash");
}

// ---------------------------------------------------------------------------
// Forgery: tamper fact_axiom goal_hash → OBLIG_BUS + FACT_BUS mismatch
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_custom_chip_tamper_fact_axiom_goal_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        // fact_axiom row = [active, goal_hash, nonce_in, lax]
        let rows = v["chips"]["fact_axiom"].as_array_mut().unwrap();
        if let Some(row) = rows.first_mut() {
            let arr = row.as_array_mut().unwrap();
            arr[1] = serde_json::json!(888); // wrong goal_hash
        }
    });
    prove_json(&json).expect("should fail: tampered fact_axiom goal");
}

// ---------------------------------------------------------------------------
// Forgery: remove fact_rom entirely → FACT_BUS demand without supply
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_custom_chip_remove_fact_rom_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        v["fact_rom"] = serde_json::json!([]);
    });
    prove_json(&json).expect("should fail: missing fact_rom");
}

// ---------------------------------------------------------------------------
// Phase 6-6a soundness: tamper pred_rom arg → arithmetic constraint violation
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_pred_rom_tamper_arg_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        // pred_rom[0] = [pred_hash, is_active, num_lookups, is_plus, is_mul, is_inc, arg0, arg1, arg2]
        // Tamper arg1 (inc result b) — breaks a+1=b constraint
        let rows = v["pred_rom"].as_array_mut().unwrap();
        if let Some(row) = rows.first_mut() {
            let arr = row.as_array_mut().unwrap();
            arr[7] = serde_json::json!(99); // arg1 = 99 (wrong inc result)
        }
    });
    prove_json(&json).expect("should fail: tampered pred_rom arg");
}

// ---------------------------------------------------------------------------
// Phase 6-6a soundness: remove pred_rom → PRED_BUS demand without supply
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_pred_rom_remove_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        v["pred_rom"] = serde_json::json!([]);
    });
    prove_json(&json).expect("should fail: empty pred_rom");
}

// ---------------------------------------------------------------------------
// Phase 6-6a soundness: tamper pred_hash → PRED_BUS key mismatch
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p6_pred_rom_tamper_hash_fails() {
    let json = tamper_fixture("custom_chip_inc", |v| {
        // Tamper pred_hash in pred_rom → PRED_BUS key won't match fact_axiom demand
        let rows = v["pred_rom"].as_array_mut().unwrap();
        if let Some(row) = rows.first_mut() {
            let arr = row.as_array_mut().unwrap();
            arr[0] = serde_json::json!(77777); // wrong pred_hash
        }
    });
    prove_json(&json).expect("should fail: tampered pred_hash");
}
