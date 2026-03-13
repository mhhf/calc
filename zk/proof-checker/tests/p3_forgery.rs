//! Phase 3: Cross-sequent forgery tests.
//!
//! Verifies that a valid proof for sequent S₁ cannot be presented as
//! a proof for sequent S₂. All tests modify the identity fixture
//! (A ⊢ A) and feed the tampered JSON to prove_json.
//!
//! Tests:
//! - Wrong ctx_hash → CONTEXT_BUS imbalance
//! - Wrong oblig_hash → OBLIG_BUS imbalance
//! - Extra init row → unbalanced buses
//! - Lax flip (0→1) → OBLIG_BUS tuple mismatch

use proof_checker::bridge::prove_json;

/// Load the identity fixture as a JSON string.
fn identity_json() -> String {
    include_str!("../tests/fixtures/identity.json").to_string()
}

/// Load, modify, and re-serialize the identity fixture.
fn tamper_identity(modify: impl FnOnce(&mut serde_json::Value)) -> String {
    let mut v: serde_json::Value = serde_json::from_str(&identity_json()).unwrap();
    modify(&mut v);
    serde_json::to_string(&v).unwrap()
}

// ---------------------------------------------------------------------------
// Baseline: unmodified identity fixture passes
// ---------------------------------------------------------------------------

#[test]
fn p3_identity_baseline() {
    prove_json(&identity_json()).expect("identity baseline should pass");
}

// ---------------------------------------------------------------------------
// Forgery: replace ctx_hash → CONTEXT_BUS imbalance
// InitChip sends wrong hash, id chip still consumes original
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p3_wrong_ctx_hash_fails() {
    let json = tamper_identity(|v| {
        v["chips"]["init"][0][0] = serde_json::json!(999);
    });
    prove_json(&json).expect("should fail: wrong ctx_hash");
}

// ---------------------------------------------------------------------------
// Forgery: replace oblig_hash → OBLIG_BUS imbalance
// InitChip sends wrong obligation, id chip expects original
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p3_wrong_oblig_hash_fails() {
    let json = tamper_identity(|v| {
        v["chips"]["init"][0][2] = serde_json::json!(888);
    });
    prove_json(&json).expect("should fail: wrong oblig_hash");
}

// ---------------------------------------------------------------------------
// Forgery: add extra init row → unbalanced CONTEXT/OBLIG buses
// Extra context and obligation with no consumer
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p3_extra_init_row_fails() {
    let json = tamper_identity(|v| {
        let extra = serde_json::json!([777, 1, 777, 1, 1, 0]);
        v["chips"]["init"].as_array_mut().unwrap().push(extra);
    });
    prove_json(&json).expect("should fail: extra init row");
}

// ---------------------------------------------------------------------------
// Forgery: flip lax=0 to lax=1 → OBLIG_BUS tuple mismatch
// InitChip sends (nonce, hash, lax=1) but id expects (nonce, hash, lax=0)
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p3_lax_flip_fails() {
    let json = tamper_identity(|v| {
        v["chips"]["init"][0][5] = serde_json::json!(1);
    });
    prove_json(&json).expect("should fail: lax flip");
}
